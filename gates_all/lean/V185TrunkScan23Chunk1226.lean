import V185TrunkScan23Chunk1225

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7264838 : List Nat := [6, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2]
def baseStart_7264838 : Nat := 118140960795 + 7264838 * 2 ^ 59
def prefixEnd_7264838 : Nat := 4983230072969 + 3 ^ 40 * 7264838 * 2
def baseEnd_7264838 : Nat := 3730353771048152521614625

theorem tailTrace_7264838 : CollatzResearch.WordTrace tailWord_7264838 prefixEnd_7264838 3730353771048152521614625 := by
  unfold tailWord_7264838
  simp only [CollatzResearch.WordTrace]
  refine ⟨8280325314210629262359599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 176646940036493424263671445 8280325314210629262359599)
  ·
    refine ⟨12420487971315943893539399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8280325314210629262359599 12420487971315943893539399)
    ·
      refine ⟨18630731956973915840309099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12420487971315943893539399 18630731956973915840309099)
      ·
        refine ⟨27946097935460873760463649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18630731956973915840309099 27946097935460873760463649)
        ·
          refine ⟨20959573451595655320347737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27946097935460873760463649 20959573451595655320347737)
          ·
            refine ⟨15719680088696741490260803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20959573451595655320347737 15719680088696741490260803)
            ·
              refine ⟨23579520133045112235391205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15719680088696741490260803 23579520133045112235391205)
              ·
                refine ⟨4421160024945958544135851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23579520133045112235391205 4421160024945958544135851)
                ·
                  refine ⟨6631740037418937816203777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4421160024945958544135851 6631740037418937816203777)
                  ·
                    refine ⟨4973805028064203362152833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6631740037418937816203777 4973805028064203362152833)
                    ·
                      refine ⟨3730353771048152521614625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4973805028064203362152833 3730353771048152521614625)
                      ·
                        rfl

theorem cell23_7264838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_7264838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264838 prefixEnd_7264838 := by exact prefixLift 7264838
  have htrace : WordTrace (prefixWord ++ tailWord_7264838) baseStart_7264838 baseEnd_7264838 := by
    simpa [prefixWord, tailWord_7264838, baseEnd_7264838] using wordTrace_append hprefix tailTrace_7264838
  have hstable : (prefixWord ++ tailWord_7264838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264838).length < 2 ^ (prefixWord ++ tailWord_7264838).sum := by decide
  have hdescent : baseEnd_7264838 < baseStart_7264838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264877 : List Nat := [1, 5, 1, 1, 3, 1, 2, 2, 1, 4, 2]
def baseStart_7264877 : Nat := 118140960795 + 7264877 * 2 ^ 59
def prefixEnd_7264877 : Nat := 4983230072969 + 3 ^ 40 * 7264877 * 2
def baseEnd_7264877 : Nat := 3730373796793677869026945

theorem tailTrace_7264877 : CollatzResearch.WordTrace tailWord_7264877 prefixEnd_7264877 3730373796793677869026945 := by
  unfold tailWord_7264877
  simp only [CollatzResearch.WordTrace]
  refine ⟨264971832501598846056176885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176647888334399230704117923 264971832501598846056176885)
  ·
    refine ⟨24841109297024891817766583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 264971832501598846056176885 24841109297024891817766583)
    ·
      refine ⟨37261663945537337726649875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24841109297024891817766583 37261663945537337726649875)
      ·
        refine ⟨55892495918306006589974813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37261663945537337726649875 55892495918306006589974813)
        ·
          refine ⟨20959685969364752471240555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55892495918306006589974813 20959685969364752471240555)
          ·
            refine ⟨31439528954047128706860833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20959685969364752471240555 31439528954047128706860833)
            ·
              refine ⟨23579646715535346530145625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31439528954047128706860833 23579646715535346530145625)
              ·
                refine ⟨17684735036651509897609219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23579646715535346530145625 17684735036651509897609219)
                ·
                  refine ⟨26527102554977264846413829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17684735036651509897609219 26527102554977264846413829)
                  ·
                    refine ⟨4973831729058237158702593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26527102554977264846413829 4973831729058237158702593)
                    ·
                      refine ⟨3730373796793677869026945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4973831729058237158702593 3730373796793677869026945)
                      ·
                        rfl

theorem cell23_7264877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_7264877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264877 prefixEnd_7264877 := by exact prefixLift 7264877
  have htrace : WordTrace (prefixWord ++ tailWord_7264877) baseStart_7264877 baseEnd_7264877 := by
    simpa [prefixWord, tailWord_7264877, baseEnd_7264877] using wordTrace_append hprefix tailTrace_7264877
  have hstable : (prefixWord ++ tailWord_7264877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264877).length < 2 ^ (prefixWord ++ tailWord_7264877).sum := by decide
  have hdescent : baseEnd_7264877 < baseStart_7264877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264900 : List Nat := [2, 3, 2, 1, 3, 2, 2, 1, 7]
def baseStart_7264900 : Nat := 118140960795 + 7264900 * 2 ^ 59
def prefixEnd_7264900 : Nat := 4983230072969 + 3 ^ 40 * 7264900 * 2
def baseEnd_7264900 : Nat := 414487289649859031004371

theorem tailTrace_7264900 : CollatzResearch.WordTrace tailWord_7264900 prefixEnd_7264900 414487289649859031004371 := by
  unfold tailWord_7264900
  simp only [CollatzResearch.WordTrace]
  refine ⟨132486335690257760492132077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176648447587010347322842769 132486335690257760492132077)
  ·
    refine ⟨49682375883846660184549529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132486335690257760492132077 49682375883846660184549529)
    ·
      refine ⟨37261781912884995138412147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49682375883846660184549529 37261781912884995138412147)
      ·
        refine ⟨55892672869327492707618221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37261781912884995138412147 55892672869327492707618221)
        ·
          refine ⟨20959752325997809765356833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55892672869327492707618221 20959752325997809765356833)
          ·
            refine ⟨15719814244498357324017625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20959752325997809765356833 15719814244498357324017625)
            ·
              refine ⟨11789860683373767993013219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15719814244498357324017625 11789860683373767993013219)
              ·
                refine ⟨17684791025060651989519829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11789860683373767993013219 17684791025060651989519829)
                ·
                  refine ⟨414487289649859031004371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17684791025060651989519829 414487289649859031004371)
                  ·
                    rfl

theorem cell23_7264900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 7].length) (baseStart_7264900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264900 prefixEnd_7264900 := by exact prefixLift 7264900
  have htrace : WordTrace (prefixWord ++ tailWord_7264900) baseStart_7264900 baseEnd_7264900 := by
    simpa [prefixWord, tailWord_7264900, baseEnd_7264900] using wordTrace_append hprefix tailTrace_7264900
  have hstable : (prefixWord ++ tailWord_7264900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264900).length < 2 ^ (prefixWord ++ tailWord_7264900).sum := by decide
  have hdescent : baseEnd_7264900 < baseStart_7264900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264910 : List Nat := [4, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3]
def baseStart_7264910 : Nat := 118140960795 + 7264910 * 2 ^ 59
def prefixEnd_7264910 : Nat := 4983230072969 + 3 ^ 40 * 7264910 * 2
def baseEnd_7264910 : Nat := 3730390741655276239914293

theorem tailTrace_7264910 : CollatzResearch.WordTrace tailWord_7264910 prefixEnd_7264910 3730390741655276239914293 := by
  unfold tailWord_7264910
  simp only [CollatzResearch.WordTrace]
  refine ⟨33121629513809911586516023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176648690740319528461418789 33121629513809911586516023)
  ·
    refine ⟨49682444270714867379774035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33121629513809911586516023 49682444270714867379774035)
    ·
      refine ⟨74523666406072301069661053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49682444270714867379774035 74523666406072301069661053)
      ·
        refine ⟨27946374902277112901122895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74523666406072301069661053 27946374902277112901122895)
        ·
          refine ⟨41919562353415669351684343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27946374902277112901122895 41919562353415669351684343)
          ·
            refine ⟨62879343530123504027526515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41919562353415669351684343 62879343530123504027526515)
            ·
              refine ⟨94319015295185256041289773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62879343530123504027526515 94319015295185256041289773)
              ·
                refine ⟨35369630735694471015483665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94319015295185256041289773 35369630735694471015483665)
                ·
                  refine ⟨26527223051770853261612749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35369630735694471015483665 26527223051770853261612749)
                  ·
                    refine ⟨9947708644414069973104781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26527223051770853261612749 9947708644414069973104781)
                    ·
                      refine ⟨3730390741655276239914293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9947708644414069973104781 3730390741655276239914293)
                      ·
                        rfl

theorem cell23_7264910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_7264910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264910 prefixEnd_7264910 := by exact prefixLift 7264910
  have htrace : WordTrace (prefixWord ++ tailWord_7264910) baseStart_7264910 baseEnd_7264910 := by
    simpa [prefixWord, tailWord_7264910, baseEnd_7264910] using wordTrace_append hprefix tailTrace_7264910
  have hstable : (prefixWord ++ tailWord_7264910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264910).length < 2 ^ (prefixWord ++ tailWord_7264910).sum := by decide
  have hdescent : baseEnd_7264910 < baseStart_7264910 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265020 : List Nat := [2, 2, 2, 1, 3, 2, 1, 2, 3, 5]
def baseStart_7265020 : Nat := 118140960795 + 7265020 * 2 ^ 59
def prefixEnd_7265020 : Nat := 4983230072969 + 3 ^ 40 * 7265020 * 2
def baseEnd_7265020 : Nat := 1243482408175756936512929

theorem tailTrace_7265020 : CollatzResearch.WordTrace tailWord_7265020 prefixEnd_7265020 1243482408175756936512929 := by
  unfold tailWord_7265020
  simp only [CollatzResearch.WordTrace]
  refine ⟨132488524070040390739316257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176651365426720520985755009 132488524070040390739316257)
  ·
    refine ⟨99366393052530293054487193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132488524070040390739316257 99366393052530293054487193)
    ·
      refine ⟨74524794789397719790865395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99366393052530293054487193 74524794789397719790865395)
      ·
        refine ⟨111787192184096579686298093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74524794789397719790865395 111787192184096579686298093)
        ·
          refine ⟨41920197069036217382361785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111787192184096579686298093 41920197069036217382361785)
          ·
            refine ⟨31440147801777163036771339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41920197069036217382361785 31440147801777163036771339)
            ·
              refine ⟨47160221702665744555157009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31440147801777163036771339 47160221702665744555157009)
              ·
                refine ⟨35370166276999308416367757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47160221702665744555157009 35370166276999308416367757)
                ·
                  refine ⟨13263812353874740656137909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35370166276999308416367757 13263812353874740656137909)
                  ·
                    refine ⟨1243482408175756936512929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13263812353874740656137909 1243482408175756936512929)
                    ·
                      rfl

theorem cell23_7265020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_7265020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265020 prefixEnd_7265020 := by exact prefixLift 7265020
  have htrace : WordTrace (prefixWord ++ tailWord_7265020) baseStart_7265020 baseEnd_7265020 := by
    simpa [prefixWord, tailWord_7265020, baseEnd_7265020] using wordTrace_append hprefix tailTrace_7265020
  have hstable : (prefixWord ++ tailWord_7265020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265020).length < 2 ^ (prefixWord ++ tailWord_7265020).sum := by decide
  have hdescent : baseEnd_7265020 < baseStart_7265020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265050 : List Nat := [3, 1, 1, 3, 2, 1, 1, 4, 1, 6]
def baseStart_7265050 : Nat := 118140960795 + 7265050 * 2 ^ 59
def prefixEnd_7265050 : Nat := 4983230072969 + 3 ^ 40 * 7265050 * 2
def baseEnd_7265050 : Nat := 1243487542982301897387883

theorem tailTrace_7265050 : CollatzResearch.WordTrace tailWord_7265050 prefixEnd_7265050 1243487542982301897387883 := by
  unfold tailWord_7265050
  simp only [CollatzResearch.WordTrace]
  refine ⟨66244535582493024150556151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176652094886648064401483069 66244535582493024150556151)
  ·
    refine ⟨99366803373739536225834227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66244535582493024150556151 99366803373739536225834227)
    ·
      refine ⟨149050205060609304338751341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99366803373739536225834227 149050205060609304338751341)
      ·
        refine ⟨55893826897728489127031753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149050205060609304338751341 55893826897728489127031753)
        ·
          refine ⟨41920370173296366845273815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55893826897728489127031753 41920370173296366845273815)
          ·
            refine ⟨62880555259944550267910723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41920370173296366845273815 62880555259944550267910723)
            ·
              refine ⟨94320832889916825401866085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62880555259944550267910723 94320832889916825401866085)
              ·
                refine ⟨17685156166859404762849891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94320832889916825401866085 17685156166859404762849891)
                ·
                  refine ⟨26527734250289107144274837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17685156166859404762849891 26527734250289107144274837)
                  ·
                    refine ⟨1243487542982301897387883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26527734250289107144274837 1243487542982301897387883)
                    ·
                      rfl

theorem cell23_7265050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 1, 6].length) (baseStart_7265050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265050 prefixEnd_7265050 := by exact prefixLift 7265050
  have htrace : WordTrace (prefixWord ++ tailWord_7265050) baseStart_7265050 baseEnd_7265050 := by
    simpa [prefixWord, tailWord_7265050, baseEnd_7265050] using wordTrace_append hprefix tailTrace_7265050
  have hstable : (prefixWord ++ tailWord_7265050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265050).length < 2 ^ (prefixWord ++ tailWord_7265050).sum := by decide
  have hdescent : baseEnd_7265050 < baseStart_7265050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265057 : List Nat := [1, 2, 3, 2, 1, 2, 3, 3, 1, 1, 4]
def baseStart_7265057 : Nat := 118140960795 + 7265057 * 2 ^ 59
def prefixEnd_7265057 : Nat := 4983230072969 + 3 ^ 40 * 7265057 * 2
def baseEnd_7265057 : Nat := 3730466223311487164776117

theorem tailTrace_7265057 : CollatzResearch.WordTrace tailWord_7265057 prefixEnd_7265057 3730466223311487164776117 := by
  unfold tailWord_7265057
  simp only [CollatzResearch.WordTrace]
  refine ⟨264978397640946736797729425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176652265093964491198486283 264978397640946736797729425)
  ·
    refine ⟨198733798230710052598297069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264978397640946736797729425 198733798230710052598297069)
    ·
      refine ⟨74525174336516269724361401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198733798230710052598297069 74525174336516269724361401)
      ·
        refine ⟨55893880752387202293271051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74525174336516269724361401 55893880752387202293271051)
        ·
          refine ⟨83840821128580803439906577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55893880752387202293271051 83840821128580803439906577)
          ·
            refine ⟨62880615846435602579929933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83840821128580803439906577 62880615846435602579929933)
            ·
              refine ⟨23580230942413350967473725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62880615846435602579929933 23580230942413350967473725)
              ·
                refine ⟨8842586603405006612802647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23580230942413350967473725 8842586603405006612802647)
                ·
                  refine ⟨13263879905107509919203971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8842586603405006612802647 13263879905107509919203971)
                  ·
                    refine ⟨19895819857661264878805957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13263879905107509919203971 19895819857661264878805957)
                    ·
                      refine ⟨3730466223311487164776117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19895819857661264878805957 3730466223311487164776117)
                      ·
                        rfl

theorem cell23_7265057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_7265057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265057 prefixEnd_7265057 := by exact prefixLift 7265057
  have htrace : WordTrace (prefixWord ++ tailWord_7265057) baseStart_7265057 baseEnd_7265057 := by
    simpa [prefixWord, tailWord_7265057, baseEnd_7265057] using wordTrace_append hprefix tailTrace_7265057
  have hstable : (prefixWord ++ tailWord_7265057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265057).length < 2 ^ (prefixWord ++ tailWord_7265057).sum := by decide
  have hdescent : baseEnd_7265057 < baseStart_7265057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265077 : List Nat := [1, 3, 3, 1, 3, 2, 1, 2, 1, 1, 5]
def baseStart_7265077 : Nat := 118140960795 + 7265077 * 2 ^ 59
def prefixEnd_7265077 : Nat := 4983230072969 + 3 ^ 40 * 7265077 * 2
def baseEnd_7265077 : Nat := 3730476492924577086526025

theorem tailTrace_7265077 : CollatzResearch.WordTrace tailWord_7265077 prefixEnd_7265077 3730476492924577086526025 := by
  unfold tailWord_7265077
  simp only [CollatzResearch.WordTrace]
  refine ⟨264979127100874280213457485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176652751400582853475638323 264979127100874280213457485)
  ·
    refine ⟨99367172662827855080046557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264979127100874280213457485 99367172662827855080046557)
    ·
      refine ⟨37262689748560445655017459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99367172662827855080046557 37262689748560445655017459)
      ·
        refine ⟨55894034622840668482526189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37262689748560445655017459 55894034622840668482526189)
        ·
          refine ⟨20960262983565250680947321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55894034622840668482526189 20960262983565250680947321)
          ·
            refine ⟨15720197237673938010710491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20960262983565250680947321 15720197237673938010710491)
            ·
              refine ⟨23580295856510907016065737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15720197237673938010710491 23580295856510907016065737)
              ·
                refine ⟨17685221892383180262049303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23580295856510907016065737 17685221892383180262049303)
                ·
                  refine ⟨26527832838574770393073955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17685221892383180262049303 26527832838574770393073955)
                  ·
                    refine ⟨39791749257862155589610933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26527832838574770393073955 39791749257862155589610933)
                    ·
                      refine ⟨3730476492924577086526025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39791749257862155589610933 3730476492924577086526025)
                      ·
                        rfl

theorem cell23_7265077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_7265077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265077 prefixEnd_7265077 := by exact prefixLift 7265077
  have htrace : WordTrace (prefixWord ++ tailWord_7265077) baseStart_7265077 baseEnd_7265077 := by
    simpa [prefixWord, tailWord_7265077, baseEnd_7265077] using wordTrace_append hprefix tailTrace_7265077
  have hstable : (prefixWord ++ tailWord_7265077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265077).length < 2 ^ (prefixWord ++ tailWord_7265077).sum := by decide
  have hdescent : baseEnd_7265077 < baseStart_7265077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265087 : List Nat := [1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 4]
def baseStart_7265087 : Nat := 118140960795 + 7265087 * 2 ^ 59
def prefixEnd_7265087 : Nat := 4983230072969 + 3 ^ 40 * 7265087 * 2
def baseEnd_7265087 : Nat := 3730481627731122047400979

theorem tailTrace_7265087 : CollatzResearch.WordTrace tailWord_7265087 prefixEnd_7265087 3730481627731122047400979 := by
  unfold tailWord_7265087
  simp only [CollatzResearch.WordTrace]
  refine ⟨264979491830838051921321515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176652994553892034614214343 264979491830838051921321515)
  ·
    refine ⟨397469237746257077881982273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264979491830838051921321515 397469237746257077881982273)
    ·
      refine ⟨298101928309692808411486705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397469237746257077881982273 298101928309692808411486705)
      ·
        refine ⟨223576446232269606308615029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298101928309692808411486705 223576446232269606308615029)
        ·
          refine ⟨20960291834275275591432659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 223576446232269606308615029 20960291834275275591432659)
          ·
            refine ⟨31440437751412913387148989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20960291834275275591432659 31440437751412913387148989)
            ·
              refine ⟨11790164156779842520180871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31440437751412913387148989 11790164156779842520180871)
              ·
                refine ⟨17685246235169763780271307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11790164156779842520180871 17685246235169763780271307)
                ·
                  refine ⟨26527869352754645670406961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17685246235169763780271307 26527869352754645670406961)
                  ·
                    refine ⟨19895902014565984252805221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26527869352754645670406961 19895902014565984252805221)
                    ·
                      refine ⟨3730481627731122047400979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19895902014565984252805221 3730481627731122047400979)
                      ·
                        rfl

theorem cell23_7265087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 4].length) (baseStart_7265087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265087 prefixEnd_7265087 := by exact prefixLift 7265087
  have htrace : WordTrace (prefixWord ++ tailWord_7265087) baseStart_7265087 baseEnd_7265087 := by
    simpa [prefixWord, tailWord_7265087, baseEnd_7265087] using wordTrace_append hprefix tailTrace_7265087
  have hstable : (prefixWord ++ tailWord_7265087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265087).length < 2 ^ (prefixWord ++ tailWord_7265087).sum := by decide
  have hdescent : baseEnd_7265087 < baseStart_7265087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265097 : List Nat := [1, 2, 1, 1, 2, 7, 2, 7]
def baseStart_7265097 : Nat := 118140960795 + 7265097 * 2 ^ 59
def prefixEnd_7265097 : Nat := 4983230072969 + 3 ^ 40 * 7265097 * 2
def baseEnd_7265097 : Nat := 138166176390283963269479

theorem tailTrace_7265097 : CollatzResearch.WordTrace tailWord_7265097 prefixEnd_7265097 138166176390283963269479 := by
  unfold tailWord_7265097
  simp only [CollatzResearch.WordTrace]
  refine ⟨264979856560801823629185545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176653237707201215752790363 264979856560801823629185545)
  ·
    refine ⟨198734892420601367721889159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264979856560801823629185545 198734892420601367721889159)
    ·
      refine ⟨298102338630902051582833739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198734892420601367721889159 298102338630902051582833739)
      ·
        refine ⟨447153507946353077374250609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298102338630902051582833739 447153507946353077374250609)
        ·
          refine ⟨335365130959764808030687957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447153507946353077374250609 335365130959764808030687957)
          ·
            refine ⟨7860120256869487688219249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 335365130959764808030687957 7860120256869487688219249)
            ·
              refine ⟨5895090192652115766164437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7860120256869487688219249 5895090192652115766164437)
              ·
                refine ⟨138166176390283963269479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5895090192652115766164437 138166176390283963269479)
                ·
                  rfl

theorem cell23_7265097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 7].length) (baseStart_7265097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265097 prefixEnd_7265097 := by exact prefixLift 7265097
  have htrace : WordTrace (prefixWord ++ tailWord_7265097) baseStart_7265097 baseEnd_7265097 := by
    simpa [prefixWord, tailWord_7265097, baseEnd_7265097] using wordTrace_append hprefix tailTrace_7265097
  have hstable : (prefixWord ++ tailWord_7265097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265097).length < 2 ^ (prefixWord ++ tailWord_7265097).sum := by decide
  have hdescent : baseEnd_7265097 < baseStart_7265097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265120 : List Nat := [2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 5]
def baseStart_7265120 : Nat := 118140960795 + 7265120 * 2 ^ 59
def prefixEnd_7265120 : Nat := 4983230072969 + 3 ^ 40 * 7265120 * 2
def baseEnd_7265120 : Nat := 3730498572592720418288327

theorem tailTrace_7265120 : CollatzResearch.WordTrace tailWord_7265120 prefixEnd_7265120 3730498572592720418288327 := by
  unfold tailWord_7265120
  simp only [CollatzResearch.WordTrace]
  refine ⟨132490347719859249278636407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176653796959812332371515209 132490347719859249278636407)
  ·
    refine ⟨198735521579788873917954611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132490347719859249278636407 198735521579788873917954611)
    ·
      refine ⟨298103282369683310876931917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198735521579788873917954611 298103282369683310876931917)
      ·
        refine ⟨111788730888631241578849469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298103282369683310876931917 111788730888631241578849469)
        ·
          refine ⟨41920774083236715592068551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111788730888631241578849469 41920774083236715592068551)
          ·
            refine ⟨62881161124855073388102827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41920774083236715592068551 62881161124855073388102827)
            ·
              refine ⟨94321741687282610082154241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62881161124855073388102827 94321741687282610082154241)
              ·
                refine ⟨70741306265461957561615681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94321741687282610082154241 70741306265461957561615681)
                ·
                  refine ⟨53055979699096468171211761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70741306265461957561615681 53055979699096468171211761)
                  ·
                    refine ⟨39791984774322351128408821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53055979699096468171211761 39791984774322351128408821)
                    ·
                      refine ⟨3730498572592720418288327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39791984774322351128408821 3730498572592720418288327)
                      ·
                        rfl

theorem cell23_7265120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_7265120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265120 prefixEnd_7265120 := by exact prefixLift 7265120
  have htrace : WordTrace (prefixWord ++ tailWord_7265120) baseStart_7265120 baseEnd_7265120 := by
    simpa [prefixWord, tailWord_7265120, baseEnd_7265120] using wordTrace_append hprefix tailTrace_7265120
  have hstable : (prefixWord ++ tailWord_7265120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265120).length < 2 ^ (prefixWord ++ tailWord_7265120).sum := by decide
  have hdescent : baseEnd_7265120 < baseStart_7265120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265124 : List Nat := [2, 3, 1, 1, 4, 1, 2, 1, 4, 1, 3]
def baseStart_7265124 : Nat := 118140960795 + 7265124 * 2 ^ 59
def prefixEnd_7265124 : Nat := 4983230072969 + 3 ^ 40 * 7265124 * 2
def baseEnd_7265124 : Nat := 3730500626515338402638309

theorem tailTrace_7265124 : CollatzResearch.WordTrace tailWord_7265124 prefixEnd_7265124 3730500626515338402638309 := by
  unfold tailWord_7265124
  simp only [CollatzResearch.WordTrace]
  refine ⟨132490420665852003620209213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176653894221136004826945617 132490420665852003620209213)
  ·
    refine ⟨49683907749694501357578455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132490420665852003620209213 49683907749694501357578455)
    ·
      refine ⟨74525861624541752036367683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49683907749694501357578455 74525861624541752036367683)
      ·
        refine ⟨111788792436812628054551525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74525861624541752036367683 111788792436812628054551525)
        ·
          refine ⟨20960398581902367760228411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111788792436812628054551525 20960398581902367760228411)
          ·
            refine ⟨31440597872853551640342617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20960398581902367760228411 31440597872853551640342617)
            ·
              refine ⟨23580448404640163730256963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31440597872853551640342617 23580448404640163730256963)
              ·
                refine ⟨35370672606960245595385445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23580448404640163730256963 35370672606960245595385445)
                ·
                  refine ⟨6632001113805046049134771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35370672606960245595385445 6632001113805046049134771)
                  ·
                    refine ⟨9948001670707569073702157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6632001113805046049134771 9948001670707569073702157)
                    ·
                      refine ⟨3730500626515338402638309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9948001670707569073702157 3730500626515338402638309)
                      ·
                        rfl

theorem cell23_7265124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 4, 1, 3].length) (baseStart_7265124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265124 prefixEnd_7265124 := by exact prefixLift 7265124
  have htrace : WordTrace (prefixWord ++ tailWord_7265124) baseStart_7265124 baseEnd_7265124 := by
    simpa [prefixWord, tailWord_7265124, baseEnd_7265124] using wordTrace_append hprefix tailTrace_7265124
  have hstable : (prefixWord ++ tailWord_7265124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265124).length < 2 ^ (prefixWord ++ tailWord_7265124).sum := by decide
  have hdescent : baseEnd_7265124 < baseStart_7265124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265141 : List Nat := [1, 3, 4, 1, 1, 3, 1, 3, 2, 1, 3]
def baseStart_7265141 : Nat := 118140960795 + 7265141 * 2 ^ 59
def prefixEnd_7265141 : Nat := 4983230072969 + 3 ^ 40 * 7265141 * 2
def baseEnd_7265141 : Nat := 3730509355686464836125731

theorem tailTrace_7265141 : CollatzResearch.WordTrace tailWord_7265141 prefixEnd_7265141 3730509355686464836125731 := by
  unfold tailWord_7265141
  simp only [CollatzResearch.WordTrace]
  refine ⟨264981461372642419143787277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176654307581761612762524851 264981461372642419143787277)
  ·
    refine ⟨99368048014740907178920229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264981461372642419143787277 99368048014740907178920229)
    ·
      refine ⟨18631509002763920096047543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99368048014740907178920229 18631509002763920096047543)
      ·
        refine ⟨27947263504145880144071315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18631509002763920096047543 27947263504145880144071315)
        ·
          refine ⟨41920895256218820216106973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27947263504145880144071315 41920895256218820216106973)
          ·
            refine ⟨15720335721082057581040115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41920895256218820216106973 15720335721082057581040115)
            ·
              refine ⟨23580503581623086371560173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15720335721082057581040115 23580503581623086371560173)
              ·
                refine ⟨8842688843108657389335065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23580503581623086371560173 8842688843108657389335065)
                ·
                  refine ⟨6632016632331493042001299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8842688843108657389335065 6632016632331493042001299)
                  ·
                    refine ⟨9948024948497239563001949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6632016632331493042001299 9948024948497239563001949)
                    ·
                      refine ⟨3730509355686464836125731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9948024948497239563001949 3730509355686464836125731)
                      ·
                        rfl

theorem cell23_7265141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_7265141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265141 prefixEnd_7265141 := by exact prefixLift 7265141
  have htrace : WordTrace (prefixWord ++ tailWord_7265141) baseStart_7265141 baseEnd_7265141 := by
    simpa [prefixWord, tailWord_7265141, baseEnd_7265141] using wordTrace_append hprefix tailTrace_7265141
  have hstable : (prefixWord ++ tailWord_7265141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265141).length < 2 ^ (prefixWord ++ tailWord_7265141).sum := by decide
  have hdescent : baseEnd_7265141 < baseStart_7265141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265164 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 6, 2, 2]
def baseStart_7265164 : Nat := 118140960795 + 7265164 * 2 ^ 59
def prefixEnd_7265164 : Nat := 4983230072969 + 3 ^ 40 * 7265164 * 2
def baseEnd_7265164 : Nat := 3730521165741518246138125

theorem tailTrace_7265164 : CollatzResearch.WordTrace tailWord_7265164 prefixEnd_7265164 3730521165741518246138125 := by
  unfold tailWord_7265164
  simp only [CollatzResearch.WordTrace]
  refine ⟨132491150125779547035937273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176654866834372729381249697 132491150125779547035937273)
  ·
    refine ⟨99368362594334660276952955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132491150125779547035937273 99368362594334660276952955)
    ·
      refine ⟨149052543891501990415429433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99368362594334660276952955 149052543891501990415429433)
      ·
        refine ⟨111789407918626492811572075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149052543891501990415429433 111789407918626492811572075)
        ·
          refine ⟨167684111877939739217358113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111789407918626492811572075 167684111877939739217358113)
          ·
            refine ⟨125763083908454804413018585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167684111877939739217358113 125763083908454804413018585)
            ·
              refine ⟨94322312931341103309763939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125763083908454804413018585 94322312931341103309763939)
              ·
                refine ⟨141483469397011654964645909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94322312931341103309763939 141483469397011654964645909)
                ·
                  refine ⟨6632037627984921326467777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 141483469397011654964645909 6632037627984921326467777)
                  ·
                    refine ⟨4974028220988690994850833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6632037627984921326467777 4974028220988690994850833)
                    ·
                      refine ⟨3730521165741518246138125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4974028220988690994850833 3730521165741518246138125)
                      ·
                        rfl

theorem cell23_7265164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 6, 2, 2].length) (baseStart_7265164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265164 prefixEnd_7265164 := by exact prefixLift 7265164
  have htrace : WordTrace (prefixWord ++ tailWord_7265164) baseStart_7265164 baseEnd_7265164 := by
    simpa [prefixWord, tailWord_7265164, baseEnd_7265164] using wordTrace_append hprefix tailTrace_7265164
  have hstable : (prefixWord ++ tailWord_7265164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265164).length < 2 ^ (prefixWord ++ tailWord_7265164).sum := by decide
  have hdescent : baseEnd_7265164 < baseStart_7265164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265204 : List Nat := [2, 5, 2, 1, 1, 1, 1, 1, 9]
def baseStart_7265204 : Nat := 118140960795 + 7265204 * 2 ^ 59
def prefixEnd_7265204 : Nat := 4983230072969 + 3 ^ 40 * 7265204 * 2
def baseEnd_7265204 : Nat := 414504633885299787737549

theorem tailTrace_7265204 : CollatzResearch.WordTrace tailWord_7265204 prefixEnd_7265204 414504633885299787737549 := by
  unfold tailWord_7265204
  simp only [CollatzResearch.WordTrace]
  refine ⟨132491879585707090451665333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176655839447609453935553777 132491879585707090451665333)
  ·
    refine ⟨12421113711160039729843625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132491879585707090451665333 12421113711160039729843625)
    ·
      refine ⟨9315835283370029797382719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12421113711160039729843625 9315835283370029797382719)
      ·
        refine ⟨13973752925055044696074079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9315835283370029797382719 13973752925055044696074079)
        ·
          refine ⟨20960629387582567044111119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13973752925055044696074079 20960629387582567044111119)
          ·
            refine ⟨31440944081373850566166679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20960629387582567044111119 31440944081373850566166679)
            ·
              refine ⟨47161416122060775849250019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31440944081373850566166679 47161416122060775849250019)
              ·
                refine ⟨70742124183091163773875029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47161416122060775849250019 70742124183091163773875029)
                ·
                  refine ⟨414504633885299787737549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 70742124183091163773875029 414504633885299787737549)
                  ·
                    rfl

theorem cell23_7265204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_7265204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265204 prefixEnd_7265204 := by exact prefixLift 7265204
  have htrace : WordTrace (prefixWord ++ tailWord_7265204) baseStart_7265204 baseEnd_7265204 := by
    simpa [prefixWord, tailWord_7265204, baseEnd_7265204] using wordTrace_append hprefix tailTrace_7265204
  have hstable : (prefixWord ++ tailWord_7265204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265204).length < 2 ^ (prefixWord ++ tailWord_7265204).sum := by decide
  have hdescent : baseEnd_7265204 < baseStart_7265204 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265311 : List Nat := [1, 1, 2, 4, 1, 5, 2, 1, 6]
def baseStart_7265311 : Nat := 118140960795 + 7265311 * 2 ^ 59
def prefixEnd_7265311 : Nat := 4983230072969 + 3 ^ 40 * 7265311 * 2
def baseEnd_7265311 : Nat := 414510738599747685666661

theorem tailTrace_7265311 : CollatzResearch.WordTrace tailWord_7265311 prefixEnd_7265311 414510738599747685666661 := by
  unfold tailWord_7265311
  simp only [CollatzResearch.WordTrace]
  refine ⟨264987661782026538177475787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176658441188017692118317191 264987661782026538177475787)
  ·
    refine ⟨397481492673039807266213681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264987661782026538177475787 397481492673039807266213681)
    ·
      refine ⟨298111119504779855449660261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397481492673039807266213681 298111119504779855449660261)
      ·
        refine ⟨55895834907146222896811299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 298111119504779855449660261 55895834907146222896811299)
        ·
          refine ⟨83843752360719334345216949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55895834907146222896811299 83843752360719334345216949)
          ·
            refine ⟨7860351783817437594864089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83843752360719334345216949 7860351783817437594864089)
            ·
              refine ⟨5895263837863078196148067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7860351783817437594864089 5895263837863078196148067)
              ·
                refine ⟨8842895756794617294222101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5895263837863078196148067 8842895756794617294222101)
                ·
                  refine ⟨414510738599747685666661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8842895756794617294222101 414510738599747685666661)
                  ·
                    rfl

theorem cell23_7265311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 6].length) (baseStart_7265311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265311 prefixEnd_7265311 := by exact prefixLift 7265311
  have htrace : WordTrace (prefixWord ++ tailWord_7265311) baseStart_7265311 baseEnd_7265311 := by
    simpa [prefixWord, tailWord_7265311, baseEnd_7265311] using wordTrace_append hprefix tailTrace_7265311
  have hstable : (prefixWord ++ tailWord_7265311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265311).length < 2 ^ (prefixWord ++ tailWord_7265311).sum := by decide
  have hdescent : baseEnd_7265311 < baseStart_7265311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265354 : List Nat := [3, 1, 2, 1, 1, 2, 2, 3, 4, 4]
def baseStart_7265354 : Nat := 118140960795 + 7265354 * 2 ^ 59
def prefixEnd_7265354 : Nat := 4983230072969 + 3 ^ 40 * 7265354 * 2
def baseEnd_7265354 : Nat := 1243539575688624167587417

theorem tailTrace_7265354 : CollatzResearch.WordTrace tailWord_7265354 prefixEnd_7265354 1243539575688624167587417 := by
  unfold tailWord_7265354
  simp only [CollatzResearch.WordTrace]
  refine ⟨66247307530217689130322779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176659486747247171014194077 66247307530217689130322779)
  ·
    refine ⟨99370961295326533695484169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66247307530217689130322779 99370961295326533695484169)
    ·
      refine ⟨74528220971494900271613127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99370961295326533695484169 74528220971494900271613127)
      ·
        refine ⟨111792331457242350407419691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74528220971494900271613127 111792331457242350407419691)
        ·
          refine ⟨167688497185863525611129537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111792331457242350407419691 167688497185863525611129537)
          ·
            refine ⟨125766372889397644208347153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167688497185863525611129537 125766372889397644208347153)
            ·
              refine ⟨94324779667048233156260365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125766372889397644208347153 94324779667048233156260365)
              ·
                refine ⟨35371792375143087433597637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94324779667048233156260365 35371792375143087433597637)
                ·
                  refine ⟨6632211070339328893799557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35371792375143087433597637 6632211070339328893799557)
                  ·
                    refine ⟨1243539575688624167587417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6632211070339328893799557 1243539575688624167587417)
                    ·
                      rfl

theorem cell23_7265354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_7265354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265354 prefixEnd_7265354 := by exact prefixLift 7265354
  have htrace : WordTrace (prefixWord ++ tailWord_7265354) baseStart_7265354 baseEnd_7265354 := by
    simpa [prefixWord, tailWord_7265354, baseEnd_7265354] using wordTrace_append hprefix tailTrace_7265354
  have hstable : (prefixWord ++ tailWord_7265354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265354).length < 2 ^ (prefixWord ++ tailWord_7265354).sum := by decide
  have hdescent : baseEnd_7265354 < baseStart_7265354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265364 : List Nat := [2, 4, 1, 1, 1, 1, 2, 4, 1, 1, 5]
def baseStart_7265364 : Nat := 118140960795 + 7265364 * 2 ^ 59
def prefixEnd_7265364 : Nat := 4983230072969 + 3 ^ 40 * 7265364 * 2
def baseEnd_7265364 : Nat := 3730623861872417463637205

theorem tailTrace_7265364 : CollatzResearch.WordTrace tailWord_7265364 prefixEnd_7265364 3730623861872417463637205 := by
  unfold tailWord_7265364
  simp only [CollatzResearch.WordTrace]
  refine ⟨132494797425417264114577573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176659729900556352152770097 132494797425417264114577573)
  ·
    refine ⟨24842774517265737021483295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132494797425417264114577573 24842774517265737021483295)
    ·
      refine ⟨37264161775898605532224943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24842774517265737021483295 37264161775898605532224943)
      ·
        refine ⟨55896242663847908298337415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37264161775898605532224943 55896242663847908298337415)
        ·
          refine ⟨83844363995771862447506123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55896242663847908298337415 83844363995771862447506123)
          ·
            refine ⟨125766545993657793671259185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83844363995771862447506123 125766545993657793671259185)
            ·
              refine ⟨94324909495243345253444389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125766545993657793671259185 94324909495243345253444389)
              ·
                refine ⟨17685920530358127235020823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94324909495243345253444389 17685920530358127235020823)
                ·
                  refine ⟨26528880795537190852531235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17685920530358127235020823 26528880795537190852531235)
                  ·
                    refine ⟨39793321193305786278796853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26528880795537190852531235 39793321193305786278796853)
                    ·
                      refine ⟨3730623861872417463637205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39793321193305786278796853 3730623861872417463637205)
                      ·
                        rfl

theorem cell23_7265364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_7265364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265364 prefixEnd_7265364 := by exact prefixLift 7265364
  have htrace : WordTrace (prefixWord ++ tailWord_7265364) baseStart_7265364 baseEnd_7265364 := by
    simpa [prefixWord, tailWord_7265364, baseEnd_7265364] using wordTrace_append hprefix tailTrace_7265364
  have hstable : (prefixWord ++ tailWord_7265364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265364).length < 2 ^ (prefixWord ++ tailWord_7265364).sum := by decide
  have hdescent : baseEnd_7265364 < baseStart_7265364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265381 : List Nat := [1, 3, 1, 3, 2, 1, 2, 4, 1, 2, 3]
def baseStart_7265381 : Nat := 118140960795 + 7265381 * 2 ^ 59
def prefixEnd_7265381 : Nat := 4983230072969 + 3 ^ 40 * 7265381 * 2
def baseEnd_7265381 : Nat := 3730632591043543897124627

theorem tailTrace_7265381 : CollatzResearch.WordTrace tailWord_7265381 prefixEnd_7265381 3730632591043543897124627 := by
  unfold tailWord_7265381
  simp only [CollatzResearch.WordTrace]
  refine ⟨264990214891772940132523997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176660143261181960088349331 264990214891772940132523997)
  ·
    refine ⟨99371330584414852549696499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264990214891772940132523997 99371330584414852549696499)
    ·
      refine ⟨149056995876622278824544749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99371330584414852549696499 149056995876622278824544749)
      ·
        refine ⟨55896373453733354559204281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149056995876622278824544749 55896373453733354559204281)
        ·
          refine ⟨41922280090300015919403211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55896373453733354559204281 41922280090300015919403211)
          ·
            refine ⟨62883420135450023879104817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41922280090300015919403211 62883420135450023879104817)
            ·
              refine ⟨47162565101587517909328613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62883420135450023879104817 47162565101587517909328613)
              ·
                refine ⟨8842980956547659607999115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47162565101587517909328613 8842980956547659607999115)
                ·
                  refine ⟨13264471434821489411998673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8842980956547659607999115 13264471434821489411998673)
                  ·
                    refine ⟨9948353576116117058999005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13264471434821489411998673 9948353576116117058999005)
                    ·
                      refine ⟨3730632591043543897124627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9948353576116117058999005 3730632591043543897124627)
                      ·
                        rfl

theorem cell23_7265381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_7265381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265381 prefixEnd_7265381 := by exact prefixLift 7265381
  have htrace : WordTrace (prefixWord ++ tailWord_7265381) baseStart_7265381 baseEnd_7265381 := by
    simpa [prefixWord, tailWord_7265381, baseEnd_7265381] using wordTrace_append hprefix tailTrace_7265381
  have hstable : (prefixWord ++ tailWord_7265381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265381).length < 2 ^ (prefixWord ++ tailWord_7265381).sum := by decide
  have hdescent : baseEnd_7265381 < baseStart_7265381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265398 : List Nat := [5, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3]
def baseStart_7265398 : Nat := 118140960795 + 7265398 * 2 ^ 59
def prefixEnd_7265398 : Nat := 4983230072969 + 3 ^ 40 * 7265398 * 2
def baseEnd_7265398 : Nat := 3730641320214670330612049

theorem tailTrace_7265398 : CollatzResearch.WordTrace tailWord_7265398 prefixEnd_7265398 3730641320214670330612049 := by
  unfold tailWord_7265398
  simp only [CollatzResearch.WordTrace]
  refine ⟨16561927183294459502243303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176660556621807568023928565 16561927183294459502243303)
  ·
    refine ⟨24842890774941689253364955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16561927183294459502243303 24842890774941689253364955)
    ·
      refine ⟨37264336162412533880047433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24842890774941689253364955 37264336162412533880047433)
      ·
        refine ⟨27948252121809400410035575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37264336162412533880047433 27948252121809400410035575)
        ·
          refine ⟨41922378182714100615053363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27948252121809400410035575 41922378182714100615053363)
          ·
            refine ⟨62883567274071150922580045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41922378182714100615053363 62883567274071150922580045)
            ·
              refine ⟨23581337727776681595967517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62883567274071150922580045 23581337727776681595967517)
              ·
                refine ⟨8843001647916255598487819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23581337727776681595967517 8843001647916255598487819)
                ·
                  refine ⟨13264502471874383397731729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8843001647916255598487819 13264502471874383397731729)
                  ·
                    refine ⟨9948376853905787548298797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13264502471874383397731729 9948376853905787548298797)
                    ·
                      refine ⟨3730641320214670330612049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9948376853905787548298797 3730641320214670330612049)
                      ·
                        rfl

theorem cell23_7265398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_7265398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265398 prefixEnd_7265398 := by exact prefixLift 7265398
  have htrace : WordTrace (prefixWord ++ tailWord_7265398) baseStart_7265398 baseEnd_7265398 := by
    simpa [prefixWord, tailWord_7265398, baseEnd_7265398] using wordTrace_append hprefix tailTrace_7265398
  have hstable : (prefixWord ++ tailWord_7265398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265398).length < 2 ^ (prefixWord ++ tailWord_7265398).sum := by decide
  have hdescent : baseEnd_7265398 < baseStart_7265398 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265411 : List Nat := [1, 1, 1, 3, 3, 2, 3, 1, 4, 1, 3]
def baseStart_7265411 : Nat := 118140960795 + 7265411 * 2 ^ 59
def prefixEnd_7265411 : Nat := 4983230072969 + 3 ^ 40 * 7265411 * 2
def baseEnd_7265411 : Nat := 3730647995463178779749489

theorem tailTrace_7265411 : CollatzResearch.WordTrace tailWord_7265411 prefixEnd_7265411 3730647995463178779749489 := by
  unfold tailWord_7265411
  simp only [CollatzResearch.WordTrace]
  refine ⟨264991309081664255256116087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176660872721109503504077391 264991309081664255256116087)
  ·
    refine ⟨397486963622496382884174131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264991309081664255256116087 397486963622496382884174131)
    ·
      refine ⟨596230445433744574326261197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397486963622496382884174131 596230445433744574326261197)
      ·
        refine ⟨223586417037654215372347949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 596230445433744574326261197 223586417037654215372347949)
        ·
          refine ⟨83844906389120330764630481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223586417037654215372347949 83844906389120330764630481)
          ·
            refine ⟨62883679791840248073472861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83844906389120330764630481 62883679791840248073472861)
            ·
              refine ⟨23581379921940093027552323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62883679791840248073472861 23581379921940093027552323)
              ·
                refine ⟨35372069882910139541328485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23581379921940093027552323 35372069882910139541328485)
                ·
                  refine ⟨6632263103045651163999091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35372069882910139541328485 6632263103045651163999091)
                  ·
                    refine ⟨9948394654568476745998637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6632263103045651163999091 9948394654568476745998637)
                    ·
                      refine ⟨3730647995463178779749489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9948394654568476745998637 3730647995463178779749489)
                      ·
                        rfl

theorem cell23_7265411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 4, 1, 3].length) (baseStart_7265411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265411 prefixEnd_7265411 := by exact prefixLift 7265411
  have htrace : WordTrace (prefixWord ++ tailWord_7265411) baseStart_7265411 baseEnd_7265411 := by
    simpa [prefixWord, tailWord_7265411, baseEnd_7265411] using wordTrace_append hprefix tailTrace_7265411
  have hstable : (prefixWord ++ tailWord_7265411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265411).length < 2 ^ (prefixWord ++ tailWord_7265411).sum := by decide
  have hdescent : baseEnd_7265411 < baseStart_7265411 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265464 : List Nat := [2, 1, 2, 1, 2, 1, 2, 4, 2, 2, 4]
def baseStart_7265464 : Nat := 118140960795 + 7265464 * 2 ^ 59
def prefixEnd_7265464 : Nat := 4983230072969 + 3 ^ 40 * 7265464 * 2
def baseEnd_7265464 : Nat := 3730675209937867072386745

theorem tailTrace_7265464 : CollatzResearch.WordTrace tailWord_7265464 prefixEnd_7265464 3730675209937867072386745 := by
  unfold tailWord_7265464
  simp only [CollatzResearch.WordTrace]
  refine ⟨132496621075236122653897723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176662161433648163538530297 132496621075236122653897723)
  ·
    refine ⟨198744931612854183980846585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132496621075236122653897723 198744931612854183980846585)
    ·
      refine ⟨149058698709640637985634939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198744931612854183980846585 149058698709640637985634939)
      ·
        refine ⟨223588048064460956978452409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149058698709640637985634939 223588048064460956978452409)
        ·
          refine ⟨167691036048345717733839307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223588048064460956978452409 167691036048345717733839307)
          ·
            refine ⟨251536554072518576600758961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167691036048345717733839307 251536554072518576600758961)
            ·
              refine ⟨188652415554388932450569221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251536554072518576600758961 188652415554388932450569221)
              ·
                refine ⟨35372327916447924834481729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188652415554388932450569221 35372327916447924834481729)
                ·
                  refine ⟨26529245937335943625861297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35372327916447924834481729 26529245937335943625861297)
                  ·
                    refine ⟨19896934453001957719395973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26529245937335943625861297 19896934453001957719395973)
                    ·
                      refine ⟨3730675209937867072386745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19896934453001957719395973 3730675209937867072386745)
                      ·
                        rfl

theorem cell23_7265464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_7265464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265464 prefixEnd_7265464 := by exact prefixLift 7265464
  have htrace : WordTrace (prefixWord ++ tailWord_7265464) baseStart_7265464 baseEnd_7265464 := by
    simpa [prefixWord, tailWord_7265464, baseEnd_7265464] using wordTrace_append hprefix tailTrace_7265464
  have hstable : (prefixWord ++ tailWord_7265464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265464).length < 2 ^ (prefixWord ++ tailWord_7265464).sum := by decide
  have hdescent : baseEnd_7265464 < baseStart_7265464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265584 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 8]
def baseStart_7265584 : Nat := 118140960795 + 7265584 * 2 ^ 59
def prefixEnd_7265584 : Nat := 4983230072969 + 3 ^ 40 * 7265584 * 2
def baseEnd_7265584 : Nat := 3730736827616406602886193

theorem tailTrace_7265584 : CollatzResearch.WordTrace tailWord_7265584 prefixEnd_7265584 3730736827616406602886193 := by
  unfold tailWord_7265584
  simp only [CollatzResearch.WordTrace]
  refine ⟨132498809455018752901081903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176665079273358337201442537 132498809455018752901081903)
  ·
    refine ⟨198748214182528129351622855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132498809455018752901081903 198748214182528129351622855)
    ·
      refine ⟨298122321273792194027434283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198748214182528129351622855 298122321273792194027434283)
      ·
        refine ⟨447183481910688291041151425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298122321273792194027434283 447183481910688291041151425)
        ·
          refine ⟨335387611433016218280863569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447183481910688291041151425 335387611433016218280863569)
          ·
            refine ⟨251540708574762163710647677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335387611433016218280863569 251540708574762163710647677)
            ·
              refine ⟨94327765715535811391492879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 251540708574762163710647677 94327765715535811391492879)
              ·
                refine ⟨141491648573303717087239319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94327765715535811391492879 141491648573303717087239319)
                ·
                  refine ⟨212237472859955575630858979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141491648573303717087239319 212237472859955575630858979)
                  ·
                    refine ⟨318356209289933363446288469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 212237472859955575630858979 318356209289933363446288469)
                    ·
                      refine ⟨3730736827616406602886193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 318356209289933363446288469 3730736827616406602886193)
                      ·
                        rfl

theorem cell23_7265584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 8].length) (baseStart_7265584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265584 prefixEnd_7265584 := by exact prefixLift 7265584
  have htrace : WordTrace (prefixWord ++ tailWord_7265584) baseStart_7265584 baseEnd_7265584 := by
    simpa [prefixWord, tailWord_7265584, baseEnd_7265584] using wordTrace_append hprefix tailTrace_7265584
  have hstable : (prefixWord ++ tailWord_7265584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265584).length < 2 ^ (prefixWord ++ tailWord_7265584).sum := by decide
  have hdescent : baseEnd_7265584 < baseStart_7265584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265585 : List Nat := [1, 2, 2, 3, 3, 1, 2, 4, 1, 4]
def baseStart_7265585 : Nat := 118140960795 + 7265585 * 2 ^ 59
def prefixEnd_7265585 : Nat := 4983230072969 + 3 ^ 40 * 7265585 * 2
def baseEnd_7265585 : Nat := 1243579113699020366324563

theorem tailTrace_7265585 : CollatzResearch.WordTrace tailWord_7265585 prefixEnd_7265585 1243579113699020366324563 := by
  unfold tailWord_7265585
  simp only [CollatzResearch.WordTrace]
  refine ⟨264997655383033882972950209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176665103588689255315300139 264997655383033882972950209)
  ·
    refine ⟨198748241537275412229712657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264997655383033882972950209 198748241537275412229712657)
    ·
      refine ⟨149061181152956559172284493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198748241537275412229712657 149061181152956559172284493)
      ·
        refine ⟨55897942932358709689606685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149061181152956559172284493 55897942932358709689606685)
        ·
          refine ⟨20961728599634516133602507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55897942932358709689606685 20961728599634516133602507)
          ·
            refine ⟨31442592899451774200403761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20961728599634516133602507 31442592899451774200403761)
            ·
              refine ⟨23581944674588830650302821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31442592899451774200403761 23581944674588830650302821)
              ·
                refine ⟨4421614626485405746931779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23581944674588830650302821 4421614626485405746931779)
                ·
                  refine ⟨6632421939728108620397669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4421614626485405746931779 6632421939728108620397669)
                  ·
                    refine ⟨1243579113699020366324563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6632421939728108620397669 1243579113699020366324563)
                    ·
                      rfl

theorem cell23_7265585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 4, 1, 4].length) (baseStart_7265585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265585 prefixEnd_7265585 := by exact prefixLift 7265585
  have htrace : WordTrace (prefixWord ++ tailWord_7265585) baseStart_7265585 baseEnd_7265585 := by
    simpa [prefixWord, tailWord_7265585, baseEnd_7265585] using wordTrace_append hprefix tailTrace_7265585
  have hstable : (prefixWord ++ tailWord_7265585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265585).length < 2 ^ (prefixWord ++ tailWord_7265585).sum := by decide
  have hdescent : baseEnd_7265585 < baseStart_7265585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265629 : List Nat := [1, 4, 5, 1, 1, 1, 1, 2, 2, 2, 3]
def baseStart_7265629 : Nat := 118140960795 + 7265629 * 2 ^ 59
def prefixEnd_7265629 : Nat := 4983230072969 + 3 ^ 40 * 7265629 * 2
def baseEnd_7265629 : Nat := 3730759934245858926823487

theorem tailTrace_7265629 : CollatzResearch.WordTrace tailWord_7265629 prefixEnd_7265629 3730759934245858926823487 := by
  unfold tailWord_7265629
  simp only [CollatzResearch.WordTrace]
  refine ⟨264999260194874478487551941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176666173463249652325034627 264999260194874478487551941)
  ·
    refine ⟨49687361286538964716415989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264999260194874478487551941 49687361286538964716415989)
    ·
      refine ⟨4658190120613027942163999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49687361286538964716415989 4658190120613027942163999)
      ·
        refine ⟨6987285180919541913245999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4658190120613027942163999 6987285180919541913245999)
        ·
          refine ⟨10480927771379312869868999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6987285180919541913245999 10480927771379312869868999)
          ·
            refine ⟨15721391657068969304803499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10480927771379312869868999 15721391657068969304803499)
            ·
              refine ⟨23582087485603453957205249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15721391657068969304803499 23582087485603453957205249)
              ·
                refine ⟨17686565614202590467903937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23582087485603453957205249 17686565614202590467903937)
                ·
                  refine ⟨13264924210651942850927953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17686565614202590467903937 13264924210651942850927953)
                  ·
                    refine ⟨9948693157988957138195965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13264924210651942850927953 9948693157988957138195965)
                    ·
                      refine ⟨3730759934245858926823487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9948693157988957138195965 3730759934245858926823487)
                      ·
                        rfl

theorem cell23_7265629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_7265629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265629 prefixEnd_7265629 := by exact prefixLift 7265629
  have htrace : WordTrace (prefixWord ++ tailWord_7265629) baseStart_7265629 baseEnd_7265629 := by
    simpa [prefixWord, tailWord_7265629, baseEnd_7265629] using wordTrace_append hprefix tailTrace_7265629
  have hstable : (prefixWord ++ tailWord_7265629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265629).length < 2 ^ (prefixWord ++ tailWord_7265629).sum := by decide
  have hdescent : baseEnd_7265629 < baseStart_7265629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265631 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 4]
def baseStart_7265631 : Nat := 118140960795 + 7265631 * 2 ^ 59
def prefixEnd_7265631 : Nat := 4983230072969 + 3 ^ 40 * 7265631 * 2
def baseEnd_7265631 : Nat := 3730760961207167918998477

theorem tailTrace_7265631 : CollatzResearch.WordTrace tailWord_7265631 prefixEnd_7265631 3730760961207167918998477 := by
  unfold tailWord_7265631
  simp only [CollatzResearch.WordTrace]
  refine ⟨264999333140867232829124747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176666222093911488552749831 264999333140867232829124747)
  ·
    refine ⟨397498999711300849243687121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264999333140867232829124747 397498999711300849243687121)
    ·
      refine ⟨298124249783475636932765341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397498999711300849243687121 298124249783475636932765341)
      ·
        refine ⟨111796593668803363849787003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298124249783475636932765341 111796593668803363849787003)
        ·
          refine ⟨167694890503205045774680505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111796593668803363849787003 167694890503205045774680505)
          ·
            refine ⟨125771167877403784331010379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167694890503205045774680505 125771167877403784331010379)
            ·
              refine ⟨188656751816105676496515569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125771167877403784331010379 188656751816105676496515569)
              ·
                refine ⟨141492563862079257372386677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188656751816105676496515569 141492563862079257372386677)
                ·
                  refine ⟨13264927862069930378661251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141492563862079257372386677 13264927862069930378661251)
                  ·
                    refine ⟨19897391793104895567991877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13264927862069930378661251 19897391793104895567991877)
                    ·
                      refine ⟨3730760961207167918998477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19897391793104895567991877 3730760961207167918998477)
                      ·
                        rfl

theorem cell23_7265631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_7265631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265631 prefixEnd_7265631 := by exact prefixLift 7265631
  have htrace : WordTrace (prefixWord ++ tailWord_7265631) baseStart_7265631 baseEnd_7265631 := by
    simpa [prefixWord, tailWord_7265631, baseEnd_7265631] using wordTrace_append hprefix tailTrace_7265631
  have hstable : (prefixWord ++ tailWord_7265631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265631).length < 2 ^ (prefixWord ++ tailWord_7265631).sum := by decide
  have hdescent : baseEnd_7265631 < baseStart_7265631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265635 : List Nat := [1, 1, 1, 5, 2, 3, 1, 2, 2, 3, 2]
def baseStart_7265635 : Nat := 118140960795 + 7265635 * 2 ^ 59
def prefixEnd_7265635 : Nat := 4983230072969 + 3 ^ 40 * 7265635 * 2
def baseEnd_7265635 : Nat := 3730763015129785903348459

theorem tailTrace_7265635 : CollatzResearch.WordTrace tailWord_7265635 prefixEnd_7265635 3730763015129785903348459 := by
  unfold tailWord_7265635
  simp only [CollatzResearch.WordTrace]
  refine ⟨264999479032852741512270359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176666319355235161008180239 264999479032852741512270359)
  ·
    refine ⟨397499218549279112268405539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264999479032852741512270359 397499218549279112268405539)
    ·
      refine ⟨596248827823918668402608309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397499218549279112268405539 596248827823918668402608309)
      ·
        refine ⟨55898327608492375162744529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 596248827823918668402608309 55898327608492375162744529)
        ·
          refine ⟨41923745706369281372058397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55898327608492375162744529 41923745706369281372058397)
          ·
            refine ⟨15721404639888480514521899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41923745706369281372058397 15721404639888480514521899)
            ·
              refine ⟨23582106959832720771782849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15721404639888480514521899 23582106959832720771782849)
              ·
                refine ⟨17686580219874540578837137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23582106959832720771782849 17686580219874540578837137)
                ·
                  refine ⟨13264935164905905434127853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17686580219874540578837137 13264935164905905434127853)
                  ·
                    refine ⟨4974350686839714537797945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13264935164905905434127853 4974350686839714537797945)
                    ·
                      refine ⟨3730763015129785903348459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4974350686839714537797945 3730763015129785903348459)
                      ·
                        rfl

theorem cell23_7265635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_7265635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265635 prefixEnd_7265635 := by exact prefixLift 7265635
  have htrace : WordTrace (prefixWord ++ tailWord_7265635) baseStart_7265635 baseEnd_7265635 := by
    simpa [prefixWord, tailWord_7265635, baseEnd_7265635] using wordTrace_append hprefix tailTrace_7265635
  have hstable : (prefixWord ++ tailWord_7265635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265635).length < 2 ^ (prefixWord ++ tailWord_7265635).sum := by decide
  have hdescent : baseEnd_7265635 < baseStart_7265635 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265658 : List Nat := [3, 1, 1, 1, 1, 1, 2, 7, 2, 4]
def baseStart_7265658 : Nat := 118140960795 + 7265658 * 2 ^ 59
def prefixEnd_7265658 : Nat := 4983230072969 + 3 ^ 40 * 7265658 * 2
def baseEnd_7265658 : Nat := 1243591608394946437786951

theorem tailTrace_7265658 : CollatzResearch.WordTrace tailWord_7265658 prefixEnd_7265658 1243591608394946437786951 := by
  unfold tailWord_7265658
  simp only [CollatzResearch.WordTrace]
  refine ⟨66250079477942354110089407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176666878607846277626905085 66250079477942354110089407)
  ·
    refine ⟨99375119216913531165134111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66250079477942354110089407 99375119216913531165134111)
    ·
      refine ⟨149062678825370296747701167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99375119216913531165134111 149062678825370296747701167)
      ·
        refine ⟨223594018238055445121551751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149062678825370296747701167 223594018238055445121551751)
        ·
          refine ⟨335391027357083167682327627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223594018238055445121551751 335391027357083167682327627)
          ·
            refine ⟨503086541035624751523491441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335391027357083167682327627 503086541035624751523491441)
            ·
              refine ⟨377314905776718563642618581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503086541035624751523491441 377314905776718563642618581)
              ·
                refine ⟨8843318104141841335373873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 377314905776718563642618581 8843318104141841335373873)
                ·
                  refine ⟨6632488578106381001530405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8843318104141841335373873 6632488578106381001530405)
                  ·
                    refine ⟨1243591608394946437786951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6632488578106381001530405 1243591608394946437786951)
                    ·
                      rfl

theorem cell23_7265658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 2, 4].length) (baseStart_7265658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265658 prefixEnd_7265658 := by exact prefixLift 7265658
  have htrace : WordTrace (prefixWord ++ tailWord_7265658) baseStart_7265658 baseEnd_7265658 := by
    simpa [prefixWord, tailWord_7265658, baseEnd_7265658] using wordTrace_append hprefix tailTrace_7265658
  have hstable : (prefixWord ++ tailWord_7265658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265658).length < 2 ^ (prefixWord ++ tailWord_7265658).sum := by decide
  have hdescent : baseEnd_7265658 < baseStart_7265658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265661 : List Nat := [1, 4, 1, 1, 2, 2, 1, 3, 1, 1, 6]
def baseStart_7265661 : Nat := 118140960795 + 7265661 * 2 ^ 59
def prefixEnd_7265661 : Nat := 4983230072969 + 3 ^ 40 * 7265661 * 2
def baseEnd_7265661 : Nat := 3730776365626802801623339

theorem tailTrace_7265661 : CollatzResearch.WordTrace tailWord_7265661 prefixEnd_7265661 3730776365626802801623339 := by
  unfold tailWord_7265661
  simp only [CollatzResearch.WordTrace]
  refine ⟨265000427330758547952716837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176666951553839031968477891 265000427330758547952716837)
  ·
    refine ⟨49687580124517227741134407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265000427330758547952716837 49687580124517227741134407)
    ·
      refine ⟨74531370186775841611701611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49687580124517227741134407 74531370186775841611701611)
      ·
        refine ⟨111797055280163762417552417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74531370186775841611701611 111797055280163762417552417)
        ·
          refine ⟨83847791460122821813164313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111797055280163762417552417 83847791460122821813164313)
          ·
            refine ⟨62885843595092116359873235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83847791460122821813164313 62885843595092116359873235)
            ·
              refine ⟨94328765392638174539809853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62885843595092116359873235 94328765392638174539809853)
              ·
                refine ⟨35373287022239315452428695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94328765392638174539809853 35373287022239315452428695)
                ·
                  refine ⟨53059930533358973178643043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35373287022239315452428695 53059930533358973178643043)
                  ·
                    refine ⟨79589895800038459767964565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53059930533358973178643043 79589895800038459767964565)
                    ·
                      refine ⟨3730776365626802801623339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79589895800038459767964565 3730776365626802801623339)
                      ·
                        rfl

theorem cell23_7265661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_7265661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265661 prefixEnd_7265661 := by exact prefixLift 7265661
  have htrace : WordTrace (prefixWord ++ tailWord_7265661) baseStart_7265661 baseEnd_7265661 := by
    simpa [prefixWord, tailWord_7265661, baseEnd_7265661] using wordTrace_append hprefix tailTrace_7265661
  have hstable : (prefixWord ++ tailWord_7265661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265661).length < 2 ^ (prefixWord ++ tailWord_7265661).sum := by decide
  have hdescent : baseEnd_7265661 < baseStart_7265661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265662 : List Nat := [4, 2, 3, 2, 1, 1, 1, 1, 3, 5]
def baseStart_7265662 : Nat := 118140960795 + 7265662 * 2 ^ 59
def prefixEnd_7265662 : Nat := 4983230072969 + 3 ^ 40 * 7265662 * 2
def baseEnd_7265662 : Nat := 1243592293035819099236945

theorem tailTrace_7265662 : CollatzResearch.WordTrace tailWord_7265662 prefixEnd_7265662 1243592293035819099236945 := by
  unfold tailWord_7265662
  simp only [CollatzResearch.WordTrace]
  refine ⟨33125057975469365640437905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176666975869169950082335493 33125057975469365640437905)
  ·
    refine ⟨24843793481602024230328429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33125057975469365640437905 24843793481602024230328429)
    ·
      refine ⟨9316422555600759086373161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24843793481602024230328429 9316422555600759086373161)
      ·
        refine ⟨6987316916700569314779871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9316422555600759086373161 6987316916700569314779871)
        ·
          refine ⟨10480975375050853972169807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6987316916700569314779871 10480975375050853972169807)
          ·
            refine ⟨15721463062576280958254711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10480975375050853972169807 15721463062576280958254711)
            ·
              refine ⟨23582194593864421437382067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15721463062576280958254711 23582194593864421437382067)
              ·
                refine ⟨35373291890796632156073101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23582194593864421437382067 35373291890796632156073101)
                ·
                  refine ⟨13264984459048737058527413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35373291890796632156073101 13264984459048737058527413)
                  ·
                    refine ⟨1243592293035819099236945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13264984459048737058527413 1243592293035819099236945)
                    ·
                      rfl

theorem cell23_7265662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_7265662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265662 prefixEnd_7265662 := by exact prefixLift 7265662
  have htrace : WordTrace (prefixWord ++ tailWord_7265662) baseStart_7265662 baseEnd_7265662 := by
    simpa [prefixWord, tailWord_7265662, baseEnd_7265662] using wordTrace_append hprefix tailTrace_7265662
  have hstable : (prefixWord ++ tailWord_7265662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265662).length < 2 ^ (prefixWord ++ tailWord_7265662).sum := by decide
  have hdescent : baseEnd_7265662 < baseStart_7265662 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265665 : List Nat := [1, 2, 4, 3, 2, 1, 1, 1, 3, 1, 4]
def baseStart_7265665 : Nat := 118140960795 + 7265665 * 2 ^ 59
def prefixEnd_7265665 : Nat := 4983230072969 + 3 ^ 40 * 7265665 * 2
def baseEnd_7265665 : Nat := 3730778419549420785973321

theorem tailTrace_7265665 : CollatzResearch.WordTrace tailWord_7265665 prefixEnd_7265665 3730778419549420785973321 := by
  unfold tailWord_7265665
  simp only [CollatzResearch.WordTrace]
  refine ⟨265000573222744056635862449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176667048815162704423908299 265000573222744056635862449)
  ·
    refine ⟨198750429917058042476896837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265000573222744056635862449 198750429917058042476896837)
    ·
      refine ⟨37265705609448382964418157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198750429917058042476896837 37265705609448382964418157)
      ·
        refine ⟨13974639603543143611656809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37265705609448382964418157 13974639603543143611656809)
        ·
          refine ⟨10480979702657357708742607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13974639603543143611656809 10480979702657357708742607)
          ·
            refine ⟨15721469553986036563113911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10480979702657357708742607 15721469553986036563113911)
            ·
              refine ⟨23582204330979054844670867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15721469553986036563113911 23582204330979054844670867)
              ·
                refine ⟨35373306496468582267006301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23582204330979054844670867 35373306496468582267006301)
                ·
                  refine ⟨13264989936175718350127363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35373306496468582267006301 13264989936175718350127363)
                  ·
                    refine ⟨19897484904263577525191045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13264989936175718350127363 19897484904263577525191045)
                    ·
                      refine ⟨3730778419549420785973321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19897484904263577525191045 3730778419549420785973321)
                      ·
                        rfl

theorem cell23_7265665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_7265665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265665 prefixEnd_7265665 := by exact prefixLift 7265665
  have htrace : WordTrace (prefixWord ++ tailWord_7265665) baseStart_7265665 baseEnd_7265665 := by
    simpa [prefixWord, tailWord_7265665, baseEnd_7265665] using wordTrace_append hprefix tailTrace_7265665
  have hstable : (prefixWord ++ tailWord_7265665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265665).length < 2 ^ (prefixWord ++ tailWord_7265665).sum := by decide
  have hdescent : baseEnd_7265665 < baseStart_7265665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265671 : List Nat := [1, 1, 4, 2, 2, 2, 2, 9]
def baseStart_7265671 : Nat := 118140960795 + 7265671 * 2 ^ 59
def prefixEnd_7265671 : Nat := 4983230072969 + 3 ^ 40 * 7265671 * 2
def baseEnd_7265671 : Nat := 138177092608642509722159

theorem tailTrace_7265671 : CollatzResearch.WordTrace tailWord_7265671 prefixEnd_7265671 138177092608642509722159 := by
  unfold tailWord_7265671
  simp only [CollatzResearch.WordTrace]
  refine ⟨265000792060722319660580867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176667194707148213107053911 265000792060722319660580867)
  ·
    refine ⟨397501188091083479490871301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265000792060722319660580867 397501188091083479490871301)
    ·
      refine ⟨74531472767078152404538369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 397501188091083479490871301 74531472767078152404538369)
      ·
        refine ⟨55898604575308614303403777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74531472767078152404538369 55898604575308614303403777)
        ·
          refine ⟨41923953431481460727552833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55898604575308614303403777 41923953431481460727552833)
          ·
            refine ⟨31442965073611095545664625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41923953431481460727552833 31442965073611095545664625)
            ·
              refine ⟨23582223805208321659248469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31442965073611095545664625 23582223805208321659248469)
              ·
                refine ⟨138177092608642509722159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23582223805208321659248469 138177092608642509722159)
                ·
                  rfl

theorem cell23_7265671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 9].length) (baseStart_7265671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265671 prefixEnd_7265671 := by exact prefixLift 7265671
  have htrace : WordTrace (prefixWord ++ tailWord_7265671) baseStart_7265671 baseEnd_7265671 := by
    simpa [prefixWord, tailWord_7265671, baseEnd_7265671] using wordTrace_append hprefix tailTrace_7265671
  have hstable : (prefixWord ++ tailWord_7265671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265671).length < 2 ^ (prefixWord ++ tailWord_7265671).sum := by decide
  have hdescent : baseEnd_7265671 < baseStart_7265671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265688 : List Nat := [2, 1, 2, 5, 3, 10]
def baseStart_7265688 : Nat := 118140960795 + 7265688 * 2 ^ 59
def prefixEnd_7265688 : Nat := 4983230072969 + 3 ^ 40 * 7265688 * 2
def baseEnd_7265688 : Nat := 15353046212364091341505

theorem tailTrace_7265688 : CollatzResearch.WordTrace tailWord_7265688 prefixEnd_7265688 15353046212364091341505 := by
  unfold tailWord_7265688
  simp only [CollatzResearch.WordTrace]
  refine ⟨132500706050830365781974859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176667608067773821042633145 132500706050830365781974859)
  ·
    refine ⟨198751059076245548672962289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132500706050830365781974859 198751059076245548672962289)
    ·
      refine ⟨149063294307184161504721717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198751059076245548672962289 149063294307184161504721717)
      ·
        refine ⟨13974683841298515141067661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149063294307184161504721717 13974683841298515141067661)
        ·
          refine ⟨5240506440486943177900373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13974683841298515141067661 5240506440486943177900373)
          ·
            refine ⟨15353046212364091341505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5240506440486943177900373 15353046212364091341505)
            ·
              rfl

theorem cell23_7265688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 10].length) (baseStart_7265688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265688 prefixEnd_7265688 := by exact prefixLift 7265688
  have htrace : WordTrace (prefixWord ++ tailWord_7265688) baseStart_7265688 baseEnd_7265688 := by
    simpa [prefixWord, tailWord_7265688, baseEnd_7265688] using wordTrace_append hprefix tailTrace_7265688
  have hstable : (prefixWord ++ tailWord_7265688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265688).length < 2 ^ (prefixWord ++ tailWord_7265688).sum := by decide
  have hdescent : baseEnd_7265688 < baseStart_7265688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265725 : List Nat := [1, 4, 1, 2, 2, 1, 1, 3, 3, 3, 2]
def baseStart_7265725 : Nat := 118140960795 + 7265725 * 2 ^ 59
def prefixEnd_7265725 : Nat := 4983230072969 + 3 ^ 40 * 7265725 * 2
def baseEnd_7265725 : Nat := 3730809228388690551223045

theorem tailTrace_7265725 : CollatzResearch.WordTrace tailWord_7265725 prefixEnd_7265725 3730809228388690551223045 := by
  unfold tailWord_7265725
  simp only [CollatzResearch.WordTrace]
  refine ⟨265002761602526686883046629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176668507735017791255364419 265002761602526686883046629)
  ·
    refine ⟨49688017800473753790571243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265002761602526686883046629 49688017800473753790571243)
    ·
      refine ⟨74532026700710630685856865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49688017800473753790571243 74532026700710630685856865)
      ·
        refine ⟨55899020025532973014392649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74532026700710630685856865 55899020025532973014392649)
        ·
          refine ⟨41924265019149729760794487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55899020025532973014392649 41924265019149729760794487)
          ·
            refine ⟨62886397528724594641191731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41924265019149729760794487 62886397528724594641191731)
            ·
              refine ⟨94329596293086891961787597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62886397528724594641191731 94329596293086891961787597)
              ·
                refine ⟨35373598609907584485670349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94329596293086891961787597 35373598609907584485670349)
                ·
                  refine ⟨13265099478715344182126381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35373598609907584485670349 13265099478715344182126381)
                  ·
                    refine ⟨4974412304518254068297393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13265099478715344182126381 4974412304518254068297393)
                    ·
                      refine ⟨3730809228388690551223045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4974412304518254068297393 3730809228388690551223045)
                      ·
                        rfl

theorem cell23_7265725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_7265725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265725 prefixEnd_7265725 := by exact prefixLift 7265725
  have htrace : WordTrace (prefixWord ++ tailWord_7265725) baseStart_7265725 baseEnd_7265725 := by
    simpa [prefixWord, tailWord_7265725, baseEnd_7265725] using wordTrace_append hprefix tailTrace_7265725
  have hstable : (prefixWord ++ tailWord_7265725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265725).length < 2 ^ (prefixWord ++ tailWord_7265725).sum := by decide
  have hdescent : baseEnd_7265725 < baseStart_7265725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265730 : List Nat := [3, 5, 2, 1, 2, 1, 2, 1, 1, 5]
def baseStart_7265730 : Nat := 118140960795 + 7265730 * 2 ^ 59
def prefixEnd_7265730 : Nat := 4983230072969 + 3 ^ 40 * 7265730 * 2
def baseEnd_7265730 : Nat := 1243603931930654343886841

theorem tailTrace_7265730 : CollatzResearch.WordTrace tailWord_7265730 prefixEnd_7265730 1243603931930654343886841 := by
  unfold tailWord_7265730
  simp only [CollatzResearch.WordTrace]
  refine ⟨66250735991877143184244661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176668629311672381824652429 66250735991877143184244661)
  ·
    refine ⟨6211006499238482173522937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66250735991877143184244661 6211006499238482173522937)
    ·
      refine ⟨4658254874428861630142203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6211006499238482173522937 4658254874428861630142203)
      ·
        refine ⟨6987382311643292445213305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4658254874428861630142203 6987382311643292445213305)
        ·
          refine ⟨5240536733732469333909979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6987382311643292445213305 5240536733732469333909979)
          ·
            refine ⟨7860805100598704000864969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5240536733732469333909979 7860805100598704000864969)
            ·
              refine ⟨5895603825449028000648727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7860805100598704000864969 5895603825449028000648727)
              ·
                refine ⟨8843405738173542000973091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5895603825449028000648727 8843405738173542000973091)
                ·
                  refine ⟨13265108607260313001459637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8843405738173542000973091 13265108607260313001459637)
                  ·
                    refine ⟨1243603931930654343886841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13265108607260313001459637 1243603931930654343886841)
                    ·
                      rfl

theorem cell23_7265730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_7265730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265730 prefixEnd_7265730 := by exact prefixLift 7265730
  have htrace : WordTrace (prefixWord ++ tailWord_7265730) baseStart_7265730 baseEnd_7265730 := by
    simpa [prefixWord, tailWord_7265730, baseEnd_7265730] using wordTrace_append hprefix tailTrace_7265730
  have hstable : (prefixWord ++ tailWord_7265730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265730).length < 2 ^ (prefixWord ++ tailWord_7265730).sum := by decide
  have hdescent : baseEnd_7265730 < baseStart_7265730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265768 : List Nat := [2, 1, 4, 1, 1, 2, 1, 3, 2, 2, 4]
def baseStart_7265768 : Nat := 118140960795 + 7265768 * 2 ^ 59
def prefixEnd_7265768 : Nat := 4983230072969 + 3 ^ 40 * 7265768 * 2
def baseEnd_7265768 : Nat := 3730831308056833882985347

theorem tailTrace_7265768 : CollatzResearch.WordTrace tailWord_7265768 prefixEnd_7265768 3730831308056833882985347 := by
  unfold tailWord_7265768
  simp only [CollatzResearch.WordTrace]
  refine ⟨132502164970685452613430979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176669553294247270151241305 132502164970685452613430979)
  ·
    refine ⟨198753247456028178920146469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132502164970685452613430979 198753247456028178920146469)
    ·
      refine ⟨37266233898005283547527463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198753247456028178920146469 37266233898005283547527463)
      ·
        refine ⟨55899350847007925321291195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37266233898005283547527463 55899350847007925321291195)
        ·
          refine ⟨83849026270511887981936793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55899350847007925321291195 83849026270511887981936793)
          ·
            refine ⟨62886769702883915986452595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83849026270511887981936793 62886769702883915986452595)
            ·
              refine ⟨94330154554325873979678893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62886769702883915986452595 94330154554325873979678893)
              ·
                refine ⟨35373807957872202742379585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94330154554325873979678893 35373807957872202742379585)
                ·
                  refine ⟨26530355968404152056784689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35373807957872202742379585 26530355968404152056784689)
                  ·
                    refine ⟨19897766976303114042588517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26530355968404152056784689 19897766976303114042588517)
                    ·
                      refine ⟨3730831308056833882985347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19897766976303114042588517 3730831308056833882985347)
                      ·
                        rfl

theorem cell23_7265768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_7265768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265768 prefixEnd_7265768 := by exact prefixLift 7265768
  have htrace : WordTrace (prefixWord ++ tailWord_7265768) baseStart_7265768 baseEnd_7265768 := by
    simpa [prefixWord, tailWord_7265768, baseEnd_7265768] using wordTrace_append hprefix tailTrace_7265768
  have hstable : (prefixWord ++ tailWord_7265768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265768).length < 2 ^ (prefixWord ++ tailWord_7265768).sum := by decide
  have hdescent : baseEnd_7265768 < baseStart_7265768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265788 : List Nat := [2, 2, 2, 1, 2, 1, 2, 2, 1, 5, 3]
def baseStart_7265788 : Nat := 118140960795 + 7265788 * 2 ^ 59
def prefixEnd_7265788 : Nat := 4983230072969 + 3 ^ 40 * 7265788 * 2
def baseEnd_7265788 : Nat := 3730841577669923804735255

theorem tailTrace_7265788 : CollatzResearch.WordTrace tailWord_7265788 prefixEnd_7265788 3730841577669923804735255 := by
  unfold tailWord_7265788
  simp only [CollatzResearch.WordTrace]
  refine ⟨132502529700649224321295009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176670039600865632428393345 132502529700649224321295009)
  ·
    refine ⟨99376897275486918240971257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132502529700649224321295009 99376897275486918240971257)
    ·
      refine ⟨74532672956615188680728443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99376897275486918240971257 74532672956615188680728443)
      ·
        refine ⟨111799009434922783021092665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74532672956615188680728443 111799009434922783021092665)
        ·
          refine ⟨83849257076192087265819499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111799009434922783021092665 83849257076192087265819499)
          ·
            refine ⟨125773885614288130898729249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83849257076192087265819499 125773885614288130898729249)
            ·
              refine ⟨94330414210716098174046937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125773885614288130898729249 94330414210716098174046937)
              ·
                refine ⟨70747810658037073630535203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94330414210716098174046937 70747810658037073630535203)
                ·
                  refine ⟨106121715987055610445802805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70747810658037073630535203 106121715987055610445802805)
                  ·
                    refine ⟨9948910873786463479294013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 106121715987055610445802805 9948910873786463479294013)
                    ·
                      refine ⟨3730841577669923804735255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9948910873786463479294013 3730841577669923804735255)
                      ·
                        rfl

theorem cell23_7265788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_7265788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265788 prefixEnd_7265788 := by exact prefixLift 7265788
  have htrace : WordTrace (prefixWord ++ tailWord_7265788) baseStart_7265788 baseEnd_7265788 := by
    simpa [prefixWord, tailWord_7265788, baseEnd_7265788] using wordTrace_append hprefix tailTrace_7265788
  have hstable : (prefixWord ++ tailWord_7265788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265788).length < 2 ^ (prefixWord ++ tailWord_7265788).sum := by decide
  have hdescent : baseEnd_7265788 < baseStart_7265788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265845 : List Nat := [1, 3, 3, 1, 1, 3, 1, 3, 2, 1, 4]
def baseStart_7265845 : Nat := 118140960795 + 7265845 * 2 ^ 59
def prefixEnd_7265845 : Nat := 4983230072969 + 3 ^ 40 * 7265845 * 2
def baseEnd_7265845 : Nat := 3730870846067230081722493

theorem tailTrace_7265845 : CollatzResearch.WordTrace tailWord_7265845 prefixEnd_7265845 3730870846067230081722493 := by
  unfold tailWord_7265845
  simp only [CollatzResearch.WordTrace]
  refine ⟨265007138362091947377414989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176671425574727964918276659 265007138362091947377414989)
  ·
    refine ⟨99377676885784480266530621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265007138362091947377414989 99377676885784480266530621)
    ·
      refine ⟨37266628832169180099948983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99377676885784480266530621 37266628832169180099948983)
      ·
        refine ⟨55899943248253770149923475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37266628832169180099948983 55899943248253770149923475)
        ·
          refine ⟨83849914872380655224885213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55899943248253770149923475 83849914872380655224885213)
          ·
            refine ⟨31443718077142745709331955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83849914872380655224885213 31443718077142745709331955)
            ·
              refine ⟨47165577115714118563997933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31443718077142745709331955 47165577115714118563997933)
              ·
                refine ⟨17687091418392794461499225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47165577115714118563997933 17687091418392794461499225)
                ·
                  refine ⟨13265318563794595846124419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17687091418392794461499225 13265318563794595846124419)
                  ·
                    refine ⟨19897977845691893769186629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13265318563794595846124419 19897977845691893769186629)
                    ·
                      refine ⟨3730870846067230081722493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19897977845691893769186629 3730870846067230081722493)
                      ·
                        rfl

theorem cell23_7265845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_7265845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265845 prefixEnd_7265845 := by exact prefixLift 7265845
  have htrace : WordTrace (prefixWord ++ tailWord_7265845) baseStart_7265845 baseEnd_7265845 := by
    simpa [prefixWord, tailWord_7265845, baseEnd_7265845] using wordTrace_append hprefix tailTrace_7265845
  have hstable : (prefixWord ++ tailWord_7265845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265845).length < 2 ^ (prefixWord ++ tailWord_7265845).sum := by decide
  have hdescent : baseEnd_7265845 < baseStart_7265845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265872 : List Nat := [2, 1, 1, 1, 1, 3, 5, 4, 1, 4]
def baseStart_7265872 : Nat := 118140960795 + 7265872 * 2 ^ 59
def prefixEnd_7265872 : Nat := 4983230072969 + 3 ^ 40 * 7265872 * 2
def baseEnd_7265872 : Nat := 1243628236681633825361623

theorem tailTrace_7265872 : CollatzResearch.WordTrace tailWord_7265872 prefixEnd_7265872 1243628236681633825361623 := by
  unfold tailWord_7265872
  simp only [CollatzResearch.WordTrace]
  refine ⟨132504061566497065494323935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176672082088662753992431913 132504061566497065494323935)
  ·
    refine ⟨198756092349745598241485903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132504061566497065494323935 198756092349745598241485903)
    ·
      refine ⟨298134138524618397362228855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198756092349745598241485903 298134138524618397362228855)
      ·
        refine ⟨447201207786927596043343283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298134138524618397362228855 447201207786927596043343283)
        ·
          refine ⟨670801811680391394065014925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447201207786927596043343283 670801811680391394065014925)
          ·
            refine ⟨251550679380146772774380597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 670801811680391394065014925 251550679380146772774380597)
            ·
              refine ⟨23582876191888759947598181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 251550679380146772774380597 23582876191888759947598181)
              ·
                refine ⟨4421789285979142490174659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23582876191888759947598181 4421789285979142490174659)
                ·
                  refine ⟨6632683928968713735261989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4421789285979142490174659 6632683928968713735261989)
                  ·
                    refine ⟨1243628236681633825361623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6632683928968713735261989 1243628236681633825361623)
                    ·
                      rfl

theorem cell23_7265872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 4, 1, 4].length) (baseStart_7265872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265872 prefixEnd_7265872 := by exact prefixLift 7265872
  have htrace : WordTrace (prefixWord ++ tailWord_7265872) baseStart_7265872 baseEnd_7265872 := by
    simpa [prefixWord, tailWord_7265872, baseEnd_7265872] using wordTrace_append hprefix tailTrace_7265872
  have hstable : (prefixWord ++ tailWord_7265872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265872).length < 2 ^ (prefixWord ++ tailWord_7265872).sum := by decide
  have hdescent : baseEnd_7265872 < baseStart_7265872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265915 : List Nat := [1, 1, 1, 1, 1, 4, 5, 3, 1, 5]
def baseStart_7265915 : Nat := 118140960795 + 7265915 * 2 ^ 59
def prefixEnd_7265915 : Nat := 4983230072969 + 3 ^ 40 * 7265915 * 2
def baseEnd_7265915 : Nat := 1243635596571014935949057

theorem tailTrace_7265915 : CollatzResearch.WordTrace tailWord_7265915 prefixEnd_7265915 1243635596571014935949057 := by
  unfold tailWord_7265915
  simp only [CollatzResearch.WordTrace]
  refine ⟨265009691471838349332463199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176673127647892232888308799 265009691471838349332463199)
  ·
    refine ⟨397514537207757523998694799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265009691471838349332463199 397514537207757523998694799)
    ·
      refine ⟨596271805811636285998042199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397514537207757523998694799 596271805811636285998042199)
      ·
        refine ⟨894407708717454428997063299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596271805811636285998042199 894407708717454428997063299)
        ·
          refine ⟨1341611563076181643495594949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 894407708717454428997063299 1341611563076181643495594949)
          ·
            refine ⟨251552168076784058155424053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1341611563076181643495594949 251552168076784058155424053)
            ·
              refine ⟨23583015757198505452071005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 251552168076784058155424053 23583015757198505452071005)
              ·
                refine ⟨8843630908949439544526627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23583015757198505452071005 8843630908949439544526627)
                ·
                  refine ⟨13265446363424159316789941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8843630908949439544526627 13265446363424159316789941)
                  ·
                    refine ⟨1243635596571014935949057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13265446363424159316789941 1243635596571014935949057)
                    ·
                      rfl

theorem cell23_7265915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 5].length) (baseStart_7265915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265915 prefixEnd_7265915 := by exact prefixLift 7265915
  have htrace : WordTrace (prefixWord ++ tailWord_7265915) baseStart_7265915 baseEnd_7265915 := by
    simpa [prefixWord, tailWord_7265915, baseEnd_7265915] using wordTrace_append hprefix tailTrace_7265915
  have hstable : (prefixWord ++ tailWord_7265915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265915).length < 2 ^ (prefixWord ++ tailWord_7265915).sum := by decide
  have hdescent : baseEnd_7265915 < baseStart_7265915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265929 : List Nat := [1, 2, 1, 1, 4, 1, 4, 4, 1, 1, 3]
def baseStart_7265929 : Nat := 118140960795 + 7265929 * 2 ^ 59
def prefixEnd_7265929 : Nat := 4983230072969 + 3 ^ 40 * 7265929 * 2
def baseEnd_7265929 : Nat := 3730913978442207753072107

theorem tailTrace_7265929 : CollatzResearch.WordTrace tailWord_7265929 prefixEnd_7265929 3730913978442207753072107 := by
  unfold tailWord_7265929
  simp only [CollatzResearch.WordTrace]
  refine ⟨265010202093787629723472841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176673468062525086482315227 265010202093787629723472841)
  ·
    refine ⟨198757651570340722292604631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265010202093787629723472841 198757651570340722292604631)
    ·
      refine ⟨298136477355511083438906947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198757651570340722292604631 298136477355511083438906947)
      ·
        refine ⟨447204716033266625158360421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298136477355511083438906947 447204716033266625158360421)
        ·
          refine ⟨83850884256237492217192579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 447204716033266625158360421 83850884256237492217192579)
          ·
            refine ⟨125776326384356238325788869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83850884256237492217192579 125776326384356238325788869)
            ·
              refine ⟨23583061197066794686085413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125776326384356238325788869 23583061197066794686085413)
              ·
                refine ⟨4421823974450024003641015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23583061197066794686085413 4421823974450024003641015)
                ·
                  refine ⟨6632735961675036005461523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4421823974450024003641015 6632735961675036005461523)
                  ·
                    refine ⟨9949103942512554008192285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6632735961675036005461523 9949103942512554008192285)
                    ·
                      refine ⟨3730913978442207753072107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9949103942512554008192285 3730913978442207753072107)
                      ·
                        rfl

theorem cell23_7265929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 4, 1, 1, 3].length) (baseStart_7265929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265929 prefixEnd_7265929 := by exact prefixLift 7265929
  have htrace : WordTrace (prefixWord ++ tailWord_7265929) baseStart_7265929 baseEnd_7265929 := by
    simpa [prefixWord, tailWord_7265929, baseEnd_7265929] using wordTrace_append hprefix tailTrace_7265929
  have hstable : (prefixWord ++ tailWord_7265929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265929).length < 2 ^ (prefixWord ++ tailWord_7265929).sum := by decide
  have hdescent : baseEnd_7265929 < baseStart_7265929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265935 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 4, 6, 2]
def baseStart_7265935 : Nat := 118140960795 + 7265935 * 2 ^ 59
def prefixEnd_7265935 : Nat := 4983230072969 + 3 ^ 40 * 7265935 * 2
def baseEnd_7265935 : Nat := 3730917059326134729597079

theorem tailTrace_7265935 : CollatzResearch.WordTrace tailWord_7265935 prefixEnd_7265935 3730917059326134729597079 := by
  unfold tailWord_7265935
  simp only [CollatzResearch.WordTrace]
  refine ⟨265010420931765892748191259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176673613954510595165460839 265010420931765892748191259)
  ·
    refine ⟨397515631397648839122286889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265010420931765892748191259 397515631397648839122286889)
    ·
      refine ⟨298136723548236629341715167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397515631397648839122286889 298136723548236629341715167)
      ·
        refine ⟨447205085322354944012572751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298136723548236629341715167 447205085322354944012572751)
        ·
          refine ⟨670807627983532416018859127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447205085322354944012572751 670807627983532416018859127)
          ·
            refine ⟨1006211441975298624028288691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670807627983532416018859127 1006211441975298624028288691)
            ·
              refine ⟨1509317162962947936042433037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1006211441975298624028288691 1509317162962947936042433037)
              ·
                refine ⟨565993936111105476015912389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1509317162962947936042433037 565993936111105476015912389)
                ·
                  refine ⟨106123863020832276752983573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 565993936111105476015912389 106123863020832276752983573)
                  ·
                    refine ⟨4974556079101512972796105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106123863020832276752983573 4974556079101512972796105)
                    ·
                      refine ⟨3730917059326134729597079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4974556079101512972796105 3730917059326134729597079)
                      ·
                        rfl

theorem cell23_7265935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 6, 2].length) (baseStart_7265935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265935 prefixEnd_7265935 := by exact prefixLift 7265935
  have htrace : WordTrace (prefixWord ++ tailWord_7265935) baseStart_7265935 baseEnd_7265935 := by
    simpa [prefixWord, tailWord_7265935, baseEnd_7265935] using wordTrace_append hprefix tailTrace_7265935
  have hstable : (prefixWord ++ tailWord_7265935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265935).length < 2 ^ (prefixWord ++ tailWord_7265935).sum := by decide
  have hdescent : baseEnd_7265935 < baseStart_7265935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265952 : List Nat := [2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 4]
def baseStart_7265952 : Nat := 118140960795 + 7265952 * 2 ^ 59
def prefixEnd_7265952 : Nat := 4983230072969 + 3 ^ 40 * 7265952 * 2
def baseEnd_7265952 : Nat := 3730925788497261163084501

theorem tailTrace_7265952 : CollatzResearch.WordTrace tailWord_7265952 prefixEnd_7265952 3730925788497261163084501 := by
  unfold tailWord_7265952
  simp only [CollatzResearch.WordTrace]
  refine ⟨132505520486352152325780055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176674027315136203101040073 132505520486352152325780055)
  ·
    refine ⟨198758280729528228488670083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132505520486352152325780055 198758280729528228488670083)
    ·
      refine ⟨298137421094292342733005125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198758280729528228488670083 298137421094292342733005125)
      ·
        refine ⟨55900766455179814262438461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 298137421094292342733005125 55900766455179814262438461)
        ·
          refine ⟨20962787420692430348414423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55900766455179814262438461 20962787420692430348414423)
          ·
            refine ⟨31444181131038645522621635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20962787420692430348414423 31444181131038645522621635)
            ·
              refine ⟨47166271696557968283932453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31444181131038645522621635 47166271696557968283932453)
              ·
                refine ⟨8843675943104619053237335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47166271696557968283932453 8843675943104619053237335)
                ·
                  refine ⟨13265513914656928579856003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8843675943104619053237335 13265513914656928579856003)
                  ·
                    refine ⟨19898270871985392869784005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13265513914656928579856003 19898270871985392869784005)
                    ·
                      refine ⟨3730925788497261163084501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19898270871985392869784005 3730925788497261163084501)
                      ·
                        rfl

theorem cell23_7265952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_7265952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265952 prefixEnd_7265952 := by exact prefixLift 7265952
  have htrace : WordTrace (prefixWord ++ tailWord_7265952) baseStart_7265952 baseEnd_7265952 := by
    simpa [prefixWord, tailWord_7265952, baseEnd_7265952] using wordTrace_append hprefix tailTrace_7265952
  have hstable : (prefixWord ++ tailWord_7265952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265952).length < 2 ^ (prefixWord ++ tailWord_7265952).sum := by decide
  have hdescent : baseEnd_7265952 < baseStart_7265952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7265975 : List Nat := [1, 1, 3, 1, 5, 3, 9]
def baseStart_7265975 : Nat := 118140960795 + 7265975 * 2 ^ 59
def prefixEnd_7265975 : Nat := 4983230072969 + 3 ^ 40 * 7265975 * 2
def baseEnd_7265975 : Nat := 46060958006818698433295

theorem tailTrace_7265975 : CollatzResearch.WordTrace tailWord_7265975 prefixEnd_7265975 46060958006818698433295 := by
  unfold tailWord_7265975
  simp only [CollatzResearch.WordTrace]
  refine ⟨265011879851620979579647379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176674586567747319719764919 265011879851620979579647379)
  ·
    refine ⟨397517819777431469369471069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265011879851620979579647379 397517819777431469369471069)
    ·
      refine ⟨149069182416536801013551651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 397517819777431469369471069 149069182416536801013551651)
      ·
        refine ⟨223603773624805201520327477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149069182416536801013551651 223603773624805201520327477)
        ·
          refine ⟨20962853777325487642530701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 223603773624805201520327477 20962853777325487642530701)
          ·
            refine ⟨7861070166497057865949013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20962853777325487642530701 7861070166497057865949013)
            ·
              refine ⟨46060958006818698433295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7861070166497057865949013 46060958006818698433295)
              ·
                rfl

theorem cell23_7265975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 9].length) (baseStart_7265975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7265975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7265975 prefixEnd_7265975 := by exact prefixLift 7265975
  have htrace : WordTrace (prefixWord ++ tailWord_7265975) baseStart_7265975 baseEnd_7265975 := by
    simpa [prefixWord, tailWord_7265975, baseEnd_7265975] using wordTrace_append hprefix tailTrace_7265975
  have hstable : (prefixWord ++ tailWord_7265975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7265975).length < 2 ^ (prefixWord ++ tailWord_7265975).sum := by decide
  have hdescent : baseEnd_7265975 < baseStart_7265975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7265975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266019 : List Nat := [1, 1, 1, 7, 2, 1, 1, 2, 1, 3, 3]
def baseStart_7266019 : Nat := 118140960795 + 7266019 * 2 ^ 59
def prefixEnd_7266019 : Nat := 4983230072969 + 3 ^ 40 * 7266019 * 2
def baseEnd_7266019 : Nat := 3730960191701112400946693

theorem tailTrace_7266019 : CollatzResearch.WordTrace tailWord_7266019 prefixEnd_7266019 3730960191701112400946693 := by
  unfold tailWord_7266019
  simp only [CollatzResearch.WordTrace]
  refine ⟨265013484663461575094249111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176675656442307716729499407 265013484663461575094249111)
  ·
    refine ⟨397520226995192362641373667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265013484663461575094249111 397520226995192362641373667)
    ·
      refine ⟨596280340492788543962060501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397520226995192362641373667 596280340492788543962060501)
      ·
        refine ⟨13975320480299731499110793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 596280340492788543962060501 13975320480299731499110793)
        ·
          refine ⟨10481490360224798624333095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13975320480299731499110793 10481490360224798624333095)
          ·
            refine ⟨15722235540337197936499643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10481490360224798624333095 15722235540337197936499643)
            ·
              refine ⟨23583353310505796904749465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15722235540337197936499643 23583353310505796904749465)
              ·
                refine ⟨17687514982879347678562099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23583353310505796904749465 17687514982879347678562099)
                ·
                  refine ⟨26531272474319021517843149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17687514982879347678562099 26531272474319021517843149)
                  ·
                    refine ⟨9949227177869633069191181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26531272474319021517843149 9949227177869633069191181)
                    ·
                      refine ⟨3730960191701112400946693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9949227177869633069191181 3730960191701112400946693)
                      ·
                        rfl

theorem cell23_7266019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_7266019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266019 prefixEnd_7266019 := by exact prefixLift 7266019
  have htrace : WordTrace (prefixWord ++ tailWord_7266019) baseStart_7266019 baseEnd_7266019 := by
    simpa [prefixWord, tailWord_7266019, baseEnd_7266019] using wordTrace_append hprefix tailTrace_7266019
  have hstable : (prefixWord ++ tailWord_7266019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266019).length < 2 ^ (prefixWord ++ tailWord_7266019).sum := by decide
  have hdescent : baseEnd_7266019 < baseStart_7266019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266023 : List Nat := [1, 1, 5, 4, 1, 1, 3, 1, 1, 2, 3]
def baseStart_7266023 : Nat := 118140960795 + 7266023 * 2 ^ 59
def prefixEnd_7266023 : Nat := 4983230072969 + 3 ^ 40 * 7266023 * 2
def baseEnd_7266023 : Nat := 3730962245623730385296675

theorem tailTrace_7266023 : CollatzResearch.WordTrace tailWord_7266023 prefixEnd_7266023 3730962245623730385296675 := by
  unfold tailWord_7266023
  simp only [CollatzResearch.WordTrace]
  refine ⟨265013630555447083777394723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176675753703631389184929815 265013630555447083777394723)
  ·
    refine ⟨397520445833170625666092085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265013630555447083777394723 397520445833170625666092085)
    ·
      refine ⟨37267541796859746156196133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 397520445833170625666092085 37267541796859746156196133)
      ·
        refine ⟨6987664086911202404286775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37267541796859746156196133 6987664086911202404286775)
        ·
          refine ⟨10481496130366803606430163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6987664086911202404286775 10481496130366803606430163)
          ·
            refine ⟨15722244195550205409645245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10481496130366803606430163 15722244195550205409645245)
            ·
              refine ⟨5895841573331327028616967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15722244195550205409645245 5895841573331327028616967)
              ·
                refine ⟨8843762359996990542925451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5895841573331327028616967 8843762359996990542925451)
                ·
                  refine ⟨13265643539995485814388177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8843762359996990542925451 13265643539995485814388177)
                  ·
                    refine ⟨9949232654996614360791133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13265643539995485814388177 9949232654996614360791133)
                    ·
                      refine ⟨3730962245623730385296675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9949232654996614360791133 3730962245623730385296675)
                      ·
                        rfl

theorem cell23_7266023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_7266023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266023 prefixEnd_7266023 := by exact prefixLift 7266023
  have htrace : WordTrace (prefixWord ++ tailWord_7266023) baseStart_7266023 baseEnd_7266023 := by
    simpa [prefixWord, tailWord_7266023, baseEnd_7266023] using wordTrace_append hprefix tailTrace_7266023
  have hstable : (prefixWord ++ tailWord_7266023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266023).length < 2 ^ (prefixWord ++ tailWord_7266023).sum := by decide
  have hdescent : baseEnd_7266023 < baseStart_7266023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266042 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 5, 4, 2]
def baseStart_7266042 : Nat := 118140960795 + 7266042 * 2 ^ 59
def prefixEnd_7266042 : Nat := 4983230072969 + 3 ^ 40 * 7266042 * 2
def baseEnd_7266042 : Nat := 3730972001756165810959087

theorem tailTrace_7266042 : CollatzResearch.WordTrace tailWord_7266042 prefixEnd_7266042 3730972001756165810959087 := by
  unfold tailWord_7266042
  simp only [CollatzResearch.WordTrace]
  refine ⟨66253580885594562505584095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176676215694918833348224253 66253580885594562505584095)
  ·
    refine ⟨99380371328391843758376143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66253580885594562505584095 99380371328391843758376143)
    ·
      refine ⟨149070556992587765637564215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99380371328391843758376143 149070556992587765637564215)
      ·
        refine ⟨223605835488881648456346323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149070556992587765637564215 223605835488881648456346323)
        ·
          refine ⟨335408753233322472684519485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223605835488881648456346323 335408753233322472684519485)
          ·
            refine ⟨125778282462495927256694807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 335408753233322472684519485 125778282462495927256694807)
            ·
              refine ⟨188667423693743890885042211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125778282462495927256694807 188667423693743890885042211)
              ·
                refine ⟨283001135540615836327563317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188667423693743890885042211 283001135540615836327563317)
                ·
                  refine ⟨26531356456932734655709061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 283001135540615836327563317 26531356456932734655709061)
                  ·
                    refine ⟨4974629335674887747945449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26531356456932734655709061 4974629335674887747945449)
                    ·
                      refine ⟨3730972001756165810959087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4974629335674887747945449 3730972001756165810959087)
                      ·
                        rfl

theorem cell23_7266042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 5, 4, 2].length) (baseStart_7266042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266042 prefixEnd_7266042 := by exact prefixLift 7266042
  have htrace : WordTrace (prefixWord ++ tailWord_7266042) baseStart_7266042 baseEnd_7266042 := by
    simpa [prefixWord, tailWord_7266042, baseEnd_7266042] using wordTrace_append hprefix tailTrace_7266042
  have hstable : (prefixWord ++ tailWord_7266042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266042).length < 2 ^ (prefixWord ++ tailWord_7266042).sum := by decide
  have hdescent : baseEnd_7266042 < baseStart_7266042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266045 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 4, 1, 5]
def baseStart_7266045 : Nat := 118140960795 + 7266045 * 2 ^ 59
def prefixEnd_7266045 : Nat := 4983230072969 + 3 ^ 40 * 7266045 * 2
def baseEnd_7266045 : Nat := 3730973542198129299221573

theorem tailTrace_7266045 : CollatzResearch.WordTrace tailWord_7266045 prefixEnd_7266045 3730973542198129299221573 := by
  unfold tailWord_7266045
  simp only [CollatzResearch.WordTrace]
  refine ⟨265014432961367381534695589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176676288640911587689797059 265014432961367381534695589)
  ·
    refine ⟨49690206180256384037755423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265014432961367381534695589 49690206180256384037755423)
    ·
      refine ⟨74535309270384576056633135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49690206180256384037755423 74535309270384576056633135)
      ·
        refine ⟨111802963905576864084949703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74535309270384576056633135 111802963905576864084949703)
        ·
          refine ⟨167704445858365296127424555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111802963905576864084949703 167704445858365296127424555)
          ·
            refine ⟨251556668787547944191136833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167704445858365296127424555 251556668787547944191136833)
            ·
              refine ⟨188667501590660958143352625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251556668787547944191136833 188667501590660958143352625)
              ·
                refine ⟨141500626192995718607514469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188667501590660958143352625 141500626192995718607514469)
                ·
                  refine ⟨26531367411186697238908963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141500626192995718607514469 26531367411186697238908963)
                  ·
                    refine ⟨39797051116780045858363445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26531367411186697238908963 39797051116780045858363445)
                    ·
                      refine ⟨3730973542198129299221573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39797051116780045858363445 3730973542198129299221573)
                      ·
                        rfl

theorem cell23_7266045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_7266045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266045 prefixEnd_7266045 := by exact prefixLift 7266045
  have htrace : WordTrace (prefixWord ++ tailWord_7266045) baseStart_7266045 baseEnd_7266045 := by
    simpa [prefixWord, tailWord_7266045, baseEnd_7266045] using wordTrace_append hprefix tailTrace_7266045
  have hstable : (prefixWord ++ tailWord_7266045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266045).length < 2 ^ (prefixWord ++ tailWord_7266045).sum := by decide
  have hdescent : baseEnd_7266045 < baseStart_7266045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266052 : List Nat := [2, 3, 2, 2, 1, 3, 1, 1, 2, 6]
def baseStart_7266052 : Nat := 118140960795 + 7266052 * 2 ^ 59
def prefixEnd_7266052 : Nat := 4983230072969 + 3 ^ 40 * 7266052 * 2
def baseEnd_7266052 : Nat := 1243659045520903590611347

theorem tailTrace_7266052 : CollatzResearch.WordTrace tailWord_7266052 prefixEnd_7266052 1243659045520903590611347 := by
  unfold tailWord_7266052
  simp only [CollatzResearch.WordTrace]
  refine ⟨132507344136171010865100205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176676458848228014486800273 132507344136171010865100205)
  ·
    refine ⟨49690254051064129074412577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132507344136171010865100205 49690254051064129074412577)
    ·
      refine ⟨37267690538298096805809433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49690254051064129074412577 37267690538298096805809433)
      ·
        refine ⟨27950767903723572604357075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37267690538298096805809433 27950767903723572604357075)
        ·
          refine ⟨41926151855585358906535613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27950767903723572604357075 41926151855585358906535613)
          ·
            refine ⟨15722306945844509589950855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41926151855585358906535613 15722306945844509589950855)
            ·
              refine ⟨23583460418766764384926283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15722306945844509589950855 23583460418766764384926283)
              ·
                refine ⟨35375190628150146577389425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23583460418766764384926283 35375190628150146577389425)
                ·
                  refine ⟨26531392971112609933042069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35375190628150146577389425 26531392971112609933042069)
                  ·
                    refine ⟨1243659045520903590611347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26531392971112609933042069 1243659045520903590611347)
                    ·
                      rfl

theorem cell23_7266052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_7266052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266052 prefixEnd_7266052 := by exact prefixLift 7266052
  have htrace : WordTrace (prefixWord ++ tailWord_7266052) baseStart_7266052 baseEnd_7266052 := by
    simpa [prefixWord, tailWord_7266052, baseEnd_7266052] using wordTrace_append hprefix tailTrace_7266052
  have hstable : (prefixWord ++ tailWord_7266052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266052).length < 2 ^ (prefixWord ++ tailWord_7266052).sum := by decide
  have hdescent : baseEnd_7266052 < baseStart_7266052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266054 : List Nat := [6, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2]
def baseStart_7266054 : Nat := 118140960795 + 7266054 * 2 ^ 59
def prefixEnd_7266054 : Nat := 4983230072969 + 3 ^ 40 * 7266054 * 2
def baseEnd_7266054 : Nat := 3730978163524019764009033

theorem tailTrace_7266054 : CollatzResearch.WordTrace tailWord_7266054 prefixEnd_7266054 3730978163524019764009033 := by
  unfold tailWord_7266054
  simp only [CollatzResearch.WordTrace]
  refine ⟨8281711288072961752242913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 176676507478889850714515477 8281711288072961752242913)
  ·
    refine ⟨6211283466054721314182185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8281711288072961752242913 6211283466054721314182185)
    ·
      refine ⟨4658462599541040985636639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6211283466054721314182185 4658462599541040985636639)
      ·
        refine ⟨6987693899311561478454959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4658462599541040985636639 6987693899311561478454959)
        ·
          refine ⟨10481540848967342217682439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6987693899311561478454959 10481540848967342217682439)
          ·
            refine ⟨15722311273451013326523659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10481540848967342217682439 15722311273451013326523659)
            ·
              refine ⟨23583466910176519989785489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15722311273451013326523659 23583466910176519989785489)
              ·
                refine ⟨17687600182632389992339117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23583466910176519989785489 17687600182632389992339117)
                ·
                  refine ⟨6632850068487146247127169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17687600182632389992339117 6632850068487146247127169)
                  ·
                    refine ⟨4974637551365359685345377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6632850068487146247127169 4974637551365359685345377)
                    ·
                      refine ⟨3730978163524019764009033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4974637551365359685345377 3730978163524019764009033)
                      ·
                        rfl

theorem cell23_7266054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_7266054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266054 prefixEnd_7266054 := by exact prefixLift 7266054
  have htrace : WordTrace (prefixWord ++ tailWord_7266054) baseStart_7266054 baseEnd_7266054 := by
    simpa [prefixWord, tailWord_7266054, baseEnd_7266054] using wordTrace_append hprefix tailTrace_7266054
  have hstable : (prefixWord ++ tailWord_7266054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266054).length < 2 ^ (prefixWord ++ tailWord_7266054).sum := by decide
  have hdescent : baseEnd_7266054 < baseStart_7266054 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266092 : List Nat := [2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 3]
def baseStart_7266092 : Nat := 118140960795 + 7266092 * 2 ^ 59
def prefixEnd_7266092 : Nat := 4983230072969 + 3 ^ 40 * 7266092 * 2
def baseEnd_7266092 : Nat := 3730997675788890615333857

theorem tailTrace_7266092 : CollatzResearch.WordTrace tailWord_7266092 prefixEnd_7266092 3730997675788890615333857 := by
  unfold tailWord_7266092
  simp only [CollatzResearch.WordTrace]
  refine ⟨132508073596098554280828265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176677431461464739041104353 132508073596098554280828265)
  ·
    refine ⟨99381055197073915710621199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132508073596098554280828265 99381055197073915710621199)
    ·
      refine ⟨149071582795610873565931799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99381055197073915710621199 149071582795610873565931799)
      ·
        refine ⟨223607374193416310348897699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149071582795610873565931799 223607374193416310348897699)
        ·
          refine ⟨335411061290124465523346549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223607374193416310348897699 335411061290124465523346549)
          ·
            refine ⟨31444786995949168642813739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 335411061290124465523346549 31444786995949168642813739)
            ·
              refine ⟨47167180493923752964220609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31444786995949168642813739 47167180493923752964220609)
              ·
                refine ⟨35375385370442814723165457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47167180493923752964220609 35375385370442814723165457)
                ·
                  refine ⟨26531539027832111042374093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35375385370442814723165457 26531539027832111042374093)
                  ·
                    refine ⟨9949327135437041640890285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26531539027832111042374093 9949327135437041640890285)
                    ·
                      refine ⟨3730997675788890615333857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9949327135437041640890285 3730997675788890615333857)
                      ·
                        rfl

theorem cell23_7266092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 3].length) (baseStart_7266092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266092 prefixEnd_7266092 := by exact prefixLift 7266092
  have htrace : WordTrace (prefixWord ++ tailWord_7266092) baseStart_7266092 baseEnd_7266092 := by
    simpa [prefixWord, tailWord_7266092, baseEnd_7266092] using wordTrace_append hprefix tailTrace_7266092
  have hstable : (prefixWord ++ tailWord_7266092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266092).length < 2 ^ (prefixWord ++ tailWord_7266092).sum := by decide
  have hdescent : baseEnd_7266092 < baseStart_7266092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266109 : List Nat := [1, 4, 1, 4, 1, 1, 2, 1, 2, 3, 3]
def baseStart_7266109 : Nat := 118140960795 + 7266109 * 2 ^ 59
def prefixEnd_7266109 : Nat := 4983230072969 + 3 ^ 40 * 7266109 * 2
def baseEnd_7266109 : Nat := 3731006404960017048821279

theorem tailTrace_7266109 : CollatzResearch.WordTrace tailWord_7266109 prefixEnd_7266109 3731006404960017048821279 := by
  unfold tailWord_7266109
  simp only [CollatzResearch.WordTrace]
  refine ⟨265016767233135520465025381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176677844822090346976683587 265016767233135520465025381)
  ·
    refine ⟨49690643856212910087192259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265016767233135520465025381 49690643856212910087192259)
    ·
      refine ⟨74535965784319365130788389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49690643856212910087192259 74535965784319365130788389)
      ·
        refine ⟨13975493584559880962022823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74535965784319365130788389 13975493584559880962022823)
        ·
          refine ⟨20963240376839821443034235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13975493584559880962022823 20963240376839821443034235)
          ·
            refine ⟨31444860565259732164551353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20963240376839821443034235 31444860565259732164551353)
            ·
              refine ⟨23583645423944799123413515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31444860565259732164551353 23583645423944799123413515)
              ·
                refine ⟨35375468135917198685120273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23583645423944799123413515 35375468135917198685120273)
                ·
                  refine ⟨26531601101937899013840205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35375468135917198685120273 26531601101937899013840205)
                  ·
                    refine ⟨9949350413226712130190077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26531601101937899013840205 9949350413226712130190077)
                    ·
                      refine ⟨3731006404960017048821279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9949350413226712130190077 3731006404960017048821279)
                      ·
                        rfl

theorem cell23_7266109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_7266109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266109 prefixEnd_7266109 := by exact prefixLift 7266109
  have htrace : WordTrace (prefixWord ++ tailWord_7266109) baseStart_7266109 baseEnd_7266109 := by
    simpa [prefixWord, tailWord_7266109, baseEnd_7266109] using wordTrace_append hprefix tailTrace_7266109
  have hstable : (prefixWord ++ tailWord_7266109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266109).length < 2 ^ (prefixWord ++ tailWord_7266109).sum := by decide
  have hdescent : baseEnd_7266109 < baseStart_7266109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266110 : List Nat := [4, 2, 1, 2, 2, 2, 3, 1, 2, 2, 2]
def baseStart_7266110 : Nat := 118140960795 + 7266110 * 2 ^ 59
def prefixEnd_7266110 : Nat := 4983230072969 + 3 ^ 40 * 7266110 * 2
def baseEnd_7266110 : Nat := 3731006918440671544908775

theorem tailTrace_7266110 : CollatzResearch.WordTrace tailWord_7266110 prefixEnd_7266110 3731006918440671544908775 := by
  unfold tailWord_7266110
  simp only [CollatzResearch.WordTrace]
  refine ⟨33127100463266487204476473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176677869137421265090541189 33127100463266487204476473)
  ·
    refine ⟨24845325347449865403357355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33127100463266487204476473 24845325347449865403357355)
    ·
      refine ⟨37267988021174798105036033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24845325347449865403357355 37267988021174798105036033)
      ·
        refine ⟨27950991015881098578777025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37267988021174798105036033 27950991015881098578777025)
        ·
          refine ⟨20963243261910823934082769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27950991015881098578777025 20963243261910823934082769)
          ·
            refine ⟨15722432446433117950562077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20963243261910823934082769 15722432446433117950562077)
            ·
              refine ⟨5895912167412419231460779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15722432446433117950562077 5895912167412419231460779)
              ·
                refine ⟨8843868251118628847191169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5895912167412419231460779 8843868251118628847191169)
                ·
                  refine ⟨6632901188338971635393377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8843868251118628847191169 6632901188338971635393377)
                  ·
                    refine ⟨4974675891254228726545033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6632901188338971635393377 4974675891254228726545033)
                    ·
                      refine ⟨3731006918440671544908775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4974675891254228726545033 3731006918440671544908775)
                      ·
                        rfl

theorem cell23_7266110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_7266110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266110 prefixEnd_7266110 := by exact prefixLift 7266110
  have htrace : WordTrace (prefixWord ++ tailWord_7266110) baseStart_7266110 baseEnd_7266110 := by
    simpa [prefixWord, tailWord_7266110, baseEnd_7266110] using wordTrace_append hprefix tailTrace_7266110
  have hstable : (prefixWord ++ tailWord_7266110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266110).length < 2 ^ (prefixWord ++ tailWord_7266110).sum := by decide
  have hdescent : baseEnd_7266110 < baseStart_7266110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266239 : List Nat := [1, 1, 2, 2, 2, 1, 4, 4, 1, 1, 4]
def baseStart_7266239 : Nat := 118140960795 + 7266239 * 2 ^ 59
def prefixEnd_7266239 : Nat := 4983230072969 + 3 ^ 40 * 7266239 * 2
def baseEnd_7266239 : Nat := 3731073157445101540195681

theorem tailTrace_7266239 : CollatzResearch.WordTrace tailWord_7266239 prefixEnd_7266239 3731073157445101540195681 := by
  unfold tailWord_7266239
  simp only [CollatzResearch.WordTrace]
  refine ⟨265021508722664552667257771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176681005815109701778171847 265021508722664552667257771)
  ·
    refine ⟨397532263083996829000886657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265021508722664552667257771 397532263083996829000886657)
    ·
      refine ⟨298149197312997621750664993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397532263083996829000886657 298149197312997621750664993)
      ·
        refine ⟨223611897984748216312998745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298149197312997621750664993 223611897984748216312998745)
        ·
          refine ⟨167708923488561162234749059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223611897984748216312998745 167708923488561162234749059)
          ·
            refine ⟨251563385232841743352123589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167708923488561162234749059 251563385232841743352123589)
            ·
              refine ⟨47168134731157826878523173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 251563385232841743352123589 47168134731157826878523173)
              ·
                refine ⟨8844025262092092539723095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47168134731157826878523173 8844025262092092539723095)
                ·
                  refine ⟨13266037893138138809584643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8844025262092092539723095 13266037893138138809584643)
                  ·
                    refine ⟨19899056839707208214376965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13266037893138138809584643 19899056839707208214376965)
                    ·
                      refine ⟨3731073157445101540195681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19899056839707208214376965 3731073157445101540195681)
                      ·
                        rfl

theorem cell23_7266239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 1, 4].length) (baseStart_7266239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266239 prefixEnd_7266239 := by exact prefixLift 7266239
  have htrace : WordTrace (prefixWord ++ tailWord_7266239) baseStart_7266239 baseEnd_7266239 := by
    simpa [prefixWord, tailWord_7266239, baseEnd_7266239] using wordTrace_append hprefix tailTrace_7266239
  have hstable : (prefixWord ++ tailWord_7266239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266239).length < 2 ^ (prefixWord ++ tailWord_7266239).sum := by decide
  have hdescent : baseEnd_7266239 < baseStart_7266239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266256 : List Nat := [2, 1, 1, 1, 1, 2, 8, 1, 1, 1, 4]
def baseStart_7266256 : Nat := 118140960795 + 7266256 * 2 ^ 59
def prefixEnd_7266256 : Nat := 4983230072969 + 3 ^ 40 * 7266256 * 2
def baseEnd_7266256 : Nat := 3731081886616227973683103

theorem tailTrace_7266256 : CollatzResearch.WordTrace tailWord_7266256 prefixEnd_7266256 3731081886616227973683103 := by
  unfold tailWord_7266256
  simp only [CollatzResearch.WordTrace]
  refine ⟨132511064381801482285313311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176681419175735309713751081 132511064381801482285313311)
  ·
    refine ⟨198766596572702223427969967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132511064381801482285313311 198766596572702223427969967)
    ·
      refine ⟨298149894859053335141954951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198766596572702223427969967 298149894859053335141954951)
      ·
        refine ⟨447224842288580002712932427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298149894859053335141954951 447224842288580002712932427)
        ·
          refine ⟨670837263432870004069398641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447224842288580002712932427 670837263432870004069398641)
          ·
            refine ⟨503127947574652503052048981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 670837263432870004069398641 503127947574652503052048981)
            ·
              refine ⟨5896030635640459020141199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 503127947574652503052048981 5896030635640459020141199)
              ·
                refine ⟨8844045953460688530211799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5896030635640459020141199 8844045953460688530211799)
                ·
                  refine ⟨13266068930191032795317699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8844045953460688530211799 13266068930191032795317699)
                  ·
                    refine ⟨19899103395286549192976549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13266068930191032795317699 19899103395286549192976549)
                    ·
                      refine ⟨3731081886616227973683103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19899103395286549192976549 3731081886616227973683103)
                      ·
                        rfl

theorem cell23_7266256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 1, 1, 4].length) (baseStart_7266256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266256 prefixEnd_7266256 := by exact prefixLift 7266256
  have htrace : WordTrace (prefixWord ++ tailWord_7266256) baseStart_7266256 baseEnd_7266256 := by
    simpa [prefixWord, tailWord_7266256, baseEnd_7266256] using wordTrace_append hprefix tailTrace_7266256
  have hstable : (prefixWord ++ tailWord_7266256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266256).length < 2 ^ (prefixWord ++ tailWord_7266256).sum := by decide
  have hdescent : baseEnd_7266256 < baseStart_7266256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266266 : List Nat := [3, 1, 1, 2, 5, 1, 1, 1, 4, 4]
def baseStart_7266266 : Nat := 118140960795 + 7266266 * 2 ^ 59
def prefixEnd_7266266 : Nat := 4983230072969 + 3 ^ 40 * 7266266 * 2
def baseEnd_7266266 : Nat := 1243695673807590978186019

theorem tailTrace_7266266 : CollatzResearch.WordTrace tailWord_7266266 prefixEnd_7266266 1243695673807590978186019 := by
  unfold tailWord_7266266
  simp only [CollatzResearch.WordTrace]
  refine ⟨66255623373391684069622663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176681662329044490852327101 66255623373391684069622663)
  ·
    refine ⟨99383435060087526104433995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66255623373391684069622663 99383435060087526104433995)
    ·
      refine ⟨149075152590131289156650993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99383435060087526104433995 149075152590131289156650993)
      ·
        refine ⟨111806364442598466867488245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149075152590131289156650993 111806364442598466867488245)
        ·
          refine ⟨10481846666493606268827023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111806364442598466867488245 10481846666493606268827023)
          ·
            refine ⟨15722769999740409403240535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10481846666493606268827023 15722769999740409403240535)
            ·
              refine ⟨23584154999610614104860803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15722769999740409403240535 23584154999610614104860803)
              ·
                refine ⟨35376232499415921157291205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23584154999610614104860803 35376232499415921157291205)
                ·
                  refine ⟨6633043593640485216992101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35376232499415921157291205 6633043593640485216992101)
                  ·
                    refine ⟨1243695673807590978186019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6633043593640485216992101 1243695673807590978186019)
                    ·
                      rfl

theorem cell23_7266266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 4, 4].length) (baseStart_7266266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266266 prefixEnd_7266266 := by exact prefixLift 7266266
  have htrace : WordTrace (prefixWord ++ tailWord_7266266) baseStart_7266266 baseEnd_7266266 := by
    simpa [prefixWord, tailWord_7266266, baseEnd_7266266] using wordTrace_append hprefix tailTrace_7266266
  have hstable : (prefixWord ++ tailWord_7266266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266266).length < 2 ^ (prefixWord ++ tailWord_7266266).sum := by decide
  have hdescent : baseEnd_7266266 < baseStart_7266266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266286 : List Nat := [4, 1, 2, 1, 3, 1, 3, 1, 1, 2, 4]
def baseStart_7266286 : Nat := 118140960795 + 7266286 * 2 ^ 59
def prefixEnd_7266286 : Nat := 4983230072969 + 3 ^ 40 * 7266286 * 2
def baseEnd_7266286 : Nat := 3731097291035862856307965

theorem tailTrace_7266286 : CollatzResearch.WordTrace tailWord_7266286 prefixEnd_7266286 3731097291035862856307965 := by
  unfold tailWord_7266286
  simp only [CollatzResearch.WordTrace]
  refine ⟨33127902869186784961777339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176682148635662853129479141 33127902869186784961777339)
  ·
    refine ⟨49691854303780177442666009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33127902869186784961777339 49691854303780177442666009)
    ·
      refine ⟨37268890727835133081999507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49691854303780177442666009 37268890727835133081999507)
      ·
        refine ⟨55903336091752699622999261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37268890727835133081999507 55903336091752699622999261)
        ·
          refine ⟨20963751034407262358624723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55903336091752699622999261 20963751034407262358624723)
          ·
            refine ⟨31445626551610893537937085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20963751034407262358624723 31445626551610893537937085)
            ·
              refine ⟨11792109956854085076726407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31445626551610893537937085 11792109956854085076726407)
              ·
                refine ⟨17688164935281127615089611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11792109956854085076726407 17688164935281127615089611)
                ·
                  refine ⟨26532247402921691422634417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17688164935281127615089611 26532247402921691422634417)
                  ·
                    refine ⟨19899185552191268566975813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26532247402921691422634417 19899185552191268566975813)
                    ·
                      refine ⟨3731097291035862856307965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19899185552191268566975813 3731097291035862856307965)
                      ·
                        rfl

theorem cell23_7266286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_7266286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266286 prefixEnd_7266286 := by exact prefixLift 7266286
  have htrace : WordTrace (prefixWord ++ tailWord_7266286) baseStart_7266286 baseEnd_7266286 := by
    simpa [prefixWord, tailWord_7266286, baseEnd_7266286] using wordTrace_append hprefix tailTrace_7266286
  have hstable : (prefixWord ++ tailWord_7266286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266286).length < 2 ^ (prefixWord ++ tailWord_7266286).sum := by decide
  have hdescent : baseEnd_7266286 < baseStart_7266286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266324 : List Nat := [2, 4, 3, 2, 1, 2, 1, 1, 3, 2, 2]
def baseStart_7266324 : Nat := 118140960795 + 7266324 * 2 ^ 59
def prefixEnd_7266324 : Nat := 4983230072969 + 3 ^ 40 * 7266324 * 2
def baseEnd_7266324 : Nat := 3731116803300733707632791

theorem tailTrace_7266324 : CollatzResearch.WordTrace tailWord_7266324 prefixEnd_7266324 3731116803300733707632791 := by
  unfold tailWord_7266324
  simp only [CollatzResearch.WordTrace]
  refine ⟨132512304463678306092051013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176683072618237741456068017 132512304463678306092051013)
  ·
    refine ⟨24846057086939682392259565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132512304463678306092051013 24846057086939682392259565)
    ·
      refine ⟨9317271407602380897097337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24846057086939682392259565 9317271407602380897097337)
      ·
        refine ⟨6987953555701785672823003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9317271407602380897097337 6987953555701785672823003)
        ·
          refine ⟨10481930333552678509234505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6987953555701785672823003 10481930333552678509234505)
          ·
            refine ⟨7861447750164508881925879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10481930333552678509234505 7861447750164508881925879)
            ·
              refine ⟨11792171625246763322888819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7861447750164508881925879 11792171625246763322888819)
              ·
                refine ⟨17688257437870144984333229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11792171625246763322888819 17688257437870144984333229)
                ·
                  refine ⟨6633096539201304369124961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17688257437870144984333229 6633096539201304369124961)
                  ·
                    refine ⟨4974822404400978276843721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6633096539201304369124961 4974822404400978276843721)
                    ·
                      refine ⟨3731116803300733707632791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4974822404400978276843721 3731116803300733707632791)
                      ·
                        rfl

theorem cell23_7266324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_7266324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266324 prefixEnd_7266324 := by exact prefixLift 7266324
  have htrace : WordTrace (prefixWord ++ tailWord_7266324) baseStart_7266324 baseEnd_7266324 := by
    simpa [prefixWord, tailWord_7266324, baseEnd_7266324] using wordTrace_append hprefix tailTrace_7266324
  have hstable : (prefixWord ++ tailWord_7266324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266324).length < 2 ^ (prefixWord ++ tailWord_7266324).sum := by decide
  have hdescent : baseEnd_7266324 < baseStart_7266324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266340 : List Nat := [2, 3, 1, 4, 2, 1, 1, 3, 2, 1, 3]
def baseStart_7266340 : Nat := 118140960795 + 7266340 * 2 ^ 59
def prefixEnd_7266340 : Nat := 4983230072969 + 3 ^ 40 * 7266340 * 2
def baseEnd_7266340 : Nat := 3731125018991205645032717

theorem tailTrace_7266340 : CollatzResearch.WordTrace tailWord_7266340 prefixEnd_7266340 3731125018991205645032717 := by
  unfold tailWord_7266340
  simp only [CollatzResearch.WordTrace]
  refine ⟨132512596247649323458342237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176683461663532431277789649 132512596247649323458342237)
  ·
    refine ⟨49692223592868496296878339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132512596247649323458342237 49692223592868496296878339)
    ·
      refine ⟨74538335389302744445317509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49692223592868496296878339 74538335389302744445317509)
      ·
        refine ⟨13975937885494264583497033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74538335389302744445317509 13975937885494264583497033)
        ·
          refine ⟨10481953414120698437622775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13975937885494264583497033 10481953414120698437622775)
          ·
            refine ⟨15722930121181047656434163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10481953414120698437622775 15722930121181047656434163)
            ·
              refine ⟨23584395181771571484651245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15722930121181047656434163 23584395181771571484651245)
              ·
                refine ⟨8844148193164339306744217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23584395181771571484651245 8844148193164339306744217)
                ·
                  refine ⟨6633111144873254480058163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8844148193164339306744217 6633111144873254480058163)
                  ·
                    refine ⟨9949666717309881720087245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6633111144873254480058163 9949666717309881720087245)
                    ·
                      refine ⟨3731125018991205645032717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9949666717309881720087245 3731125018991205645032717)
                      ·
                        rfl

theorem cell23_7266340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_7266340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266340 prefixEnd_7266340 := by exact prefixLift 7266340
  have htrace : WordTrace (prefixWord ++ tailWord_7266340) baseStart_7266340 baseEnd_7266340 := by
    simpa [prefixWord, tailWord_7266340, baseEnd_7266340] using wordTrace_append hprefix tailTrace_7266340
  have hstable : (prefixWord ++ tailWord_7266340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266340).length < 2 ^ (prefixWord ++ tailWord_7266340).sum := by decide
  have hdescent : baseEnd_7266340 < baseStart_7266340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266350 : List Nat := [4, 1, 3, 1, 1, 2, 3, 2, 1, 3, 2]
def baseStart_7266350 : Nat := 118140960795 + 7266350 * 2 ^ 59
def prefixEnd_7266350 : Nat := 4983230072969 + 3 ^ 40 * 7266350 * 2
def baseEnd_7266350 : Nat := 3731130153797750605907671

theorem tailTrace_7266350 : CollatzResearch.WordTrace tailWord_7266350 prefixEnd_7266350 3731130153797750605907671 := by
  unfold tailWord_7266350
  simp only [CollatzResearch.WordTrace]
  refine ⟨33128194653157802328068563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176683704816841612416365669 33128194653157802328068563)
  ·
    refine ⟨49692291979736703492102845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33128194653157802328068563 49692291979736703492102845)
    ·
      refine ⟨18634609492401263809538567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49692291979736703492102845 18634609492401263809538567)
      ·
        refine ⟨27951914238601895714307851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18634609492401263809538567 27951914238601895714307851)
        ·
          refine ⟨41927871357902843571461777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27951914238601895714307851 41927871357902843571461777)
          ·
            refine ⟨31445903518427132678596333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41927871357902843571461777 31445903518427132678596333)
            ·
              refine ⟨11792213819410174754473625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31445903518427132678596333 11792213819410174754473625)
              ·
                refine ⟨8844160364557631065855219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11792213819410174754473625 8844160364557631065855219)
                ·
                  refine ⟨13266240546836446598782829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8844160364557631065855219 13266240546836446598782829)
                  ·
                    refine ⟨4974840205063667474543561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13266240546836446598782829 4974840205063667474543561)
                    ·
                      refine ⟨3731130153797750605907671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4974840205063667474543561 3731130153797750605907671)
                      ·
                        rfl

theorem cell23_7266350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_7266350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266350 prefixEnd_7266350 := by exact prefixLift 7266350
  have htrace : WordTrace (prefixWord ++ tailWord_7266350) baseStart_7266350 baseEnd_7266350 := by
    simpa [prefixWord, tailWord_7266350, baseEnd_7266350] using wordTrace_append hprefix tailTrace_7266350
  have hstable : (prefixWord ++ tailWord_7266350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266350).length < 2 ^ (prefixWord ++ tailWord_7266350).sum := by decide
  have hdescent : baseEnd_7266350 < baseStart_7266350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266379 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 4, 3, 3]
def baseStart_7266379 : Nat := 118140960795 + 7266379 * 2 ^ 59
def prefixEnd_7266379 : Nat := 4983230072969 + 3 ^ 40 * 7266379 * 2
def baseEnd_7266379 : Nat := 3731145044736730992445037

theorem tailTrace_7266379 : CollatzResearch.WordTrace tailWord_7266379 prefixEnd_7266379 3731145044736730992445037 := by
  unfold tailWord_7266379
  simp only [CollatzResearch.WordTrace]
  refine ⟨265026614942157356577354191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176684409961438237718236127 265026614942157356577354191)
  ·
    refine ⟨397539922413236034866031287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265026614942157356577354191 397539922413236034866031287)
    ·
      refine ⟨596309883619854052299046931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397539922413236034866031287 596309883619854052299046931)
      ·
        refine ⟨894464825429781078448570397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596309883619854052299046931 894464825429781078448570397)
        ·
          refine ⟨335424309536167904418213899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 894464825429781078448570397 335424309536167904418213899)
          ·
            refine ⟨503136464304251856627320849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335424309536167904418213899 503136464304251856627320849)
            ·
              refine ⟨377352348228188892470490637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503136464304251856627320849 377352348228188892470490637)
              ·
                refine ⟨141507130585570834676433989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 377352348228188892470490637 141507130585570834676433989)
                ·
                  refine ⟨26532586984794531501831373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141507130585570834676433989 26532586984794531501831373)
                  ·
                    refine ⟨9949720119297949313186765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26532586984794531501831373 9949720119297949313186765)
                    ·
                      refine ⟨3731145044736730992445037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9949720119297949313186765 3731145044736730992445037)
                      ·
                        rfl

theorem cell23_7266379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 3, 3].length) (baseStart_7266379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266379 prefixEnd_7266379 := by exact prefixLift 7266379
  have htrace : WordTrace (prefixWord ++ tailWord_7266379) baseStart_7266379 baseEnd_7266379 := by
    simpa [prefixWord, tailWord_7266379, baseEnd_7266379] using wordTrace_append hprefix tailTrace_7266379
  have hstable : (prefixWord ++ tailWord_7266379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266379).length < 2 ^ (prefixWord ++ tailWord_7266379).sum := by decide
  have hdescent : baseEnd_7266379 < baseStart_7266379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266396 : List Nat := [2, 2, 4, 1, 1, 2, 1, 1, 1, 5, 3]
def baseStart_7266396 : Nat := 118140960795 + 7266396 * 2 ^ 59
def prefixEnd_7266396 : Nat := 4983230072969 + 3 ^ 40 * 7266396 * 2
def baseEnd_7266396 : Nat := 3731153773907857425932459

theorem tailTrace_7266396 : CollatzResearch.WordTrace tailWord_7266396 prefixEnd_7266396 3731153773907857425932459 := by
  unfold tailWord_7266396
  simp only [CollatzResearch.WordTrace]
  refine ⟨132513617491547884240361521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176684823322063845653815361 132513617491547884240361521)
  ·
    refine ⟨99385213118660913180271141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132513617491547884240361521 99385213118660913180271141)
    ·
      refine ⟨18634727459748921221300839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99385213118660913180271141 18634727459748921221300839)
      ·
        refine ⟨27952091189623381831951259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18634727459748921221300839 27952091189623381831951259)
        ·
          refine ⟨41928136784435072747926889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27952091189623381831951259 41928136784435072747926889)
          ·
            refine ⟨31446102588326304560945167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41928136784435072747926889 31446102588326304560945167)
            ·
              refine ⟨47169153882489456841417751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31446102588326304560945167 47169153882489456841417751)
              ·
                refine ⟨70753730823734185262126627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47169153882489456841417751 70753730823734185262126627)
                ·
                  refine ⟨106130596235601277893189941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70753730823734185262126627 106130596235601277893189941)
                  ·
                    refine ⟨9949743397087619802486557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 106130596235601277893189941 9949743397087619802486557)
                    ·
                      refine ⟨3731153773907857425932459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9949743397087619802486557 3731153773907857425932459)
                      ·
                        rfl

theorem cell23_7266396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_7266396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266396 prefixEnd_7266396 := by exact prefixLift 7266396
  have htrace : WordTrace (prefixWord ++ tailWord_7266396) baseStart_7266396 baseEnd_7266396 := by
    simpa [prefixWord, tailWord_7266396, baseEnd_7266396] using wordTrace_append hprefix tailTrace_7266396
  have hstable : (prefixWord ++ tailWord_7266396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266396).length < 2 ^ (prefixWord ++ tailWord_7266396).sum := by decide
  have hdescent : baseEnd_7266396 < baseStart_7266396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266397 : List Nat := [1, 4, 4, 1, 1, 1, 2, 3, 2, 2, 2]
def baseStart_7266397 : Nat := 118140960795 + 7266397 * 2 ^ 59
def prefixEnd_7266397 : Nat := 4983230072969 + 3 ^ 40 * 7266397 * 2
def baseEnd_7266397 : Nat := 3731154287388511922019955

theorem tailTrace_7266397 : CollatzResearch.WordTrace tailWord_7266397 prefixEnd_7266397 3731154287388511922019955 := by
  unfold tailWord_7266397
  simp only [CollatzResearch.WordTrace]
  refine ⟨265027271456092145651509445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176684847637394763767672963 265027271456092145651509445)
  ·
    refine ⟨49692613398017277309658021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265027271456092145651509445 49692613398017277309658021)
    ·
      refine ⟨9317365012128239495560879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49692613398017277309658021 9317365012128239495560879)
      ·
        refine ⟨13976047518192359243341319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9317365012128239495560879 13976047518192359243341319)
        ·
          refine ⟨20964071277288538865011979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13976047518192359243341319 20964071277288538865011979)
          ·
            refine ⟨31446106915932808297517969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20964071277288538865011979 31446106915932808297517969)
            ·
              refine ⟨23584580186949606223138477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31446106915932808297517969 23584580186949606223138477)
              ·
                refine ⟨8844217570106102333676929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23584580186949606223138477 8844217570106102333676929)
                ·
                  refine ⟨6633163177579576750257697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8844217570106102333676929 6633163177579576750257697)
                  ·
                    refine ⟨4974872383184682562693273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6633163177579576750257697 4974872383184682562693273)
                    ·
                      refine ⟨3731154287388511922019955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4974872383184682562693273 3731154287388511922019955)
                      ·
                        rfl

theorem cell23_7266397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_7266397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266397 prefixEnd_7266397 := by exact prefixLift 7266397
  have htrace : WordTrace (prefixWord ++ tailWord_7266397) baseStart_7266397 baseEnd_7266397 := by
    simpa [prefixWord, tailWord_7266397, baseEnd_7266397] using wordTrace_append hprefix tailTrace_7266397
  have hstable : (prefixWord ++ tailWord_7266397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266397).length < 2 ^ (prefixWord ++ tailWord_7266397).sum := by decide
  have hdescent : baseEnd_7266397 < baseStart_7266397 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266416 : List Nat := [2, 1, 1, 1, 5, 2, 3, 1, 2, 5]
def baseStart_7266416 : Nat := 118140960795 + 7266416 * 2 ^ 59
def prefixEnd_7266416 : Nat := 4983230072969 + 3 ^ 40 * 7266416 * 2
def baseEnd_7266416 : Nat := 1243721347840315782560789

theorem tailTrace_7266416 : CollatzResearch.WordTrace tailWord_7266416 prefixEnd_7266416 1243721347840315782560789 := by
  unfold tailWord_7266416
  simp only [CollatzResearch.WordTrace]
  refine ⟨132513982221511655948225551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176685309628682207930967401 132513982221511655948225551)
  ·
    refine ⟨198770973332267483922338327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132513982221511655948225551 198770973332267483922338327)
    ·
      refine ⟨298156459998401225883507491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198770973332267483922338327 298156459998401225883507491)
      ·
        refine ⟨447234689997601838825261237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298156459998401225883507491 447234689997601838825261237)
        ·
          refine ⟨41928252187275172389868241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 447234689997601838825261237 41928252187275172389868241)
          ·
            refine ⟨31446189140456379292401181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41928252187275172389868241 31446189140456379292401181)
            ·
              refine ⟨11792320927671142234650443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31446189140456379292401181 11792320927671142234650443)
              ·
                refine ⟨17688481391506713351975665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11792320927671142234650443 17688481391506713351975665)
                ·
                  refine ⟨13266361043630035013981749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17688481391506713351975665 13266361043630035013981749)
                  ·
                    refine ⟨1243721347840315782560789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13266361043630035013981749 1243721347840315782560789)
                    ·
                      rfl

theorem cell23_7266416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 2, 5].length) (baseStart_7266416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266416 prefixEnd_7266416 := by exact prefixLift 7266416
  have htrace : WordTrace (prefixWord ++ tailWord_7266416) baseStart_7266416 baseEnd_7266416 := by
    simpa [prefixWord, tailWord_7266416, baseEnd_7266416] using wordTrace_append hprefix tailTrace_7266416
  have hstable : (prefixWord ++ tailWord_7266416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266416).length < 2 ^ (prefixWord ++ tailWord_7266416).sum := by decide
  have hdescent : baseEnd_7266416 < baseStart_7266416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266436 : List Nat := [2, 3, 2, 1, 2, 1, 2, 1, 4, 1, 4]
def baseStart_7266436 : Nat := 118140960795 + 7266436 * 2 ^ 59
def prefixEnd_7266436 : Nat := 4983230072969 + 3 ^ 40 * 7266436 * 2
def baseEnd_7266436 : Nat := 3731174313134037269432275

theorem tailTrace_7266436 : CollatzResearch.WordTrace tailWord_7266436 prefixEnd_7266436 3731174313134037269432275 := by
  unfold tailWord_7266436
  simp only [CollatzResearch.WordTrace]
  refine ⟨132514346951475427656089581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176685795935300570208119441 132514346951475427656089581)
  ·
    refine ⟨49692880106803285371033593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132514346951475427656089581 49692880106803285371033593)
    ·
      refine ⟨37269660080102464028275195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49692880106803285371033593 37269660080102464028275195)
      ·
        refine ⟨55904490120153696042412793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37269660080102464028275195 55904490120153696042412793)
        ·
          refine ⟨41928367590115272031809595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55904490120153696042412793 41928367590115272031809595)
          ·
            refine ⟨62892551385172908047714393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41928367590115272031809595 62892551385172908047714393)
            ·
              refine ⟨47169413538879681035785795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62892551385172908047714393 47169413538879681035785795)
              ·
                refine ⟨70754120308319521553678693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47169413538879681035785795 70754120308319521553678693)
                ·
                  refine ⟨13266397557809910291314755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70754120308319521553678693 13266397557809910291314755)
                  ·
                    refine ⟨19899596336714865436972133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13266397557809910291314755 19899596336714865436972133)
                    ·
                      refine ⟨3731174313134037269432275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19899596336714865436972133 3731174313134037269432275)
                      ·
                        rfl

theorem cell23_7266436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_7266436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266436 prefixEnd_7266436 := by exact prefixLift 7266436
  have htrace : WordTrace (prefixWord ++ tailWord_7266436) baseStart_7266436 baseEnd_7266436 := by
    simpa [prefixWord, tailWord_7266436, baseEnd_7266436] using wordTrace_append hprefix tailTrace_7266436
  have hstable : (prefixWord ++ tailWord_7266436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266436).length < 2 ^ (prefixWord ++ tailWord_7266436).sum := by decide
  have hdescent : baseEnd_7266436 < baseStart_7266436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266439 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 5]
def baseStart_7266439 : Nat := 118140960795 + 7266439 * 2 ^ 59
def prefixEnd_7266439 : Nat := 4983230072969 + 3 ^ 40 * 7266439 * 2
def baseEnd_7266439 : Nat := 3731175853576000757694761

theorem tailTrace_7266439 : CollatzResearch.WordTrace tailWord_7266439 prefixEnd_7266439 3731175853576000757694761 := by
  unfold tailWord_7266439
  simp only [CollatzResearch.WordTrace]
  refine ⟨265028803321939986824538371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176685868881293324549692247 265028803321939986824538371)
  ·
    refine ⟨397543204982909980236807557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265028803321939986824538371 397543204982909980236807557)
    ·
      refine ⟨74539350934295621294401417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 397543204982909980236807557 74539350934295621294401417)
      ·
        refine ⟨55904513200721715970801063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74539350934295621294401417 55904513200721715970801063)
        ·
          refine ⟨83856769801082573956201595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55904513200721715970801063 83856769801082573956201595)
          ·
            refine ⟨125785154701623860934302393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83856769801082573956201595 125785154701623860934302393)
            ·
              refine ⟨94338866026217895700726795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125785154701623860934302393 94338866026217895700726795)
              ·
                refine ⟨141508299039326843551090193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94338866026217895700726795 141508299039326843551090193)
                ·
                  refine ⟨106131224279495132663317645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141508299039326843551090193 106131224279495132663317645)
                  ·
                    refine ⟨39799209104810674748744117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 106131224279495132663317645 39799209104810674748744117)
                    ·
                      refine ⟨3731175853576000757694761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39799209104810674748744117 3731175853576000757694761)
                      ·
                        rfl

theorem cell23_7266439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_7266439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266439 prefixEnd_7266439 := by exact prefixLift 7266439
  have htrace : WordTrace (prefixWord ++ tailWord_7266439) baseStart_7266439 baseEnd_7266439 := by
    simpa [prefixWord, tailWord_7266439, baseEnd_7266439] using wordTrace_append hprefix tailTrace_7266439
  have hstable : (prefixWord ++ tailWord_7266439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266439).length < 2 ^ (prefixWord ++ tailWord_7266439).sum := by decide
  have hdescent : baseEnd_7266439 < baseStart_7266439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266463 : List Nat := [1, 1, 2, 6, 1, 1, 2, 2, 3, 4]
def baseStart_7266463 : Nat := 118140960795 + 7266463 * 2 ^ 59
def prefixEnd_7266463 : Nat := 4983230072969 + 3 ^ 40 * 7266463 * 2
def baseEnd_7266463 : Nat := 1243729392370569554598217

theorem tailTrace_7266463 : CollatzResearch.WordTrace tailWord_7266463 prefixEnd_7266463 1243729392370569554598217 := by
  unfold tailWord_7266463
  simp only [CollatzResearch.WordTrace]
  refine ⟨265029678673853038923412043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176686452449235359282274695 265029678673853038923412043)
  ·
    refine ⟨397544518010779558385118065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265029678673853038923412043 397544518010779558385118065)
    ·
      refine ⟨298158388508084668788838549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397544518010779558385118065 298158388508084668788838549)
      ·
        refine ⟨13976174461316468849476807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 298158388508084668788838549 13976174461316468849476807)
        ·
          refine ⟨20964261691974703274215211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13976174461316468849476807 20964261691974703274215211)
          ·
            refine ⟨31446392537962054911322817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20964261691974703274215211 31446392537962054911322817)
            ·
              refine ⟨23584794403471541183492113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31446392537962054911322817 23584794403471541183492113)
              ·
                refine ⟨17688595802603655887619085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23584794403471541183492113 17688595802603655887619085)
                ·
                  refine ⟨6633223425976370957857157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17688595802603655887619085 6633223425976370957857157)
                  ·
                    refine ⟨1243729392370569554598217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6633223425976370957857157 1243729392370569554598217)
                    ·
                      rfl

theorem cell23_7266463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 3, 4].length) (baseStart_7266463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266463 prefixEnd_7266463 := by exact prefixLift 7266463
  have htrace : WordTrace (prefixWord ++ tailWord_7266463) baseStart_7266463 baseEnd_7266463 := by
    simpa [prefixWord, tailWord_7266463, baseEnd_7266463] using wordTrace_append hprefix tailTrace_7266463
  have hstable : (prefixWord ++ tailWord_7266463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266463).length < 2 ^ (prefixWord ++ tailWord_7266463).sum := by decide
  have hdescent : baseEnd_7266463 < baseStart_7266463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266497 : List Nat := [1, 2, 6, 1, 2, 2, 1, 1, 3, 4]
def baseStart_7266497 : Nat := 118140960795 + 7266497 * 2 ^ 59
def prefixEnd_7266497 : Nat := 4983230072969 + 3 ^ 40 * 7266497 * 2
def baseEnd_7266497 : Nat := 1243735211817987176923165

theorem tailTrace_7266497 : CollatzResearch.WordTrace tailWord_7266497 prefixEnd_7266497 1243735211817987176923165 := by
  unfold tailWord_7266497
  simp only [CollatzResearch.WordTrace]
  refine ⟨265030918755729862730149745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176687279170486575153433163 265030918755729862730149745)
  ·
    refine ⟨198773189066797397047612309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265030918755729862730149745 198773189066797397047612309)
    ·
      refine ⟨9317493237506127986606827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 198773189066797397047612309 9317493237506127986606827)
      ·
        refine ⟨13976239856259191979910241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9317493237506127986606827 13976239856259191979910241)
        ·
          refine ⟨10482179892194393984932681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13976239856259191979910241 10482179892194393984932681)
          ·
            refine ⟨7861634919145795488699511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10482179892194393984932681 7861634919145795488699511)
            ·
              refine ⟨11792452378718693233049267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7861634919145795488699511 11792452378718693233049267)
              ·
                refine ⟨17688678568078039849573901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11792452378718693233049267 17688678568078039849573901)
                ·
                  refine ⟨6633254463029264943590213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17688678568078039849573901 6633254463029264943590213)
                  ·
                    refine ⟨1243735211817987176923165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6633254463029264943590213 1243735211817987176923165)
                    ·
                      rfl

theorem cell23_7266497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_7266497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266497 prefixEnd_7266497 := by exact prefixLift 7266497
  have htrace : WordTrace (prefixWord ++ tailWord_7266497) baseStart_7266497 baseEnd_7266497 := by
    simpa [prefixWord, tailWord_7266497, baseEnd_7266497] using wordTrace_append hprefix tailTrace_7266497
  have hstable : (prefixWord ++ tailWord_7266497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266497).length < 2 ^ (prefixWord ++ tailWord_7266497).sum := by decide
  have hdescent : baseEnd_7266497 < baseStart_7266497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266506 : List Nat := [3, 1, 2, 1, 3, 1, 2, 2, 3, 5]
def baseStart_7266506 : Nat := 118140960795 + 7266506 * 2 ^ 59
def prefixEnd_7266506 : Nat := 4983230072969 + 3 ^ 40 * 7266506 * 2
def baseEnd_7266506 : Nat := 1243736752259950665185651

theorem tailTrace_7266506 : CollatzResearch.WordTrace tailWord_7266506 prefixEnd_7266506 1243736752259950665185651 := by
  unfold tailWord_7266506
  simp only [CollatzResearch.WordTrace]
  refine ⟨66257811753174314316806843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176687498008464838178151581 66257811753174314316806843)
  ·
    refine ⟨99386717629761471475210265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66257811753174314316806843 99386717629761471475210265)
    ·
      refine ⟨74540038222321103606407699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99386717629761471475210265 74540038222321103606407699)
      ·
        refine ⟨111810057333481655409611549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74540038222321103606407699 111810057333481655409611549)
        ·
          refine ⟨41928771500055620778604331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111810057333481655409611549 41928771500055620778604331)
          ·
            refine ⟨62893157250083431167906497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41928771500055620778604331 62893157250083431167906497)
            ·
              refine ⟨47169867937562573375929873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62893157250083431167906497 47169867937562573375929873)
              ·
                refine ⟨35377400953171930031947405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47169867937562573375929873 35377400953171930031947405)
                ·
                  refine ⟨13266525357439473761980277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35377400953171930031947405 13266525357439473761980277)
                  ·
                    refine ⟨1243736752259950665185651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13266525357439473761980277 1243736752259950665185651)
                    ·
                      rfl

theorem cell23_7266506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_7266506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266506 prefixEnd_7266506 := by exact prefixLift 7266506
  have htrace : WordTrace (prefixWord ++ tailWord_7266506) baseStart_7266506 baseEnd_7266506 := by
    simpa [prefixWord, tailWord_7266506, baseEnd_7266506] using wordTrace_append hprefix tailTrace_7266506
  have hstable : (prefixWord ++ tailWord_7266506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266506).length < 2 ^ (prefixWord ++ tailWord_7266506).sum := by decide
  have hdescent : baseEnd_7266506 < baseStart_7266506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266510 : List Nat := [4, 1, 1, 1, 4, 3, 2, 1, 6]
def baseStart_7266510 : Nat := 118140960795 + 7266510 * 2 ^ 59
def prefixEnd_7266510 : Nat := 4983230072969 + 3 ^ 40 * 7266510 * 2
def baseEnd_7266510 : Nat := 414579145633607775545215

theorem tailTrace_7266510 : CollatzResearch.WordTrace tailWord_7266510 prefixEnd_7266510 414579145633607775545215 := by
  unfold tailWord_7266510
  simp only [CollatzResearch.WordTrace]
  refine ⟨33128924113085345743796623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176687595269788510633581989 33128924113085345743796623)
  ·
    refine ⟨49693386169628018615694935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33128924113085345743796623 49693386169628018615694935)
    ·
      refine ⟨74540079254442027923542403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49693386169628018615694935 74540079254442027923542403)
      ·
        refine ⟨111810118881663041885313605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74540079254442027923542403 111810118881663041885313605)
        ·
          refine ⟨20964397290311820353496301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111810118881663041885313605 20964397290311820353496301)
          ·
            refine ⟨7861648983866932632561113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20964397290311820353496301 7861648983866932632561113)
            ·
              refine ⟨5896236737900199474420835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7861648983866932632561113 5896236737900199474420835)
              ·
                refine ⟨8844355106850299211631253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5896236737900199474420835 8844355106850299211631253)
                ·
                  refine ⟨414579145633607775545215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8844355106850299211631253 414579145633607775545215)
                  ·
                    rfl

theorem cell23_7266510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 6].length) (baseStart_7266510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266510 prefixEnd_7266510 := by exact prefixLift 7266510
  have htrace : WordTrace (prefixWord ++ tailWord_7266510) baseStart_7266510 baseEnd_7266510 := by
    simpa [prefixWord, tailWord_7266510, baseEnd_7266510] using wordTrace_append hprefix tailTrace_7266510
  have hstable : (prefixWord ++ tailWord_7266510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266510).length < 2 ^ (prefixWord ++ tailWord_7266510).sum := by decide
  have hdescent : baseEnd_7266510 < baseStart_7266510 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266536 : List Nat := [2, 1, 4, 1, 2, 2, 1, 1, 3, 6]
def baseStart_7266536 : Nat := 118140960795 + 7266536 * 2 ^ 59
def prefixEnd_7266536 : Nat := 4983230072969 + 3 ^ 40 * 7266536 * 2
def baseEnd_7266536 : Nat := 1243741887066495626060605

theorem tailTrace_7266536 : CollatzResearch.WordTrace tailWord_7266536 prefixEnd_7266536 1243741887066495626060605 := by
  unfold tailWord_7266536
  simp only [CollatzResearch.WordTrace]
  refine ⟨132516170601294286195409731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176688227468392381593879641 132516170601294286195409731)
  ·
    refine ⟨198774255901941429293114597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132516170601294286195409731 198774255901941429293114597)
    ·
      refine ⟨37270172981614017992458987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198774255901941429293114597 37270172981614017992458987)
      ·
        refine ⟨55905259472421026988688481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37270172981614017992458987 55905259472421026988688481)
        ·
          refine ⟨41928944604315770241516361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55905259472421026988688481 41928944604315770241516361)
          ·
            refine ⟨31446708453236827681137271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41928944604315770241516361 31446708453236827681137271)
            ·
              refine ⟨47170062679855241521705907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31446708453236827681137271 47170062679855241521705907)
              ·
                refine ⟨70755094019782862282558861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47170062679855241521705907 70755094019782862282558861)
                ·
                  refine ⟨26533160257418573355959573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70755094019782862282558861 26533160257418573355959573)
                  ·
                    refine ⟨1243741887066495626060605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26533160257418573355959573 1243741887066495626060605)
                    ·
                      rfl

theorem cell23_7266536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_7266536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266536 prefixEnd_7266536 := by exact prefixLift 7266536
  have htrace : WordTrace (prefixWord ++ tailWord_7266536) baseStart_7266536 baseEnd_7266536 := by
    simpa [prefixWord, tailWord_7266536, baseEnd_7266536] using wordTrace_append hprefix tailTrace_7266536
  have hstable : (prefixWord ++ tailWord_7266536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266536).length < 2 ^ (prefixWord ++ tailWord_7266536).sum := by decide
  have hdescent : baseEnd_7266536 < baseStart_7266536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266549 : List Nat := [1, 3, 19]
def baseStart_7266549 : Nat := 118140960795 + 7266549 * 2 ^ 59
def prefixEnd_7266549 : Nat := 4983230072969 + 3 ^ 40 * 7266549 * 2
def baseEnd_7266549 : Nat := 568698725262611694455

theorem tailTrace_7266549 : CollatzResearch.WordTrace tailWord_7266549 prefixEnd_7266549 568698725262611694455 := by
  unfold tailWord_7266549
  simp only [CollatzResearch.WordTrace]
  refine ⟨265032815351541475611042701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176688543567694317074028467 265032815351541475611042701)
  ·
    refine ⟨99387305756828053354141013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265032815351541475611042701 99387305756828053354141013)
    ·
      refine ⟨568698725262611694455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 19 99387305756828053354141013 568698725262611694455)
      ·
        rfl

theorem cell23_7266549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 19].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 19].length) (baseStart_7266549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266549 prefixEnd_7266549 := by exact prefixLift 7266549
  have htrace : WordTrace (prefixWord ++ tailWord_7266549) baseStart_7266549 baseEnd_7266549 := by
    simpa [prefixWord, tailWord_7266549, baseEnd_7266549] using wordTrace_append hprefix tailTrace_7266549
  have hstable : (prefixWord ++ tailWord_7266549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266549).length < 2 ^ (prefixWord ++ tailWord_7266549).sum := by decide
  have hdescent : baseEnd_7266549 < baseStart_7266549 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266554 : List Nat := [3, 1, 1, 1, 1, 7, 2, 2, 1, 1, 3]
def baseStart_7266554 : Nat := 118140960795 + 7266554 * 2 ^ 59
def prefixEnd_7266554 : Nat := 4983230072969 + 3 ^ 40 * 7266554 * 2
def baseEnd_7266554 : Nat := 3731234903851267807756733

theorem tailTrace_7266554 : CollatzResearch.WordTrace tailWord_7266554 prefixEnd_7266554 3731234903851267807756733 := by
  unfold tailWord_7266554
  simp only [CollatzResearch.WordTrace]
  refine ⟨66258249429130840366243679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176688665144348907643316477 66258249429130840366243679)
  ·
    refine ⟨99387374143696260549365519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66258249429130840366243679 99387374143696260549365519)
    ·
      refine ⟨149081061215544390824048279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99387374143696260549365519 149081061215544390824048279)
      ·
        refine ⟨223621591823316586236072419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149081061215544390824048279 223621591823316586236072419)
        ·
          refine ⟨335432387734974879354108629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223621591823316586236072419 335432387734974879354108629)
          ·
            refine ⟨7861696587538473734861921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 335432387734974879354108629 7861696587538473734861921)
            ·
              refine ⟨5896272440653855301146441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7861696587538473734861921 5896272440653855301146441)
              ·
                refine ⟨4422204330490391475859831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5896272440653855301146441 4422204330490391475859831)
                ·
                  refine ⟨6633306495735587213789747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4422204330490391475859831 6633306495735587213789747)
                  ·
                    refine ⟨9949959743603380820684621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6633306495735587213789747 9949959743603380820684621)
                    ·
                      refine ⟨3731234903851267807756733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9949959743603380820684621 3731234903851267807756733)
                      ·
                        rfl

theorem cell23_7266554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 2, 1, 1, 3].length) (baseStart_7266554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266554 prefixEnd_7266554 := by exact prefixLift 7266554
  have htrace : WordTrace (prefixWord ++ tailWord_7266554) baseStart_7266554 baseEnd_7266554 := by
    simpa [prefixWord, tailWord_7266554, baseEnd_7266554] using wordTrace_append hprefix tailTrace_7266554
  have hstable : (prefixWord ++ tailWord_7266554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266554).length < 2 ^ (prefixWord ++ tailWord_7266554).sum := by decide
  have hdescent : baseEnd_7266554 < baseStart_7266554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266583 : List Nat := [1, 1, 3, 4, 1, 3, 3, 7]
def baseStart_7266583 : Nat := 118140960795 + 7266583 * 2 ^ 59
def prefixEnd_7266583 : Nat := 4983230072969 + 3 ^ 40 * 7266583 * 2
def baseEnd_7266583 : Nat := 138194436844083266455337

theorem tailTrace_7266583 : CollatzResearch.WordTrace tailWord_7266583 prefixEnd_7266583 138194436844083266455337 := by
  unfold tailWord_7266583
  simp only [CollatzResearch.WordTrace]
  refine ⟨265034055433418299417780403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176689370288945532945186935 265034055433418299417780403)
  ·
    refine ⟨397551083150127449126670605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265034055433418299417780403 397551083150127449126670605)
    ·
      refine ⟨149081656181297793422501477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 397551083150127449126670605 149081656181297793422501477)
      ·
        refine ⟨27952810533993336266719027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149081656181297793422501477 27952810533993336266719027)
        ·
          refine ⟨41929215800990004400078541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27952810533993336266719027 41929215800990004400078541)
          ·
            refine ⟨15723455925371251650029453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41929215800990004400078541 15723455925371251650029453)
            ·
              refine ⟨5896295972014219368761045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15723455925371251650029453 5896295972014219368761045)
              ·
                refine ⟨138194436844083266455337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5896295972014219368761045 138194436844083266455337)
                ·
                  rfl

theorem cell23_7266583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 7].length) (baseStart_7266583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266583 prefixEnd_7266583 := by exact prefixLift 7266583
  have htrace : WordTrace (prefixWord ++ tailWord_7266583) baseStart_7266583 baseEnd_7266583 := by
    simpa [prefixWord, tailWord_7266583, baseEnd_7266583] using wordTrace_append hprefix tailTrace_7266583
  have hstable : (prefixWord ++ tailWord_7266583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266583).length < 2 ^ (prefixWord ++ tailWord_7266583).sum := by decide
  have hdescent : baseEnd_7266583 < baseStart_7266583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266593 : List Nat := [1, 2, 3, 2, 1, 1, 4, 2, 1, 3, 3]
def baseStart_7266593 : Nat := 118140960795 + 7266593 * 2 ^ 59
def prefixEnd_7266593 : Nat := 4983230072969 + 3 ^ 40 * 7266593 * 2
def baseEnd_7266593 : Nat := 3731254929596793155169053

theorem tailTrace_7266593 : CollatzResearch.WordTrace tailWord_7266593 prefixEnd_7266593 3731254929596793155169053 := by
  unfold tailWord_7266593
  simp only [CollatzResearch.WordTrace]
  refine ⟨265034420163382071125644433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176689613442254714083762955 265034420163382071125644433)
  ·
    refine ⟨198775815122536553344233325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265034420163382071125644433 198775815122536553344233325)
    ·
      refine ⟨74540930670951207504087497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198775815122536553344233325 74540930670951207504087497)
      ·
        refine ⟨55905698003213405628065623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74540930670951207504087497 55905698003213405628065623)
        ·
          refine ⟨83858547004820108442098435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55905698003213405628065623 83858547004820108442098435)
          ·
            refine ⟨125787820507230162663147653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83858547004820108442098435 125787820507230162663147653)
            ·
              refine ⟨23585216345105655499340185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125787820507230162663147653 23585216345105655499340185)
              ·
                refine ⟨17688912258829241624505139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23585216345105655499340185 17688912258829241624505139)
                ·
                  refine ⟨26533368388243862436757709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17688912258829241624505139 26533368388243862436757709)
                  ·
                    refine ⟨9950013145591448413784141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26533368388243862436757709 9950013145591448413784141)
                    ·
                      refine ⟨3731254929596793155169053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9950013145591448413784141 3731254929596793155169053)
                      ·
                        rfl

theorem cell23_7266593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_7266593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266593 prefixEnd_7266593 := by exact prefixLift 7266593
  have htrace : WordTrace (prefixWord ++ tailWord_7266593) baseStart_7266593 baseEnd_7266593 := by
    simpa [prefixWord, tailWord_7266593, baseEnd_7266593] using wordTrace_append hprefix tailTrace_7266593
  have hstable : (prefixWord ++ tailWord_7266593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266593).length < 2 ^ (prefixWord ++ tailWord_7266593).sum := by decide
  have hdescent : baseEnd_7266593 < baseStart_7266593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266594 : List Nat := [3, 3, 1, 1, 3, 1, 1, 5, 1, 2, 2]
def baseStart_7266594 : Nat := 118140960795 + 7266594 * 2 ^ 59
def prefixEnd_7266594 : Nat := 4983230072969 + 3 ^ 40 * 7266594 * 2
def baseEnd_7266594 : Nat := 3731255443077447651256549

theorem tailTrace_7266594 : CollatzResearch.WordTrace tailWord_7266594 prefixEnd_7266594 3731255443077447651256549 := by
  unfold tailWord_7266594
  simp only [CollatzResearch.WordTrace]
  refine ⟨66258614159094612074107709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176689637757585632197620557 66258614159094612074107709)
  ·
    refine ⟨24846980309660479527790391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66258614159094612074107709 24846980309660479527790391)
    ·
      refine ⟨37270470464490719291685587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24846980309660479527790391 37270470464490719291685587)
      ·
        refine ⟨55905705696736078937528381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37270470464490719291685587 55905705696736078937528381)
        ·
          refine ⟨20964639636276029601573143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55905705696736078937528381 20964639636276029601573143)
          ·
            refine ⟨31446959454414044402359715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20964639636276029601573143 31446959454414044402359715)
            ·
              refine ⟨47170439181621066603539573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31446959454414044402359715 47170439181621066603539573)
              ·
                refine ⟨4422228673276974994081835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47170439181621066603539573 4422228673276974994081835)
                ·
                  refine ⟨6633343009915462491122753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4422228673276974994081835 6633343009915462491122753)
                  ·
                    refine ⟨4975007257436596868342065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6633343009915462491122753 4975007257436596868342065)
                    ·
                      refine ⟨3731255443077447651256549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4975007257436596868342065 3731255443077447651256549)
                      ·
                        rfl

theorem cell23_7266594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 5, 1, 2, 2].length) (baseStart_7266594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266594 prefixEnd_7266594 := by exact prefixLift 7266594
  have htrace : WordTrace (prefixWord ++ tailWord_7266594) baseStart_7266594 baseEnd_7266594 := by
    simpa [prefixWord, tailWord_7266594, baseEnd_7266594] using wordTrace_append hprefix tailTrace_7266594
  have hstable : (prefixWord ++ tailWord_7266594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266594).length < 2 ^ (prefixWord ++ tailWord_7266594).sum := by decide
  have hdescent : baseEnd_7266594 < baseStart_7266594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266616 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 1, 5, 4]
def baseStart_7266616 : Nat := 118140960795 + 7266616 * 2 ^ 59
def prefixEnd_7266616 : Nat := 4983230072969 + 3 ^ 40 * 7266616 * 2
def baseEnd_7266616 : Nat := 3731266739651846565181447

theorem tailTrace_7266616 : CollatzResearch.WordTrace tailWord_7266616 prefixEnd_7266616 3731266739651846565181447 := by
  unfold tailWord_7266616
  simp only [CollatzResearch.WordTrace]
  refine ⟨132517629521149373026865851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176690172694865830702487801 132517629521149373026865851)
  ·
    refine ⟨198776444281724059540298777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132517629521149373026865851 198776444281724059540298777)
    ·
      refine ⟨149082333211293044655224083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198776444281724059540298777 149082333211293044655224083)
      ·
        refine ⟨223623499816939566982836125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149082333211293044655224083 223623499816939566982836125)
        ·
          refine ⟨83858812431352337618563547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223623499816939566982836125 83858812431352337618563547)
          ·
            refine ⟨125788218647028506427845321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83858812431352337618563547 125788218647028506427845321)
            ·
              refine ⟨94341163985271379820883991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125788218647028506427845321 94341163985271379820883991)
              ·
                refine ⟨141511745977907069731325987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94341163985271379820883991 141511745977907069731325987)
                ·
                  refine ⟨212267618966860604596988981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141511745977907069731325987 212267618966860604596988981)
                  ·
                    refine ⟨19900089278143181680967717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 212267618966860604596988981 19900089278143181680967717)
                    ·
                      refine ⟨3731266739651846565181447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19900089278143181680967717 3731266739651846565181447)
                      ·
                        rfl

theorem cell23_7266616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_7266616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266616 prefixEnd_7266616 := by exact prefixLift 7266616
  have htrace : WordTrace (prefixWord ++ tailWord_7266616) baseStart_7266616 baseEnd_7266616 := by
    simpa [prefixWord, tailWord_7266616, baseEnd_7266616] using wordTrace_append hprefix tailTrace_7266616
  have hstable : (prefixWord ++ tailWord_7266616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266616).length < 2 ^ (prefixWord ++ tailWord_7266616).sum := by decide
  have hdescent : baseEnd_7266616 < baseStart_7266616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266678 : List Nat := [5, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3]
def baseStart_7266678 : Nat := 118140960795 + 7266678 * 2 ^ 59
def prefixEnd_7266678 : Nat := 4983230072969 + 3 ^ 40 * 7266678 * 2
def baseEnd_7266678 : Nat := 3731298575452425322606163

theorem tailTrace_7266678 : CollatzResearch.WordTrace tailWord_7266678 prefixEnd_7266678 3731298575452425322606163 := by
  unfold tailWord_7266678
  simp only [CollatzResearch.WordTrace]
  refine ⟨16564845023004633165155543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176691680245382753761659125 16564845023004633165155543)
  ·
    refine ⟨24847267534506949747733315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16564845023004633165155543 24847267534506949747733315)
    ·
      refine ⟨37270901301760424621599973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24847267534506949747733315 37270901301760424621599973)
      ·
        refine ⟨6988293994080079616549995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37270901301760424621599973 6988293994080079616549995)
        ·
          refine ⟨10482440991120119424824993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6988293994080079616549995 10482440991120119424824993)
          ·
            refine ⟨7861830743340089568618745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10482440991120119424824993 7861830743340089568618745)
            ·
              refine ⟨5896373057505067176464059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7861830743340089568618745 5896373057505067176464059)
              ·
                refine ⟨8844559586257600764696089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5896373057505067176464059 8844559586257600764696089)
                ·
                  refine ⟨6633419689693200573522067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8844559586257600764696089 6633419689693200573522067)
                  ·
                    refine ⟨9950129534539800860283101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6633419689693200573522067 9950129534539800860283101)
                    ·
                      refine ⟨3731298575452425322606163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9950129534539800860283101 3731298575452425322606163)
                      ·
                        rfl

theorem cell23_7266678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_7266678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266678 prefixEnd_7266678 := by exact prefixLift 7266678
  have htrace : WordTrace (prefixWord ++ tailWord_7266678) baseStart_7266678 baseEnd_7266678 := by
    simpa [prefixWord, tailWord_7266678, baseEnd_7266678] using wordTrace_append hprefix tailTrace_7266678
  have hstable : (prefixWord ++ tailWord_7266678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266678).length < 2 ^ (prefixWord ++ tailWord_7266678).sum := by decide
  have hdescent : baseEnd_7266678 < baseStart_7266678 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266750 : List Nat := [4, 2, 1, 1, 1, 1, 3, 1, 5, 4]
def baseStart_7266750 : Nat := 118140960795 + 7266750 * 2 ^ 59
def prefixEnd_7266750 : Nat := 4983230072969 + 3 ^ 40 * 7266750 * 2
def baseEnd_7266750 : Nat := 1243778515353183013635277

theorem tailTrace_7266750 : CollatzResearch.WordTrace tailWord_7266750 prefixEnd_7266750 1243778515353183013635277 := by
  unfold tailWord_7266750
  simp only [CollatzResearch.WordTrace]
  refine ⟨33130018302976660867388713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176693430949208857959406469 33130018302976660867388713)
  ·
    refine ⟨24847513727232495650541535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33130018302976660867388713 24847513727232495650541535)
    ·
      refine ⟨37271270590848743475812303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24847513727232495650541535 37271270590848743475812303)
      ·
        refine ⟨55906905886273115213718455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37271270590848743475812303 55906905886273115213718455)
        ·
          refine ⟨83860358829409672820577683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55906905886273115213718455 83860358829409672820577683)
          ·
            refine ⟨125790538244114509230866525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83860358829409672820577683 125790538244114509230866525)
            ·
              refine ⟨47171451841542940961574947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125790538244114509230866525 47171451841542940961574947)
              ·
                refine ⟨70757177762314411442362421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47171451841542940961574947 70757177762314411442362421)
                ·
                  refine ⟨6633485415216976072721477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70757177762314411442362421 6633485415216976072721477)
                  ·
                    refine ⟨1243778515353183013635277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6633485415216976072721477 1243778515353183013635277)
                    ·
                      rfl

theorem cell23_7266750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_7266750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266750 prefixEnd_7266750 := by exact prefixLift 7266750
  have htrace : WordTrace (prefixWord ++ tailWord_7266750) baseStart_7266750 baseEnd_7266750 := by
    simpa [prefixWord, tailWord_7266750, baseEnd_7266750] using wordTrace_append hprefix tailTrace_7266750
  have hstable : (prefixWord ++ tailWord_7266750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266750).length < 2 ^ (prefixWord ++ tailWord_7266750).sum := by decide
  have hdescent : baseEnd_7266750 < baseStart_7266750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266760 : List Nat := [2, 1, 3, 1, 3, 3, 1, 1, 1, 4, 3]
def baseStart_7266760 : Nat := 118140960795 + 7266760 * 2 ^ 59
def prefixEnd_7266760 : Nat := 4983230072969 + 3 ^ 40 * 7266760 * 2
def baseEnd_7266760 : Nat := 3731340680866094001780785

theorem tailTrace_7266760 : CollatzResearch.WordTrace tailWord_7266760 prefixEnd_7266760 3731340680866094001780785 := by
  unfold tailWord_7266760
  simp only [CollatzResearch.WordTrace]
  refine ⟨132520255576888529323486867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176693674102518039097982489 132520255576888529323486867)
  ·
    refine ⟨198780383365332793985230301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132520255576888529323486867 198780383365332793985230301)
    ·
      refine ⟨74542643761999797744461363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198780383365332793985230301 74542643761999797744461363)
      ·
        refine ⟨111813965642999696616692045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74542643761999797744461363 111813965642999696616692045)
        ·
          refine ⟨41930237116124886231259517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111813965642999696616692045 41930237116124886231259517)
          ·
            refine ⟨15723838918546832336722319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41930237116124886231259517 15723838918546832336722319)
            ·
              refine ⟨23585758377820248505083479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15723838918546832336722319 23585758377820248505083479)
              ·
                refine ⟨35378637566730372757625219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23585758377820248505083479 35378637566730372757625219)
                ·
                  refine ⟨53067956350095559136437829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35378637566730372757625219 53067956350095559136437829)
                  ·
                    refine ⟨9950241815642917338082093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53067956350095559136437829 9950241815642917338082093)
                    ·
                      refine ⟨3731340680866094001780785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9950241815642917338082093 3731340680866094001780785)
                      ·
                        rfl

theorem cell23_7266760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_7266760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266760 prefixEnd_7266760 := by exact prefixLift 7266760
  have htrace : WordTrace (prefixWord ++ tailWord_7266760) baseStart_7266760 baseEnd_7266760 := by
    simpa [prefixWord, tailWord_7266760, baseEnd_7266760] using wordTrace_append hprefix tailTrace_7266760
  have hstable : (prefixWord ++ tailWord_7266760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266760).length < 2 ^ (prefixWord ++ tailWord_7266760).sum := by decide
  have hdescent : baseEnd_7266760 < baseStart_7266760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266783 : List Nat := [1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 6]
def baseStart_7266783 : Nat := 118140960795 + 7266783 * 2 ^ 59
def prefixEnd_7266783 : Nat := 4983230072969 + 3 ^ 40 * 7266783 * 2
def baseEnd_7266783 : Nat := 3731352490921147411793179

theorem tailTrace_7266783 : CollatzResearch.WordTrace tailWord_7266783 prefixEnd_7266783 3731352490921147411793179 := by
  unfold tailWord_7266783
  simp only [CollatzResearch.WordTrace]
  refine ⟨265041350032693733575061003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176694233355129155716707335 265041350032693733575061003)
  ·
    refine ⟨397562025049040600362591505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265041350032693733575061003 397562025049040600362591505)
    ·
      refine ⟨298171518786780450271943629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397562025049040600362591505 298171518786780450271943629)
      ·
        refine ⟨111814319545042668851978861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298171518786780450271943629 111814319545042668851978861)
        ·
          refine ⟨41930369829391000819492073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111814319545042668851978861 41930369829391000819492073)
          ·
            refine ⟨31447777372043250614619055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41930369829391000819492073 31447777372043250614619055)
            ·
              refine ⟨47171666058064875921928583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31447777372043250614619055 47171666058064875921928583)
              ·
                refine ⟨70757499087097313882892875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47171666058064875921928583 70757499087097313882892875)
                ·
                  refine ⟨106136248630645970824339313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70757499087097313882892875 106136248630645970824339313)
                  ·
                    refine ⟨79602186472984478118254485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106136248630645970824339313 79602186472984478118254485)
                    ·
                      refine ⟨3731352490921147411793179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79602186472984478118254485 3731352490921147411793179)
                      ·
                        rfl

theorem cell23_7266783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_7266783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266783 prefixEnd_7266783 := by exact prefixLift 7266783
  have htrace : WordTrace (prefixWord ++ tailWord_7266783) baseStart_7266783 baseEnd_7266783 := by
    simpa [prefixWord, tailWord_7266783, baseEnd_7266783] using wordTrace_append hprefix tailTrace_7266783
  have hstable : (prefixWord ++ tailWord_7266783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266783).length < 2 ^ (prefixWord ++ tailWord_7266783).sum := by decide
  have hdescent : baseEnd_7266783 < baseStart_7266783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266793 : List Nat := [1, 2, 1, 1, 1, 2, 1, 6, 3, 5]
def baseStart_7266793 : Nat := 118140960795 + 7266793 * 2 ^ 59
def prefixEnd_7266793 : Nat := 4983230072969 + 3 ^ 40 * 7266793 * 2
def baseEnd_7266793 : Nat := 1243785875242564124222711

theorem tailTrace_7266793 : CollatzResearch.WordTrace tailWord_7266793 prefixEnd_7266793 1243785875242564124222711 := by
  unfold tailWord_7266793
  simp only [CollatzResearch.WordTrace]
  refine ⟨265041714762657505282925033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176694476508438336855283355 265041714762657505282925033)
  ·
    refine ⟨198781286071993128962193775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265041714762657505282925033 198781286071993128962193775)
    ·
      refine ⟨298171929107989693443290663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198781286071993128962193775 298171929107989693443290663)
      ·
        refine ⟨447257893661984540164935995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298171929107989693443290663 447257893661984540164935995)
        ·
          refine ⟨670886840492976810247403993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447257893661984540164935995 670886840492976810247403993)
          ·
            refine ⟨503165130369732607685552995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 670886840492976810247403993 503165130369732607685552995)
            ·
              refine ⟨754747695554598911528329493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503165130369732607685552995 754747695554598911528329493)
              ·
                refine ⟨35378798229121823977890445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 754747695554598911528329493 35378798229121823977890445)
                ·
                  refine ⟨13267049335920683991708917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35378798229121823977890445 13267049335920683991708917)
                  ·
                    refine ⟨1243785875242564124222711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13267049335920683991708917 1243785875242564124222711)
                    ·
                      rfl

theorem cell23_7266793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 5].length) (baseStart_7266793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266793 prefixEnd_7266793 := by exact prefixLift 7266793
  have htrace : WordTrace (prefixWord ++ tailWord_7266793) baseStart_7266793 baseEnd_7266793 := by
    simpa [prefixWord, tailWord_7266793, baseEnd_7266793] using wordTrace_append hprefix tailTrace_7266793
  have hstable : (prefixWord ++ tailWord_7266793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266793).length < 2 ^ (prefixWord ++ tailWord_7266793).sum := by decide
  have hdescent : baseEnd_7266793 < baseStart_7266793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266800 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 3, 5, 2]
def baseStart_7266800 : Nat := 118140960795 + 7266800 * 2 ^ 59
def prefixEnd_7266800 : Nat := 4983230072969 + 3 ^ 40 * 7266800 * 2
def baseEnd_7266800 : Nat := 3731361220092273845280601

theorem tailTrace_7266800 : CollatzResearch.WordTrace tailWord_7266800 prefixEnd_7266800 3731361220092273845280601 := by
  unfold tailWord_7266800
  simp only [CollatzResearch.WordTrace]
  refine ⟨132520985036816072739214927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176694646715754763652286569 132520985036816072739214927)
  ·
    refine ⟨198781477555224109108822391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132520985036816072739214927 198781477555224109108822391)
    ·
      refine ⟨298172216332836163663233587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198781477555224109108822391 298172216332836163663233587)
      ·
        refine ⟨447258324499254245494850381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298172216332836163663233587 447258324499254245494850381)
        ·
          refine ⟨167721871687220342060568893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 447258324499254245494850381 167721871687220342060568893)
          ·
            refine ⟨62895701882707628272713335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167721871687220342060568893 62895701882707628272713335)
            ·
              refine ⟨94343552824061442409070003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62895701882707628272713335 94343552824061442409070003)
              ·
                refine ⟨141515329236092163613605005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94343552824061442409070003 141515329236092163613605005)
                ·
                  refine ⟨53068248463534561355101877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141515329236092163613605005 53068248463534561355101877)
                  ·
                    refine ⟨4975148293456365127040801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53068248463534561355101877 4975148293456365127040801)
                    ·
                      refine ⟨3731361220092273845280601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4975148293456365127040801 3731361220092273845280601)
                      ·
                        rfl

theorem cell23_7266800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 3, 5, 2].length) (baseStart_7266800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266800 prefixEnd_7266800 := by exact prefixLift 7266800
  have htrace : WordTrace (prefixWord ++ tailWord_7266800) baseStart_7266800 baseEnd_7266800 := by
    simpa [prefixWord, tailWord_7266800, baseEnd_7266800] using wordTrace_append hprefix tailTrace_7266800
  have hstable : (prefixWord ++ tailWord_7266800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266800).length < 2 ^ (prefixWord ++ tailWord_7266800).sum := by decide
  have hdescent : baseEnd_7266800 < baseStart_7266800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266817 : List Nat := [1, 2, 4, 1, 3, 1, 2, 1, 1, 5, 2]
def baseStart_7266817 : Nat := 118140960795 + 7266817 * 2 ^ 59
def prefixEnd_7266817 : Nat := 4983230072969 + 3 ^ 40 * 7266817 * 2
def baseEnd_7266817 : Nat := 3731369949263400278768023

theorem tailTrace_7266817 : CollatzResearch.WordTrace tailWord_7266817 prefixEnd_7266817 3731369949263400278768023 := by
  unfold tailWord_7266817
  simp only [CollatzResearch.WordTrace]
  refine ⟨265042590114570557381798705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176695060076380371587865803 265042590114570557381798705)
  ·
    refine ⟨198781942585927918036349029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265042590114570557381798705 198781942585927918036349029)
    ·
      refine ⟨37271614234861484631815443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198781942585927918036349029 37271614234861484631815443)
      ·
        refine ⟨55907421352292226947723165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37271614234861484631815443 55907421352292226947723165)
        ·
          refine ⟨20965283007109585105396187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55907421352292226947723165 20965283007109585105396187)
          ·
            refine ⟨31447924510664377658094281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20965283007109585105396187 31447924510664377658094281)
            ·
              refine ⟨23585943382998283243570711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31447924510664377658094281 23585943382998283243570711)
              ·
                refine ⟨35378915074497424865356067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23585943382998283243570711 35378915074497424865356067)
                ·
                  refine ⟨53068372611746137298034101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35378915074497424865356067 53068372611746137298034101)
                  ·
                    refine ⟨4975159932351200371690697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53068372611746137298034101 4975159932351200371690697)
                    ·
                      refine ⟨3731369949263400278768023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4975159932351200371690697 3731369949263400278768023)
                      ·
                        rfl

theorem cell23_7266817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_7266817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266817 prefixEnd_7266817 := by exact prefixLift 7266817
  have htrace : WordTrace (prefixWord ++ tailWord_7266817) baseStart_7266817 baseEnd_7266817 := by
    simpa [prefixWord, tailWord_7266817, baseEnd_7266817] using wordTrace_append hprefix tailTrace_7266817
  have hstable : (prefixWord ++ tailWord_7266817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266817).length < 2 ^ (prefixWord ++ tailWord_7266817).sum := by decide
  have hdescent : baseEnd_7266817 < baseStart_7266817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266818 : List Nat := [3, 4, 1, 2, 2, 2, 1, 3, 1, 4]
def baseStart_7266818 : Nat := 118140960795 + 7266818 * 2 ^ 59
def prefixEnd_7266818 : Nat := 4983230072969 + 3 ^ 40 * 7266818 * 2
def baseEnd_7266818 : Nat := 1243790154248018258285173

theorem tailTrace_7266818 : CollatzResearch.WordTrace tailWord_7266818 prefixEnd_7266818 1243790154248018258285173 := by
  unfold tailWord_7266818
  simp only [CollatzResearch.WordTrace]
  refine ⟨66260656646891733638146277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176695084391711289701723405 66260656646891733638146277)
  ·
    refine ⟨12423873121292200057152427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66260656646891733638146277 12423873121292200057152427)
    ·
      refine ⟨18635809681938300085728641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12423873121292200057152427 18635809681938300085728641)
      ·
        refine ⟨13976857261453725064296481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18635809681938300085728641 13976857261453725064296481)
        ·
          refine ⟨10482642946090293798222361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13976857261453725064296481 10482642946090293798222361)
          ·
            refine ⟨7861982209567720348666771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10482642946090293798222361 7861982209567720348666771)
            ·
              refine ⟨11792973314351580523000157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7861982209567720348666771 11792973314351580523000157)
              ·
                refine ⟨4422364992881842696125059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11792973314351580523000157 4422364992881842696125059)
                ·
                  refine ⟨6633547489322764044187589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4422364992881842696125059 6633547489322764044187589)
                  ·
                    refine ⟨1243790154248018258285173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6633547489322764044187589 1243790154248018258285173)
                    ·
                      rfl

theorem cell23_7266818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_7266818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266818 prefixEnd_7266818 := by exact prefixLift 7266818
  have htrace : WordTrace (prefixWord ++ tailWord_7266818) baseStart_7266818 baseEnd_7266818 := by
    simpa [prefixWord, tailWord_7266818, baseEnd_7266818] using wordTrace_append hprefix tailTrace_7266818
  have hstable : (prefixWord ++ tailWord_7266818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266818).length < 2 ^ (prefixWord ++ tailWord_7266818).sum := by decide
  have hdescent : baseEnd_7266818 < baseStart_7266818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266850 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 2, 6, 3]
def baseStart_7266850 : Nat := 118140960795 + 7266850 * 2 ^ 59
def prefixEnd_7266850 : Nat := 4983230072969 + 3 ^ 40 * 7266850 * 2
def baseEnd_7266850 : Nat := 3731386894124998649655371

theorem tailTrace_7266850 : CollatzResearch.WordTrace tailWord_7266850 prefixEnd_7266850 3731386894124998649655371 := by
  unfold tailWord_7266850
  simp only [CollatzResearch.WordTrace]
  refine ⟨66260948430862751004437501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176695862482300669345166669 66260948430862751004437501)
  ·
    refine ⟨24847855661573531626664063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66260948430862751004437501 24847855661573531626664063)
    ·
      refine ⟨37271783492360297439996095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24847855661573531626664063 37271783492360297439996095)
      ·
        refine ⟨55907675238540446159994143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37271783492360297439996095 55907675238540446159994143)
        ·
          refine ⟨83861512857810669239991215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55907675238540446159994143 83861512857810669239991215)
          ·
            refine ⟨125792269286716003859986823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83861512857810669239991215 125792269286716003859986823)
            ·
              refine ⟨188688403930074005789980235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125792269286716003859986823 188688403930074005789980235)
              ·
                refine ⟨283032605895111008684970353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188688403930074005789980235 283032605895111008684970353)
                ·
                  refine ⟨212274454421333256513727765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283032605895111008684970353 212274454421333256513727765)
                  ·
                    refine ⟨9950365050999996399080989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 212274454421333256513727765 9950365050999996399080989)
                    ·
                      refine ⟨3731386894124998649655371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9950365050999996399080989 3731386894124998649655371)
                      ·
                        rfl

theorem cell23_7266850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_7266850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266850 prefixEnd_7266850 := by exact prefixLift 7266850
  have htrace : WordTrace (prefixWord ++ tailWord_7266850) baseStart_7266850 baseEnd_7266850 := by
    simpa [prefixWord, tailWord_7266850, baseEnd_7266850] using wordTrace_append hprefix tailTrace_7266850
  have hstable : (prefixWord ++ tailWord_7266850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266850).length < 2 ^ (prefixWord ++ tailWord_7266850).sum := by decide
  have hdescent : baseEnd_7266850 < baseStart_7266850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266853 : List Nat := [1, 3, 1, 2, 2, 1, 3, 10]
def baseStart_7266853 : Nat := 118140960795 + 7266853 * 2 ^ 59
def prefixEnd_7266853 : Nat := 4983230072969 + 3 ^ 40 * 7266853 * 2
def baseEnd_7266853 : Nat := 138199571650628227330291

theorem tailTrace_7266853 : CollatzResearch.WordTrace tailWord_7266853 prefixEnd_7266853 138199571650628227330291 := by
  unfold tailWord_7266853
  simp only [CollatzResearch.WordTrace]
  refine ⟨265043903142440135530109213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176695935428293423686739475 265043903142440135530109213)
  ·
    refine ⟨99391463678415050823790955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265043903142440135530109213 99391463678415050823790955)
    ·
      refine ⟨149087195517622576235686433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99391463678415050823790955 149087195517622576235686433)
      ·
        refine ⟨111815396638216932176764825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149087195517622576235686433 111815396638216932176764825)
        ·
          refine ⟨83861547478662699132573619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111815396638216932176764825 83861547478662699132573619)
          ·
            refine ⟨125792321217994048698860429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83861547478662699132573619 125792321217994048698860429)
            ·
              refine ⟨47172120456747768262072661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125792321217994048698860429 47172120456747768262072661)
              ·
                refine ⟨138199571650628227330291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47172120456747768262072661 138199571650628227330291)
                ·
                  rfl

theorem cell23_7266853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 10].length) (baseStart_7266853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266853 prefixEnd_7266853 := by exact prefixLift 7266853
  have htrace : WordTrace (prefixWord ++ tailWord_7266853) baseStart_7266853 baseEnd_7266853 := by
    simpa [prefixWord, tailWord_7266853, baseEnd_7266853] using wordTrace_append hprefix tailTrace_7266853
  have hstable : (prefixWord ++ tailWord_7266853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266853).length < 2 ^ (prefixWord ++ tailWord_7266853).sum := by decide
  have hdescent : baseEnd_7266853 < baseStart_7266853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266861 : List Nat := [1, 5, 4, 1, 1, 1, 1, 1, 3, 5]
def baseStart_7266861 : Nat := 118140960795 + 7266861 * 2 ^ 59
def prefixEnd_7266861 : Nat := 4983230072969 + 3 ^ 40 * 7266861 * 2
def baseEnd_7266861 : Nat := 1243797514137399368872607

theorem tailTrace_7266861 : CollatzResearch.WordTrace tailWord_7266861 prefixEnd_7266861 1243797514137399368872607 := by
  unfold tailWord_7266861
  simp only [CollatzResearch.WordTrace]
  refine ⟨265044194926411152896400437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176696129950940768597600291 265044194926411152896400437)
  ·
    refine ⟨24847893274351045584037541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 265044194926411152896400437 24847893274351045584037541)
    ·
      refine ⟨4658979988940821047007039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24847893274351045584037541 4658979988940821047007039)
      ·
        refine ⟨6988469983411231570510559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4658979988940821047007039 6988469983411231570510559)
        ·
          refine ⟨10482704975116847355765839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6988469983411231570510559 10482704975116847355765839)
          ·
            refine ⟨15724057462675271033648759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10482704975116847355765839 15724057462675271033648759)
            ·
              refine ⟨23586086194012906550473139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15724057462675271033648759 23586086194012906550473139)
              ·
                refine ⟨35379129291019359825709709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23586086194012906550473139 35379129291019359825709709)
                ·
                  refine ⟨13267173484132259934641141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35379129291019359825709709 13267173484132259934641141)
                  ·
                    refine ⟨1243797514137399368872607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13267173484132259934641141 1243797514137399368872607)
                    ·
                      rfl

theorem cell23_7266861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_7266861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266861 prefixEnd_7266861 := by exact prefixLift 7266861
  have htrace : WordTrace (prefixWord ++ tailWord_7266861) baseStart_7266861 baseEnd_7266861 := by
    simpa [prefixWord, tailWord_7266861, baseEnd_7266861] using wordTrace_append hprefix tailTrace_7266861
  have hstable : (prefixWord ++ tailWord_7266861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266861).length < 2 ^ (prefixWord ++ tailWord_7266861).sum := by decide
  have hdescent : baseEnd_7266861 < baseStart_7266861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266868 : List Nat := [2, 5, 1, 3, 1, 1, 2, 1, 2, 3, 2]
def baseStart_7266868 : Nat := 118140960795 + 7266868 * 2 ^ 59
def prefixEnd_7266868 : Nat := 4983230072969 + 3 ^ 40 * 7266868 * 2
def baseEnd_7266868 : Nat := 3731396136776779579230289

theorem tailTrace_7266868 : CollatzResearch.WordTrace tailWord_7266868 prefixEnd_7266868 3731396136776779579230289 := by
  unfold tailWord_7266868
  simp only [CollatzResearch.WordTrace]
  refine ⟨132522225118692896545952629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176696300158257195394603505 132522225118692896545952629)
  ·
    refine ⟨12423958604877459051183059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132522225118692896545952629 12423958604877459051183059)
    ·
      refine ⟨18635937907316188576774589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12423958604877459051183059 18635937907316188576774589)
      ·
        refine ⟨6988476715243570716290471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18635937907316188576774589 6988476715243570716290471)
        ·
          refine ⟨10482715072865356074435707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6988476715243570716290471 10482715072865356074435707)
          ·
            refine ⟨15724072609298034111653561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10482715072865356074435707 15724072609298034111653561)
            ·
              refine ⟨11793054456973525583740171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15724072609298034111653561 11793054456973525583740171)
              ·
                refine ⟨17689581685460288375610257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11793054456973525583740171 17689581685460288375610257)
                ·
                  refine ⟨13267186264095216281707693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17689581685460288375610257 13267186264095216281707693)
                  ·
                    refine ⟨4975194849035706105640385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13267186264095216281707693 4975194849035706105640385)
                    ·
                      refine ⟨3731396136776779579230289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4975194849035706105640385 3731396136776779579230289)
                      ·
                        rfl

theorem cell23_7266868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_7266868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266868 prefixEnd_7266868 := by exact prefixLift 7266868
  have htrace : WordTrace (prefixWord ++ tailWord_7266868) baseStart_7266868 baseEnd_7266868 := by
    simpa [prefixWord, tailWord_7266868, baseEnd_7266868] using wordTrace_append hprefix tailTrace_7266868
  have hstable : (prefixWord ++ tailWord_7266868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266868).length < 2 ^ (prefixWord ++ tailWord_7266868).sum := by decide
  have hdescent : baseEnd_7266868 < baseStart_7266868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266877 : List Nat := [1, 4, 1, 3, 2, 2, 1, 2, 1, 2, 4]
def baseStart_7266877 : Nat := 118140960795 + 7266877 * 2 ^ 59
def prefixEnd_7266877 : Nat := 4983230072969 + 3 ^ 40 * 7266877 * 2
def baseEnd_7266877 : Nat := 3731400758102670044017747

theorem tailTrace_7266877 : CollatzResearch.WordTrace tailWord_7266877 prefixEnd_7266877 3731400758102670044017747 := by
  unfold tailWord_7266877
  simp only [CollatzResearch.WordTrace]
  refine ⟨265044778494353187628982885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176696518996235458419321923 265044778494353187628982885)
  ·
    refine ⟨49695895967691222680434291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265044778494353187628982885 49695895967691222680434291)
    ·
      refine ⟨74543843951536834020651437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49695895967691222680434291 74543843951536834020651437)
      ·
        refine ⟨27953941481826312757744289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74543843951536834020651437 27953941481826312757744289)
        ·
          refine ⟨20965456111369734568308217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27953941481826312757744289 20965456111369734568308217)
          ·
            refine ⟨15724092083527300926231163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20965456111369734568308217 15724092083527300926231163)
            ·
              refine ⟨23586138125290951389346745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15724092083527300926231163 23586138125290951389346745)
              ·
                refine ⟨17689603593968213542010059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23586138125290951389346745 17689603593968213542010059)
                ·
                  refine ⟨26534405390952320313015089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17689603593968213542010059 26534405390952320313015089)
                  ·
                    refine ⟨19900804043214240234761317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26534405390952320313015089 19900804043214240234761317)
                    ·
                      refine ⟨3731400758102670044017747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19900804043214240234761317 3731400758102670044017747)
                      ·
                        rfl

theorem cell23_7266877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_7266877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266877 prefixEnd_7266877 := by exact prefixLift 7266877
  have htrace : WordTrace (prefixWord ++ tailWord_7266877) baseStart_7266877 baseEnd_7266877 := by
    simpa [prefixWord, tailWord_7266877, baseEnd_7266877] using wordTrace_append hprefix tailTrace_7266877
  have hstable : (prefixWord ++ tailWord_7266877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266877).length < 2 ^ (prefixWord ++ tailWord_7266877).sum := by decide
  have hdescent : baseEnd_7266877 < baseStart_7266877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266880 : List Nat := [2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 3]
def baseStart_7266880 : Nat := 118140960795 + 7266880 * 2 ^ 59
def prefixEnd_7266880 : Nat := 4983230072969 + 3 ^ 40 * 7266880 * 2
def baseEnd_7266880 : Nat := 3731402298544633532280233

theorem tailTrace_7266880 : CollatzResearch.WordTrace tailWord_7266880 prefixEnd_7266880 3731402298544633532280233 := by
  unfold tailWord_7266880
  simp only [CollatzResearch.WordTrace]
  refine ⟨132522443956671159570671047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176696591942228212760894729 132522443956671159570671047)
  ·
    refine ⟨198783665935006739356006571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132522443956671159570671047 198783665935006739356006571)
    ·
      refine ⟨298175498902510109034009857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198783665935006739356006571 298175498902510109034009857)
      ·
        refine ⟨223631624176882581775507393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298175498902510109034009857 223631624176882581775507393)
        ·
          refine ⟨167723718132661936331630545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223631624176882581775507393 167723718132661936331630545)
          ·
            refine ⟨125792788599496452248722909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167723718132661936331630545 125792788599496452248722909)
            ·
              refine ⟨47172295724811169593271091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125792788599496452248722909 47172295724811169593271091)
              ·
                refine ⟨70758443587216754389906637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47172295724811169593271091 70758443587216754389906637)
                ·
                  refine ⟨26534416345206282896214989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70758443587216754389906637 26534416345206282896214989)
                  ·
                    refine ⟨9950406129452356086080621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26534416345206282896214989 9950406129452356086080621)
                    ·
                      refine ⟨3731402298544633532280233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9950406129452356086080621 3731402298544633532280233)
                      ·
                        rfl

theorem cell23_7266880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 3].length) (baseStart_7266880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266880 prefixEnd_7266880 := by exact prefixLift 7266880
  have htrace : WordTrace (prefixWord ++ tailWord_7266880) baseStart_7266880 baseEnd_7266880 := by
    simpa [prefixWord, tailWord_7266880, baseEnd_7266880] using wordTrace_append hprefix tailTrace_7266880
  have hstable : (prefixWord ++ tailWord_7266880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266880).length < 2 ^ (prefixWord ++ tailWord_7266880).sum := by decide
  have hdescent : baseEnd_7266880 < baseStart_7266880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266883 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 4, 7]
def baseStart_7266883 : Nat := 118140960795 + 7266883 * 2 ^ 59
def prefixEnd_7266883 : Nat := 4983230072969 + 3 ^ 40 * 7266883 * 2
def baseEnd_7266883 : Nat := 1243801279662199006847573

theorem tailTrace_7266883 : CollatzResearch.WordTrace tailWord_7266883 prefixEnd_7266883 1243801279662199006847573 := by
  unfold tailWord_7266883
  simp only [CollatzResearch.WordTrace]
  refine ⟨265044997332331450653701303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176696664888220967102467535 265044997332331450653701303)
  ·
    refine ⟨397567495998497175980551955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265044997332331450653701303 397567495998497175980551955)
    ·
      refine ⟨596351243997745763970827933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397567495998497175980551955 596351243997745763970827933)
      ·
        refine ⟨223631716499154661489060475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 596351243997745763970827933 223631716499154661489060475)
        ·
          refine ⟨335447574748731992233590713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223631716499154661489060475 335447574748731992233590713)
          ·
            refine ⟨251585681061548994175193035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335447574748731992233590713 251585681061548994175193035)
            ·
              refine ⟨377378521592323491262789553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251585681061548994175193035 377378521592323491262789553)
              ·
                refine ⟨283033891194242618447092165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 377378521592323491262789553 283033891194242618447092165)
                ·
                  refine ⟨53068854598920490958829781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 283033891194242618447092165 53068854598920490958829781)
                  ·
                    refine ⟨1243801279662199006847573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53068854598920490958829781 1243801279662199006847573)
                    ·
                      rfl

theorem cell23_7266883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 7].length) (baseStart_7266883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266883 prefixEnd_7266883 := by exact prefixLift 7266883
  have htrace : WordTrace (prefixWord ++ tailWord_7266883) baseStart_7266883 baseEnd_7266883 := by
    simpa [prefixWord, tailWord_7266883, baseEnd_7266883] using wordTrace_append hprefix tailTrace_7266883
  have hstable : (prefixWord ++ tailWord_7266883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266883).length < 2 ^ (prefixWord ++ tailWord_7266883).sum := by decide
  have hdescent : baseEnd_7266883 < baseStart_7266883 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266900 : List Nat := [2, 4, 1, 1, 1, 3, 1, 1, 2, 7]
def baseStart_7266900 : Nat := 118140960795 + 7266900 * 2 ^ 59
def prefixEnd_7266900 : Nat := 4983230072969 + 3 ^ 40 * 7266900 * 2
def baseEnd_7266900 : Nat := 1243804189385907818010047

theorem tailTrace_7266900 : CollatzResearch.WordTrace tailWord_7266900 prefixEnd_7266900 1243804189385907818010047 := by
  unfold tailWord_7266900
  simp only [CollatzResearch.WordTrace]
  refine ⟨132522808686634931278535077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176697078248846575038046769 132522808686634931278535077)
  ·
    refine ⟨24848026628744049614725327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132522808686634931278535077 24848026628744049614725327)
    ·
      refine ⟨37272039943116074422087991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24848026628744049614725327 37272039943116074422087991)
      ·
        refine ⟨55908059914674111633131987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37272039943116074422087991 55908059914674111633131987)
        ·
          refine ⟨83862089872011167449697981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55908059914674111633131987 83862089872011167449697981)
          ·
            refine ⟨31448283702004187793636743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83862089872011167449697981 31448283702004187793636743)
            ·
              refine ⟨47172425553006281690455115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31448283702004187793636743 47172425553006281690455115)
              ·
                refine ⟨70758638329509422535682673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47172425553006281690455115 70758638329509422535682673)
                ·
                  refine ⟨53068978747132066901762005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70758638329509422535682673 53068978747132066901762005)
                  ·
                    refine ⟨1243804189385907818010047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53068978747132066901762005 1243804189385907818010047)
                    ·
                      rfl

theorem cell23_7266900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_7266900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266900 prefixEnd_7266900 := by exact prefixLift 7266900
  have htrace : WordTrace (prefixWord ++ tailWord_7266900) baseStart_7266900 baseEnd_7266900 := by
    simpa [prefixWord, tailWord_7266900, baseEnd_7266900] using wordTrace_append hprefix tailTrace_7266900
  have hstable : (prefixWord ++ tailWord_7266900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266900).length < 2 ^ (prefixWord ++ tailWord_7266900).sum := by decide
  have hdescent : baseEnd_7266900 < baseStart_7266900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266940 : List Nat := [2, 2, 2, 1, 1, 2, 2, 3, 2, 1, 5]
def baseStart_7266940 : Nat := 118140960795 + 7266940 * 2 ^ 59
def prefixEnd_7266940 : Nat := 4983230072969 + 3 ^ 40 * 7266940 * 2
def baseEnd_7266940 : Nat := 3731433107383903297529957

theorem tailTrace_7266940 : CollatzResearch.WordTrace tailWord_7266940 prefixEnd_7266940 3731433107383903297529957 := by
  unfold tailWord_7266940
  simp only [CollatzResearch.WordTrace]
  refine ⟨132523538146562474694263137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176698050862083299592350849 132523538146562474694263137)
  ·
    refine ⟨99392653609921856020697353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132523538146562474694263137 99392653609921856020697353)
    ·
      refine ⟨74544490207441392015523015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99392653609921856020697353 74544490207441392015523015)
      ·
        refine ⟨111816735311162088023284523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74544490207441392015523015 111816735311162088023284523)
        ·
          refine ⟨167725102966743132034926785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111816735311162088023284523 167725102966743132034926785)
          ·
            refine ⟨125793827225057349026195089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167725102966743132034926785 125793827225057349026195089)
            ·
              refine ⟨94345370418793011769646317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125793827225057349026195089 94345370418793011769646317)
              ·
                refine ⟨35379513907047379413617369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94345370418793011769646317 35379513907047379413617369)
                ·
                  refine ⟨26534635430285534560213027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35379513907047379413617369 26534635430285534560213027)
                  ·
                    refine ⟨39801953145428301840319541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26534635430285534560213027 39801953145428301840319541)
                    ·
                      refine ⟨3731433107383903297529957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39801953145428301840319541 3731433107383903297529957)
                      ·
                        rfl

theorem cell23_7266940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_7266940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266940 prefixEnd_7266940 := by exact prefixLift 7266940
  have htrace : WordTrace (prefixWord ++ tailWord_7266940) baseStart_7266940 baseEnd_7266940 := by
    simpa [prefixWord, tailWord_7266940, baseEnd_7266940] using wordTrace_append hprefix tailTrace_7266940
  have hstable : (prefixWord ++ tailWord_7266940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266940).length < 2 ^ (prefixWord ++ tailWord_7266940).sum := by decide
  have hdescent : baseEnd_7266940 < baseStart_7266940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266941 : List Nat := [1, 4, 1, 1, 5, 1, 1, 3, 1, 3, 2]
def baseStart_7266941 : Nat := 118140960795 + 7266941 * 2 ^ 59
def prefixEnd_7266941 : Nat := 4983230072969 + 3 ^ 40 * 7266941 * 2
def baseEnd_7266941 : Nat := 3731433620864557793617453

theorem tailTrace_7266941 : CollatzResearch.WordTrace tailWord_7266941 prefixEnd_7266941 3731433620864557793617453 := by
  unfold tailWord_7266941
  simp only [CollatzResearch.WordTrace]
  refine ⟨265047112766121326559312677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176698075177414217706208451 265047112766121326559312677)
  ·
    refine ⟨49696333643647748729871127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265047112766121326559312677 49696333643647748729871127)
    ·
      refine ⟨74544500465471623094806691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49696333643647748729871127 74544500465471623094806691)
      ·
        refine ⟨111816750698207434642210037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74544500465471623094806691 111816750698207434642210037)
        ·
          refine ⟨10482820377956946997707191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111816750698207434642210037 10482820377956946997707191)
          ·
            refine ⟨15724230566935420496560787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10482820377956946997707191 15724230566935420496560787)
            ·
              refine ⟨23586345850403130744841181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15724230566935420496560787 23586345850403130744841181)
              ·
                refine ⟨8844879693901174029315443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23586345850403130744841181 8844879693901174029315443)
                ·
                  refine ⟨13267319540851761043973165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8844879693901174029315443 13267319540851761043973165)
                  ·
                    refine ⟨4975244827819410391489937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13267319540851761043973165 4975244827819410391489937)
                    ·
                      refine ⟨3731433620864557793617453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4975244827819410391489937 3731433620864557793617453)
                      ·
                        rfl

theorem cell23_7266941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 3, 2].length) (baseStart_7266941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7266941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7266941 prefixEnd_7266941 := by exact prefixLift 7266941
  have htrace : WordTrace (prefixWord ++ tailWord_7266941) baseStart_7266941 baseEnd_7266941 := by
    simpa [prefixWord, tailWord_7266941, baseEnd_7266941] using wordTrace_append hprefix tailTrace_7266941
  have hstable : (prefixWord ++ tailWord_7266941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266941).length < 2 ^ (prefixWord ++ tailWord_7266941).sum := by decide
  have hdescent : baseEnd_7266941 < baseStart_7266941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267007 : List Nat := [1, 1, 2, 2, 2, 5, 1, 2, 2, 5]
def baseStart_7267007 : Nat := 118140960795 + 7267007 * 2 ^ 59
def prefixEnd_7267007 : Nat := 4983230072969 + 3 ^ 40 * 7267007 * 2
def baseEnd_7267007 : Nat := 1243822503529251511797383

theorem tailTrace_7267007 : CollatzResearch.WordTrace tailWord_7267007 prefixEnd_7267007 1243822503529251511797383 := by
  unfold tailWord_7267007
  simp only [CollatzResearch.WordTrace]
  refine ⟨265049519983882219831215275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176699679989254813220810183 265049519983882219831215275)
  ·
    refine ⟨397574279975823329746822913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265049519983882219831215275 397574279975823329746822913)
    ·
      refine ⟨298180709981867497310117185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397574279975823329746822913 298180709981867497310117185)
      ·
        refine ⟨223635532486400622982587889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298180709981867497310117185 223635532486400622982587889)
        ·
          refine ⟨167726649364800467236940917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223635532486400622982587889 167726649364800467236940917)
          ·
            refine ⟨15724373377950043803463211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 167726649364800467236940917 15724373377950043803463211)
            ·
              refine ⟨23586560066925065705194817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15724373377950043803463211 23586560066925065705194817)
              ·
                refine ⟨17689920050193799278896113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23586560066925065705194817 17689920050193799278896113)
                ·
                  refine ⟨13267440037645349459172085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17689920050193799278896113 13267440037645349459172085)
                  ·
                    refine ⟨1243822503529251511797383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13267440037645349459172085 1243822503529251511797383)
                    ·
                      rfl

theorem cell23_7267007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 5].length) (baseStart_7267007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267007 prefixEnd_7267007 := by exact prefixLift 7267007
  have htrace : WordTrace (prefixWord ++ tailWord_7267007) baseStart_7267007 baseEnd_7267007 := by
    simpa [prefixWord, tailWord_7267007, baseEnd_7267007] using wordTrace_append hprefix tailTrace_7267007
  have hstable : (prefixWord ++ tailWord_7267007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267007).length < 2 ^ (prefixWord ++ tailWord_7267007).sum := by decide
  have hdescent : baseEnd_7267007 < baseStart_7267007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267040 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 6]
def baseStart_7267040 : Nat := 118140960795 + 7267040 * 2 ^ 59
def prefixEnd_7267040 : Nat := 4983230072969 + 3 ^ 40 * 7267040 * 2
def baseEnd_7267040 : Nat := 3731484455449352906279497

theorem tailTrace_7267040 : CollatzResearch.WordTrace tailWord_7267040 prefixEnd_7267040 3731484455449352906279497 := by
  unfold tailWord_7267040
  simp only [CollatzResearch.WordTrace]
  refine ⟨132525361796381333233583287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176700482395175110978111049 132525361796381333233583287)
  ·
    refine ⟨198788042694571999850374931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132525361796381333233583287 198788042694571999850374931)
    ·
      refine ⟨298182064041857999775562397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198788042694571999850374931 298182064041857999775562397)
      ·
        refine ⟨111818274015696749915835899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298182064041857999775562397 111818274015696749915835899)
        ·
          refine ⟨167727411023545124873753849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111818274015696749915835899 167727411023545124873753849)
          ·
            refine ⟨125795558267658843655315387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167727411023545124873753849 125795558267658843655315387)
            ·
              refine ⟨188693337401488265482973081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125795558267658843655315387 188693337401488265482973081)
              ·
                refine ⟨141520003051116199112229811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188693337401488265482973081 141520003051116199112229811)
                ·
                  refine ⟨212280004576674298668344717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141520003051116199112229811 212280004576674298668344717)
                  ·
                    refine ⟨79605001716252862000629269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 212280004576674298668344717 79605001716252862000629269)
                    ·
                      refine ⟨3731484455449352906279497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79605001716252862000629269 3731484455449352906279497)
                      ·
                        rfl

theorem cell23_7267040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_7267040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267040 prefixEnd_7267040 := by exact prefixLift 7267040
  have htrace : WordTrace (prefixWord ++ tailWord_7267040) baseStart_7267040 baseEnd_7267040 := by
    simpa [prefixWord, tailWord_7267040, baseEnd_7267040] using wordTrace_append hprefix tailTrace_7267040
  have hstable : (prefixWord ++ tailWord_7267040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267040).length < 2 ^ (prefixWord ++ tailWord_7267040).sum := by decide
  have hdescent : baseEnd_7267040 < baseStart_7267040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267044 : List Nat := [2, 3, 1, 1, 1, 5, 2, 1, 2, 1, 4]
def baseStart_7267044 : Nat := 118140960795 + 7267044 * 2 ^ 59
def prefixEnd_7267044 : Nat := 4983230072969 + 3 ^ 40 * 7267044 * 2
def baseEnd_7267044 : Nat := 3731486509371970890629479

theorem tailTrace_7267044 : CollatzResearch.WordTrace tailWord_7267044 prefixEnd_7267044 3731486509371970890629479 := by
  unfold tailWord_7267044
  simp only [CollatzResearch.WordTrace]
  refine ⟨132525434742374087575156093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176700579656498783433541457 132525434742374087575156093)
  ·
    refine ⟨49697038028390282840683535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132525434742374087575156093 49697038028390282840683535)
    ·
      refine ⟨74545557042585424261025303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49697038028390282840683535 74545557042585424261025303)
      ·
        refine ⟨111818335563878136391537955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74545557042585424261025303 111818335563878136391537955)
        ·
          refine ⟨167727503345817204587306933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111818335563878136391537955 167727503345817204587306933)
          ·
            refine ⟨15724453438670362930060025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 167727503345817204587306933 15724453438670362930060025)
            ·
              refine ⟨11793340079002772197545019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15724453438670362930060025 11793340079002772197545019)
              ·
                refine ⟨17690010118504158296317529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11793340079002772197545019 17690010118504158296317529)
                ·
                  refine ⟨13267507588878118722238147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17690010118504158296317529 13267507588878118722238147)
                  ·
                    refine ⟨19901261383317178083357221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13267507588878118722238147 19901261383317178083357221)
                    ·
                      refine ⟨3731486509371970890629479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19901261383317178083357221 3731486509371970890629479)
                      ·
                        rfl

theorem cell23_7267044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_7267044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267044 prefixEnd_7267044 := by exact prefixLift 7267044
  have htrace : WordTrace (prefixWord ++ tailWord_7267044) baseStart_7267044 baseEnd_7267044 := by
    simpa [prefixWord, tailWord_7267044, baseEnd_7267044] using wordTrace_append hprefix tailTrace_7267044
  have hstable : (prefixWord ++ tailWord_7267044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267044).length < 2 ^ (prefixWord ++ tailWord_7267044).sum := by decide
  have hdescent : baseEnd_7267044 < baseStart_7267044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267157 : List Nat := [1, 3, 2, 2, 2, 1, 3, 9]
def baseStart_7267157 : Nat := 118140960795 + 7267157 * 2 ^ 59
def prefixEnd_7267157 : Nat := 4983230072969 + 3 ^ 40 * 7267157 * 2
def baseEnd_7267157 : Nat := 138205353062441812908017

theorem tailTrace_7267157 : CollatzResearch.WordTrace tailWord_7267157 prefixEnd_7267157 138205353062441812908017 := by
  unfold tailWord_7267157
  simp only [CollatzResearch.WordTrace]
  refine ⟨265054990933338795449175725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176703327288892530299450483 265054990933338795449175725)
  ·
    refine ⟨99395621600002048293440897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265054990933338795449175725 99395621600002048293440897)
    ·
      refine ⟨74546716200001536220080673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99395621600002048293440897 74546716200001536220080673)
      ·
        refine ⟨55910037150001152165060505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74546716200001536220080673 55910037150001152165060505)
        ·
          refine ⟨41932527862500864123795379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55910037150001152165060505 41932527862500864123795379)
          ·
            refine ⟨62898791793751296185693069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41932527862500864123795379 62898791793751296185693069)
            ·
              refine ⟨23587046922656736069634901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62898791793751296185693069 23587046922656736069634901)
              ·
                refine ⟨138205353062441812908017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23587046922656736069634901 138205353062441812908017)
                ·
                  rfl

theorem cell23_7267157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 9].length) (baseStart_7267157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267157 prefixEnd_7267157 := by exact prefixLift 7267157
  have htrace : WordTrace (prefixWord ++ tailWord_7267157) baseStart_7267157 baseEnd_7267157 := by
    simpa [prefixWord, tailWord_7267157, baseEnd_7267157] using wordTrace_append hprefix tailTrace_7267157
  have hstable : (prefixWord ++ tailWord_7267157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267157).length < 2 ^ (prefixWord ++ tailWord_7267157).sum := by decide
  have hdescent : baseEnd_7267157 < baseStart_7267157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267171 : List Nat := [1, 1, 1, 5, 3, 1, 2, 3, 1, 2, 3]
def baseStart_7267171 : Nat := 118140960795 + 7267171 * 2 ^ 59
def prefixEnd_7267171 : Nat := 4983230072969 + 3 ^ 40 * 7267171 * 2
def baseEnd_7267171 : Nat := 3731551721415091893741395

theorem tailTrace_7267171 : CollatzResearch.WordTrace tailWord_7267171 prefixEnd_7267171 3731551721415091893741395 := by
  unfold tailWord_7267171
  simp only [CollatzResearch.WordTrace]
  refine ⟨265055501555288075840185367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176703667703525383893456911 265055501555288075840185367)
  ·
    refine ⟨397583252332932113760278051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265055501555288075840185367 397583252332932113760278051)
    ·
      refine ⟨596374878499398170640417077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397583252332932113760278051 596374878499398170640417077)
      ·
        refine ⟨55910144859318578497539101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 596374878499398170640417077 55910144859318578497539101)
        ·
          refine ⟨20966304322244466936577163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55910144859318578497539101 20966304322244466936577163)
          ·
            refine ⟨31449456483366700404865745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20966304322244466936577163 31449456483366700404865745)
            ·
              refine ⟨23587092362525025303649309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31449456483366700404865745 23587092362525025303649309)
              ·
                refine ⟨8845159635946884488868491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23587092362525025303649309 8845159635946884488868491)
                ·
                  refine ⟨13267739453920326733302737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8845159635946884488868491 13267739453920326733302737)
                  ·
                    refine ⟨9950804590440245049977053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13267739453920326733302737 9950804590440245049977053)
                    ·
                      refine ⟨3731551721415091893741395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9950804590440245049977053 3731551721415091893741395)
                      ·
                        rfl

theorem cell23_7267171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_7267171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267171 prefixEnd_7267171 := by exact prefixLift 7267171
  have htrace : WordTrace (prefixWord ++ tailWord_7267171) baseStart_7267171 baseEnd_7267171 := by
    simpa [prefixWord, tailWord_7267171, baseEnd_7267171] using wordTrace_append hprefix tailTrace_7267171
  have hstable : (prefixWord ++ tailWord_7267171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267171).length < 2 ^ (prefixWord ++ tailWord_7267171).sum := by decide
  have hdescent : baseEnd_7267171 < baseStart_7267171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267194 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 2, 7, 2]
def baseStart_7267194 : Nat := 118140960795 + 7267194 * 2 ^ 59
def prefixEnd_7267194 : Nat := 4983230072969 + 3 ^ 40 * 7267194 * 2
def baseEnd_7267194 : Nat := 3731563531470145303753789

theorem tailTrace_7267194 : CollatzResearch.WordTrace tailWord_7267194 prefixEnd_7267194 3731563531470145303753789 := by
  unfold tailWord_7267194
  simp only [CollatzResearch.WordTrace]
  refine ⟨66264085108551187692068159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176704226956136500512181757 66264085108551187692068159)
  ·
    refine ⟨99396127662826781538102239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66264085108551187692068159 99396127662826781538102239)
    ·
      refine ⟨149094191494240172307153359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99396127662826781538102239 149094191494240172307153359)
      ·
        refine ⟨223641287241360258460730039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149094191494240172307153359 223641287241360258460730039)
        ·
          refine ⟨335461930862040387691095059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223641287241360258460730039 335461930862040387691095059)
          ·
            refine ⟨503192896293060581536642589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335461930862040387691095059 503192896293060581536642589)
            ·
              refine ⟨188697336109897718076240971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 503192896293060581536642589 188697336109897718076240971)
              ·
                refine ⟨283046004164846577114361457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188697336109897718076240971 283046004164846577114361457)
                ·
                  refine ⟨212284503123634932835771093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283046004164846577114361457 212284503123634932835771093)
                  ·
                    refine ⟨4975418041960193738338385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 212284503123634932835771093 4975418041960193738338385)
                    ·
                      refine ⟨3731563531470145303753789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4975418041960193738338385 3731563531470145303753789)
                      ·
                        rfl

theorem cell23_7267194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 2, 7, 2].length) (baseStart_7267194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267194 prefixEnd_7267194 := by exact prefixLift 7267194
  have htrace : WordTrace (prefixWord ++ tailWord_7267194) baseStart_7267194 baseEnd_7267194 := by
    simpa [prefixWord, tailWord_7267194, baseEnd_7267194] using wordTrace_append hprefix tailTrace_7267194
  have hstable : (prefixWord ++ tailWord_7267194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267194).length < 2 ^ (prefixWord ++ tailWord_7267194).sum := by decide
  have hdescent : baseEnd_7267194 < baseStart_7267194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267202 : List Nat := [3, 4, 2, 2, 1, 2, 1, 2, 1, 1, 4]
def baseStart_7267202 : Nat := 118140960795 + 7267202 * 2 ^ 59
def prefixEnd_7267202 : Nat := 4983230072969 + 3 ^ 40 * 7267202 * 2
def baseEnd_7267202 : Nat := 3731567639315381272453753

theorem tailTrace_7267202 : CollatzResearch.WordTrace tailWord_7267202 prefixEnd_7267202 3731567639315381272453753 := by
  unfold tailWord_7267202
  simp only [CollatzResearch.WordTrace]
  refine ⟨66264158054543942033640965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176704421478783845423042573 66264158054543942033640965)
  ·
    refine ⟨12424529635226989131307681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66264158054543942033640965 12424529635226989131307681)
    ·
      refine ⟨9318397226420241848480761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12424529635226989131307681 9318397226420241848480761)
      ·
        refine ⟨6988797919815181386360571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9318397226420241848480761 6988797919815181386360571)
        ·
          refine ⟨10483196879722772079540857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6988797919815181386360571 10483196879722772079540857)
          ·
            refine ⟨7862397659792079059655643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10483196879722772079540857 7862397659792079059655643)
            ·
              refine ⟨11793596489688118589483465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7862397659792079059655643 11793596489688118589483465)
              ·
                refine ⟨8845197367266088942112599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11793596489688118589483465 8845197367266088942112599)
                ·
                  refine ⟨13267796050899133413168899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8845197367266088942112599 13267796050899133413168899)
                  ·
                    refine ⟨19901694076348700119753349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13267796050899133413168899 19901694076348700119753349)
                    ·
                      refine ⟨3731567639315381272453753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19901694076348700119753349 3731567639315381272453753)
                      ·
                        rfl

theorem cell23_7267202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_7267202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267202 prefixEnd_7267202 := by exact prefixLift 7267202
  have htrace : WordTrace (prefixWord ++ tailWord_7267202) baseStart_7267202 baseEnd_7267202 := by
    simpa [prefixWord, tailWord_7267202, baseEnd_7267202] using wordTrace_append hprefix tailTrace_7267202
  have hstable : (prefixWord ++ tailWord_7267202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267202).length < 2 ^ (prefixWord ++ tailWord_7267202).sum := by decide
  have hdescent : baseEnd_7267202 < baseStart_7267202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267217 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 4, 6]
def baseStart_7267217 : Nat := 118140960795 + 7267217 * 2 ^ 59
def prefixEnd_7267217 : Nat := 4983230072969 + 3 ^ 40 * 7267217 * 2
def baseEnd_7267217 : Nat := 1243858447175066237922061

theorem tailTrace_7267217 : CollatzResearch.WordTrace tailWord_7267217 prefixEnd_7267217 1243858447175066237922061 := by
  unfold tailWord_7267217
  simp only [CollatzResearch.WordTrace]
  refine ⟨265057179313121425696359905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176704786208747617130906603 265057179313121425696359905)
  ·
    refine ⟨198792884484841069272269929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265057179313121425696359905 198792884484841069272269929)
    ·
      refine ⟨149094663363630801954202447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198792884484841069272269929 149094663363630801954202447)
      ·
        refine ⟨223641995045446202931303671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149094663363630801954202447 223641995045446202931303671)
        ·
          refine ⟨335462992568169304396955507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223641995045446202931303671 335462992568169304396955507)
          ·
            refine ⟨503194488852253956595433261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335462992568169304396955507 503194488852253956595433261)
            ·
              refine ⟨188697933319595233723287473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 503194488852253956595433261 188697933319595233723287473)
              ·
                refine ⟨141523449989696425292465605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188697933319595233723287473 141523449989696425292465605)
                ·
                  refine ⟨26535646873068079742337301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141523449989696425292465605 26535646873068079742337301)
                  ·
                    refine ⟨1243858447175066237922061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26535646873068079742337301 1243858447175066237922061)
                    ·
                      rfl

theorem cell23_7267217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 6].length) (baseStart_7267217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267217 prefixEnd_7267217 := by exact prefixLift 7267217
  have htrace : WordTrace (prefixWord ++ tailWord_7267217) baseStart_7267217 baseEnd_7267217 := by
    simpa [prefixWord, tailWord_7267217, baseEnd_7267217] using wordTrace_append hprefix tailTrace_7267217
  have hstable : (prefixWord ++ tailWord_7267217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267217).length < 2 ^ (prefixWord ++ tailWord_7267217).sum := by decide
  have hdescent : baseEnd_7267217 < baseStart_7267217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267218 : List Nat := [3, 2, 3, 2, 2, 1, 1, 2, 1, 3, 3]
def baseStart_7267218 : Nat := 118140960795 + 7267218 * 2 ^ 59
def prefixEnd_7267218 : Nat := 4983230072969 + 3 ^ 40 * 7267218 * 2
def baseEnd_7267218 : Nat := 3731575855005853209853679

theorem tailTrace_7267218 : CollatzResearch.WordTrace tailWord_7267218 prefixEnd_7267218 3731575855005853209853679 := by
  unfold tailWord_7267218
  simp only [CollatzResearch.WordTrace]
  refine ⟨66264303946529450716786577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176704810524078535244764205 66264303946529450716786577)
  ·
    refine ⟨49698227959897088037589933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66264303946529450716786577 49698227959897088037589933)
    ·
      refine ⟨18636835484961408014096225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49698227959897088037589933 18636835484961408014096225)
      ·
        refine ⟨13977626613721056010572169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18636835484961408014096225 13977626613721056010572169)
        ·
          refine ⟨10483219960290792007929127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13977626613721056010572169 10483219960290792007929127)
          ·
            refine ⟨15724829940436188011893691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10483219960290792007929127 15724829940436188011893691)
            ·
              refine ⟨23587244910654282017840537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15724829940436188011893691 23587244910654282017840537)
              ·
                refine ⟨17690433682990711513380403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23587244910654282017840537 17690433682990711513380403)
                ·
                  refine ⟨26535650524486067270070605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17690433682990711513380403 26535650524486067270070605)
                  ·
                    refine ⟨9950868946682275226276477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26535650524486067270070605 9950868946682275226276477)
                    ·
                      refine ⟨3731575855005853209853679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9950868946682275226276477 3731575855005853209853679)
                      ·
                        rfl

theorem cell23_7267218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_7267218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267218 prefixEnd_7267218 := by exact prefixLift 7267218
  have htrace : WordTrace (prefixWord ++ tailWord_7267218) baseStart_7267218 baseEnd_7267218 := by
    simpa [prefixWord, tailWord_7267218, baseEnd_7267218] using wordTrace_append hprefix tailTrace_7267218
  have hstable : (prefixWord ++ tailWord_7267218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267218).length < 2 ^ (prefixWord ++ tailWord_7267218).sum := by decide
  have hdescent : baseEnd_7267218 < baseStart_7267218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267237 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 1, 5, 6]
def baseStart_7267237 : Nat := 118140960795 + 7267237 * 2 ^ 59
def prefixEnd_7267237 : Nat := 4983230072969 + 3 ^ 40 * 7267237 * 2
def baseEnd_7267237 : Nat := 3731585611138288635516091

theorem tailTrace_7267237 : CollatzResearch.WordTrace tailWord_7267237 prefixEnd_7267237 3731585611138288635516091 := by
  unfold tailWord_7267237
  simp only [CollatzResearch.WordTrace]
  refine ⟨265057908773048969112087965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176705272515365979408058643 265057908773048969112087965)
  ·
    refine ⟨99396715789893363417032987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265057908773048969112087965 99396715789893363417032987)
    ·
      refine ⟨149095073684840045125549481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99396715789893363417032987 149095073684840045125549481)
      ·
        refine ⟨111821305263630033844162111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149095073684840045125549481 111821305263630033844162111)
        ·
          refine ⟨167731957895445050766243167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111821305263630033844162111 167731957895445050766243167)
          ·
            refine ⟨251597936843167576149364751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167731957895445050766243167 251597936843167576149364751)
            ·
              refine ⟨377396905264751364224047127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251597936843167576149364751 377396905264751364224047127)
              ·
                refine ⟨566095357897127046336070691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377396905264751364224047127 566095357897127046336070691)
                ·
                  refine ⟨849143036845690569504106037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 566095357897127046336070691 849143036845690569504106037)
                  ·
                    refine ⟨79607159704283490891009941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 849143036845690569504106037 79607159704283490891009941)
                    ·
                      refine ⟨3731585611138288635516091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79607159704283490891009941 3731585611138288635516091)
                      ·
                        rfl

theorem cell23_7267237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_7267237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267237 prefixEnd_7267237 := by exact prefixLift 7267237
  have htrace : WordTrace (prefixWord ++ tailWord_7267237) baseStart_7267237 baseEnd_7267237 := by
    simpa [prefixWord, tailWord_7267237, baseEnd_7267237] using wordTrace_append hprefix tailTrace_7267237
  have hstable : (prefixWord ++ tailWord_7267237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267237).length < 2 ^ (prefixWord ++ tailWord_7267237).sum := by decide
  have hdescent : baseEnd_7267237 < baseStart_7267237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267258 : List Nat := [3, 1, 1, 1, 2, 1, 3, 5, 2, 2, 2]
def baseStart_7267258 : Nat := 118140960795 + 7267258 * 2 ^ 59
def prefixEnd_7267258 : Nat := 4983230072969 + 3 ^ 40 * 7267258 * 2
def baseEnd_7267258 : Nat := 3731596394232033053353495

theorem tailTrace_7267258 : CollatzResearch.WordTrace tailWord_7267258 prefixEnd_7267258 3731596394232033053353495 := by
  unfold tailWord_7267258
  simp only [CollatzResearch.WordTrace]
  refine ⟨66264668676493222424650607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176705783137315259799068285 66264668676493222424650607)
  ·
    refine ⟨99397003014739833636975911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66264668676493222424650607 99397003014739833636975911)
    ·
      refine ⟨149095504522109750455463867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99397003014739833636975911 149095504522109750455463867)
      ·
        refine ⟨223643256783164625683195801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149095504522109750455463867 223643256783164625683195801)
        ·
          refine ⟨167732442587373469262396851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223643256783164625683195801 167732442587373469262396851)
          ·
            refine ⟨251598663881060203893595277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167732442587373469262396851 251598663881060203893595277)
            ·
              refine ⟨94349498955397576460098229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 251598663881060203893595277 94349498955397576460098229)
              ·
                refine ⟨8845265527068522793134209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94349498955397576460098229 8845265527068522793134209)
                ·
                  refine ⟨6633949145301392094850657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8845265527068522793134209 6633949145301392094850657)
                  ·
                    refine ⟨4975461858976044071137993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6633949145301392094850657 4975461858976044071137993)
                    ·
                      refine ⟨3731596394232033053353495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4975461858976044071137993 3731596394232033053353495)
                      ·
                        rfl

theorem cell23_7267258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 2, 2, 2].length) (baseStart_7267258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267258 prefixEnd_7267258 := by exact prefixLift 7267258
  have htrace : WordTrace (prefixWord ++ tailWord_7267258) baseStart_7267258 baseEnd_7267258 := by
    simpa [prefixWord, tailWord_7267258, baseEnd_7267258] using wordTrace_append hprefix tailTrace_7267258
  have hstable : (prefixWord ++ tailWord_7267258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267258).length < 2 ^ (prefixWord ++ tailWord_7267258).sum := by decide
  have hdescent : baseEnd_7267258 < baseStart_7267258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267264 : List Nat := [2, 1, 1, 2, 3, 4, 1, 2, 7]
def baseStart_7267264 : Nat := 118140960795 + 7267264 * 2 ^ 59
def prefixEnd_7267264 : Nat := 4983230072969 + 3 ^ 40 * 7267264 * 2
def baseEnd_7267264 : Nat := 414622163901773336653163

theorem tailTrace_7267264 : CollatzResearch.WordTrace tailWord_7267264 prefixEnd_7267264 414622163901773336653163 := by
  unfold tailWord_7267264
  simp only [CollatzResearch.WordTrace]
  refine ⟨132529446771975576361660423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176705929029300768482213897 132529446771975576361660423)
  ·
    refine ⟨198794170157963364542490635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132529446771975576361660423 198794170157963364542490635)
    ·
      refine ⟨298191255236945046813735953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198794170157963364542490635 298191255236945046813735953)
      ·
        refine ⟨223643441427708785110301965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298191255236945046813735953 223643441427708785110301965)
        ·
          refine ⟨83866290535390794416363237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223643441427708785110301965 83866290535390794416363237)
          ·
            refine ⟨15724929475385773953068107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83866290535390794416363237 15724929475385773953068107)
            ·
              refine ⟨23587394213078660929602161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15724929475385773953068107 23587394213078660929602161)
              ·
                refine ⟨17690545659808995697201621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23587394213078660929602161 17690545659808995697201621)
                ·
                  refine ⟨414622163901773336653163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17690545659808995697201621 414622163901773336653163)
                  ·
                    rfl

theorem cell23_7267264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 7].length) (baseStart_7267264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267264 prefixEnd_7267264 := by exact prefixLift 7267264
  have htrace : WordTrace (prefixWord ++ tailWord_7267264) baseStart_7267264 baseEnd_7267264 := by
    simpa [prefixWord, tailWord_7267264, baseEnd_7267264] using wordTrace_append hprefix tailTrace_7267264
  have hstable : (prefixWord ++ tailWord_7267264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267264).length < 2 ^ (prefixWord ++ tailWord_7267264).sum := by decide
  have hdescent : baseEnd_7267264 < baseStart_7267264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267267 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 8]
def baseStart_7267267 : Nat := 118140960795 + 7267267 * 2 ^ 59
def prefixEnd_7267267 : Nat := 4983230072969 + 3 ^ 40 * 7267267 * 2
def baseEnd_7267267 : Nat := 3731601015557923518140953

theorem tailTrace_7267267 : CollatzResearch.WordTrace tailWord_7267267 prefixEnd_7267267 3731601015557923518140953 := by
  unfold tailWord_7267267
  simp only [CollatzResearch.WordTrace]
  refine ⟨265059002962940284235680055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176706001975293522823786703 265059002962940284235680055)
  ·
    refine ⟨397588504444410426353520083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265059002962940284235680055 397588504444410426353520083)
    ·
      refine ⟨596382756666615639530280125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397588504444410426353520083 596382756666615639530280125)
      ·
        refine ⟨223643533749980864823855047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 596382756666615639530280125 223643533749980864823855047)
        ·
          refine ⟨335465300624971297235782571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223643533749980864823855047 335465300624971297235782571)
          ·
            refine ⟨503197950937456945853673857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335465300624971297235782571 503197950937456945853673857)
            ·
              refine ⟨377398463203092709390255393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503197950937456945853673857 377398463203092709390255393)
              ·
                refine ⟨283048847402319532042691545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 377398463203092709390255393 283048847402319532042691545)
                ·
                  refine ⟨212286635551739649032018659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283048847402319532042691545 212286635551739649032018659)
                  ·
                    refine ⟨318429953327609473548027989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 212286635551739649032018659 318429953327609473548027989)
                    ·
                      refine ⟨3731601015557923518140953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 318429953327609473548027989 3731601015557923518140953)
                      ·
                        rfl

theorem cell23_7267267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_7267267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267267 prefixEnd_7267267 := by exact prefixLift 7267267
  have htrace : WordTrace (prefixWord ++ tailWord_7267267) baseStart_7267267 baseEnd_7267267 := by
    simpa [prefixWord, tailWord_7267267, baseEnd_7267267] using wordTrace_append hprefix tailTrace_7267267
  have hstable : (prefixWord ++ tailWord_7267267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267267).length < 2 ^ (prefixWord ++ tailWord_7267267).sum := by decide
  have hdescent : baseEnd_7267267 < baseStart_7267267 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267274 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 3, 5, 3]
def baseStart_7267274 : Nat := 118140960795 + 7267274 * 2 ^ 59
def prefixEnd_7267274 : Nat := 4983230072969 + 3 ^ 40 * 7267274 * 2
def baseEnd_7267274 : Nat := 3731604609922504990753421

theorem tailTrace_7267274 : CollatzResearch.WordTrace tailWord_7267274 prefixEnd_7267274 3731604609922504990753421 := by
  unfold tailWord_7267274
  simp only [CollatzResearch.WordTrace]
  refine ⟨66264814568478731107796219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176706172182609949620789917 66264814568478731107796219)
  ·
    refine ⟨99397221852718096661694329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66264814568478731107796219 99397221852718096661694329)
    ·
      refine ⟨74547916389538572496270747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99397221852718096661694329 74547916389538572496270747)
      ·
        refine ⟨111821874584307858744406121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74547916389538572496270747 111821874584307858744406121)
        ·
          refine ⟨83866405938230894058304591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111821874584307858744406121 83866405938230894058304591)
          ·
            refine ⟨125799608907346341087456887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83866405938230894058304591 125799608907346341087456887)
            ·
              refine ⟨188699413361019511631185331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125799608907346341087456887 188699413361019511631185331)
              ·
                refine ⟨283049120041529267446777997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188699413361019511631185331 283049120041529267446777997)
                ·
                  refine ⟨106143420015573475292541749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 283049120041529267446777997 106143420015573475292541749)
                  ·
                    refine ⟨9950945626460013308675789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 106143420015573475292541749 9950945626460013308675789)
                    ·
                      refine ⟨3731604609922504990753421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9950945626460013308675789 3731604609922504990753421)
                      ·
                        rfl

theorem cell23_7267274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_7267274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267274 prefixEnd_7267274 := by exact prefixLift 7267274
  have htrace : WordTrace (prefixWord ++ tailWord_7267274) baseStart_7267274 baseEnd_7267274 := by
    simpa [prefixWord, tailWord_7267274, baseEnd_7267274] using wordTrace_append hprefix tailTrace_7267274
  have hstable : (prefixWord ++ tailWord_7267274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267274).length < 2 ^ (prefixWord ++ tailWord_7267274).sum := by decide
  have hdescent : baseEnd_7267274 < baseStart_7267274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267281 : List Nat := [1, 2, 2, 1, 2, 1, 6, 3, 5]
def baseStart_7267281 : Nat := 118140960795 + 7267281 * 2 ^ 59
def prefixEnd_7267281 : Nat := 4983230072969 + 3 ^ 40 * 7267281 * 2
def baseEnd_7267281 : Nat := 414623133809676273707321

theorem tailTrace_7267281 : CollatzResearch.WordTrace tailWord_7267281 prefixEnd_7267281 414623133809676273707321 := by
  unfold tailWord_7267281
  simp only [CollatzResearch.WordTrace]
  refine ⟨265059513584889564626689697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176706342389926376417793131 265059513584889564626689697)
  ·
    refine ⟨198794635188667173470017273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265059513584889564626689697 198794635188667173470017273)
    ·
      refine ⟨149095976391500380102512955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198794635188667173470017273 149095976391500380102512955)
      ·
        refine ⟨223643964587250570153769433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149095976391500380102512955 223643964587250570153769433)
        ·
          refine ⟨167732973440437927615327075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223643964587250570153769433 167732973440437927615327075)
          ·
            refine ⟨251599460160656891422990613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167732973440437927615327075 251599460160656891422990613)
            ·
              refine ⟨11793724695030791785452685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 251599460160656891422990613 11793724695030791785452685)
              ·
                refine ⟨4422646760636546919544757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11793724695030791785452685 4422646760636546919544757)
                ·
                  refine ⟨414623133809676273707321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4422646760636546919544757 414623133809676273707321)
                  ·
                    rfl

theorem cell23_7267281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 3, 5].length) (baseStart_7267281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267281 prefixEnd_7267281 := by exact prefixLift 7267281
  have htrace : WordTrace (prefixWord ++ tailWord_7267281) baseStart_7267281 baseEnd_7267281 := by
    simpa [prefixWord, tailWord_7267281, baseEnd_7267281] using wordTrace_append hprefix tailTrace_7267281
  have hstable : (prefixWord ++ tailWord_7267281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267281).length < 2 ^ (prefixWord ++ tailWord_7267281).sum := by decide
  have hdescent : baseEnd_7267281 < baseStart_7267281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267298 : List Nat := [3, 3, 3, 1, 1, 2, 2, 1, 7]
def baseStart_7267298 : Nat := 118140960795 + 7267298 * 2 ^ 59
def prefixEnd_7267298 : Nat := 4983230072969 + 3 ^ 40 * 7267298 * 2
def baseEnd_7267298 : Nat := 414624103717579210761479

theorem tailTrace_7267298 : CollatzResearch.WordTrace tailWord_7267298 prefixEnd_7267298 414624103717579210761479 := by
  unfold tailWord_7267298
  simp only [CollatzResearch.WordTrace]
  refine ⟨66265033406456994132514637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176706755750551984353372365 66265033406456994132514637)
  ·
    refine ⟨24849387527421372799692989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66265033406456994132514637 24849387527421372799692989)
    ·
      refine ⟨9318520322783014799884871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24849387527421372799692989 9318520322783014799884871)
      ·
        refine ⟨13977780484174522199827307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9318520322783014799884871 13977780484174522199827307)
        ·
          refine ⟨20966670726261783299740961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13977780484174522199827307 20966670726261783299740961)
          ·
            refine ⟨15725003044696337474805721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20966670726261783299740961 15725003044696337474805721)
            ·
              refine ⟨11793752283522253106104291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15725003044696337474805721 11793752283522253106104291)
              ·
                refine ⟨17690628425283379659156437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11793752283522253106104291 17690628425283379659156437)
                ·
                  refine ⟨414624103717579210761479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17690628425283379659156437 414624103717579210761479)
                  ·
                    rfl

theorem cell23_7267298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_7267298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267298 prefixEnd_7267298 := by exact prefixLift 7267298
  have htrace : WordTrace (prefixWord ++ tailWord_7267298) baseStart_7267298 baseEnd_7267298 := by
    simpa [prefixWord, tailWord_7267298, baseEnd_7267298] using wordTrace_append hprefix tailTrace_7267298
  have hstable : (prefixWord ++ tailWord_7267298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267298).length < 2 ^ (prefixWord ++ tailWord_7267298).sum := by decide
  have hdescent : baseEnd_7267298 < baseStart_7267298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267304 : List Nat := [2, 1, 4, 1, 1, 1, 2, 3, 1, 2, 5]
def baseStart_7267304 : Nat := 118140960795 + 7267304 * 2 ^ 59
def prefixEnd_7267304 : Nat := 4983230072969 + 3 ^ 40 * 7267304 * 2
def baseEnd_7267304 : Nat := 3731620014342139873378283

theorem tailTrace_7267304 : CollatzResearch.WordTrace tailWord_7267304 prefixEnd_7267304 3731620014342139873378283 := by
  unfold tailWord_7267304
  simp only [CollatzResearch.WordTrace]
  refine ⟨132530176231903119777388483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176706901642537493036517977 132530176231903119777388483)
  ·
    refine ⟨198795264347854679666082725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132530176231903119777388483 198795264347854679666082725)
    ·
      refine ⟨37274112065222752437390511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198795264347854679666082725 37274112065222752437390511)
      ·
        refine ⟨55911168097834128656085767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37274112065222752437390511 55911168097834128656085767)
        ·
          refine ⟨83866752146751192984128651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55911168097834128656085767 83866752146751192984128651)
          ·
            refine ⟨125800128220126789476192977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83866752146751192984128651 125800128220126789476192977)
            ·
              refine ⟨94350096165095092107144733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125800128220126789476192977 94350096165095092107144733)
              ·
                refine ⟨35381286061910659540179275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94350096165095092107144733 35381286061910659540179275)
                ·
                  refine ⟨53071929092865989310268913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35381286061910659540179275 53071929092865989310268913)
                  ·
                    refine ⟨39803946819649491982701685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53071929092865989310268913 39803946819649491982701685)
                    ·
                      refine ⟨3731620014342139873378283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39803946819649491982701685 3731620014342139873378283)
                      ·
                        rfl

theorem cell23_7267304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_7267304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267304 prefixEnd_7267304 := by exact prefixLift 7267304
  have htrace : WordTrace (prefixWord ++ tailWord_7267304) baseStart_7267304 baseEnd_7267304 := by
    simpa [prefixWord, tailWord_7267304, baseEnd_7267304] using wordTrace_append hprefix tailTrace_7267304
  have hstable : (prefixWord ++ tailWord_7267304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267304).length < 2 ^ (prefixWord ++ tailWord_7267304).sum := by decide
  have hdescent : baseEnd_7267304 < baseStart_7267304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267354 : List Nat := [3, 1, 1, 3, 1, 2, 1, 3, 8]
def baseStart_7267354 : Nat := 118140960795 + 7267354 * 2 ^ 59
def prefixEnd_7267354 : Nat := 4983230072969 + 3 ^ 40 * 7267354 * 2
def baseEnd_7267354 : Nat := 414627298708318297528117

theorem tailTrace_7267354 : CollatzResearch.WordTrace tailWord_7267354 prefixEnd_7267354 414627298708318297528117 := by
  unfold tailWord_7267354
  simp only [CollatzResearch.WordTrace]
  refine ⟨66265544028406274523524279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176708117409083398729398077 66265544028406274523524279)
  ·
    refine ⟨99398316042609411785286419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66265544028406274523524279 99398316042609411785286419)
    ·
      refine ⟨149097474063914117677929629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99398316042609411785286419 149097474063914117677929629)
      ·
        refine ⟨55911552773967794129223611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149097474063914117677929629 55911552773967794129223611)
        ·
          refine ⟨83867329160951691193835417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55911552773967794129223611 83867329160951691193835417)
          ·
            refine ⟨62900496870713768395376563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83867329160951691193835417 62900496870713768395376563)
            ·
              refine ⟨94350745306070652593064845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62900496870713768395376563 94350745306070652593064845)
              ·
                refine ⟨35381529489776494722399317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94350745306070652593064845 35381529489776494722399317)
                ·
                  refine ⟨414627298708318297528117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35381529489776494722399317 414627298708318297528117)
                  ·
                    rfl

theorem cell23_7267354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 8].length) (baseStart_7267354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267354 prefixEnd_7267354 := by exact prefixLift 7267354
  have htrace : WordTrace (prefixWord ++ tailWord_7267354) baseStart_7267354 baseEnd_7267354 := by
    simpa [prefixWord, tailWord_7267354, baseEnd_7267354] using wordTrace_append hprefix tailTrace_7267354
  have hstable : (prefixWord ++ tailWord_7267354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267354).length < 2 ^ (prefixWord ++ tailWord_7267354).sum := by decide
  have hdescent : baseEnd_7267354 < baseStart_7267354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267431 : List Nat := [1, 1, 5, 1, 1, 3, 1, 3, 1, 6]
def baseStart_7267431 : Nat := 118140960795 + 7267431 * 2 ^ 59
def prefixEnd_7267431 : Nat := 4983230072969 + 3 ^ 40 * 7267431 * 2
def baseEnd_7267431 : Nat := 1243895075461753625496733

theorem tailTrace_7267431 : CollatzResearch.WordTrace tailWord_7267431 prefixEnd_7267431 1243895075461753625496733 := by
  unfold tailWord_7267431
  simp only [CollatzResearch.WordTrace]
  refine ⟨265064984534346140244650147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176709989689564093496433431 265064984534346140244650147)
  ·
    refine ⟨397597476801519210366975221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265064984534346140244650147 397597476801519210366975221)
    ·
      refine ⟨37274763450142425971903927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 397597476801519210366975221 37274763450142425971903927)
      ·
        refine ⟨55912145175213638957855891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37274763450142425971903927 55912145175213638957855891)
        ·
          refine ⟨83868217762820458436783837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55912145175213638957855891 83868217762820458436783837)
          ·
            refine ⟨31450581661057671913793939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83868217762820458436783837 31450581661057671913793939)
            ·
              refine ⟨47175872491586507870690909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31450581661057671913793939 47175872491586507870690909)
              ·
                refine ⟨17690952184344940451509091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47175872491586507870690909 17690952184344940451509091)
                ·
                  refine ⟨26536428276517410677263637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17690952184344940451509091 26536428276517410677263637)
                  ·
                    refine ⟨1243895075461753625496733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26536428276517410677263637 1243895075461753625496733)
                    ·
                      rfl

theorem cell23_7267431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_7267431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267431 prefixEnd_7267431 := by exact prefixLift 7267431
  have htrace : WordTrace (prefixWord ++ tailWord_7267431) baseStart_7267431 baseEnd_7267431 := by
    simpa [prefixWord, tailWord_7267431, baseEnd_7267431] using wordTrace_append hprefix tailTrace_7267431
  have hstable : (prefixWord ++ tailWord_7267431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267431).length < 2 ^ (prefixWord ++ tailWord_7267431).sum := by decide
  have hdescent : baseEnd_7267431 < baseStart_7267431 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267432 : List Nat := [2, 1, 4, 4, 1, 1, 1, 2, 3, 1, 3]
def baseStart_7267432 : Nat := 118140960795 + 7267432 * 2 ^ 59
def prefixEnd_7267432 : Nat := 4983230072969 + 3 ^ 40 * 7267432 * 2
def baseEnd_7267432 : Nat := 3731685739865915372577695

theorem tailTrace_7267432 : CollatzResearch.WordTrace tailWord_7267432 prefixEnd_7267432 3731685739865915372577695 := by
  unfold tailWord_7267432
  simp only [CollatzResearch.WordTrace]
  refine ⟨132532510503671258707718275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176710014004895011610291033 132532510503671258707718275)
  ·
    refine ⟨198798765755506888061577413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132532510503671258707718275 198798765755506888061577413)
    ·
      refine ⟨37274768579157541511545765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198798765755506888061577413 37274768579157541511545765)
      ·
        refine ⟨6989019108592039033414831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37274768579157541511545765 6989019108592039033414831)
        ·
          refine ⟨10483528662888058550122247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6989019108592039033414831 10483528662888058550122247)
          ·
            refine ⟨15725292994332087825183371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10483528662888058550122247 15725292994332087825183371)
            ·
              refine ⟨23587939491498131737775057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15725292994332087825183371 23587939491498131737775057)
              ·
                refine ⟨17690954618623598803331293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23587939491498131737775057 17690954618623598803331293)
                ·
                  refine ⟨6634107981983849551249235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17690954618623598803331293 6634107981983849551249235)
                  ·
                    refine ⟨9951161972975774326873853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6634107981983849551249235 9951161972975774326873853)
                    ·
                      refine ⟨3731685739865915372577695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9951161972975774326873853 3731685739865915372577695)
                      ·
                        rfl

theorem cell23_7267432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_7267432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267432 prefixEnd_7267432 := by exact prefixLift 7267432
  have htrace : WordTrace (prefixWord ++ tailWord_7267432) baseStart_7267432 baseEnd_7267432 := by
    simpa [prefixWord, tailWord_7267432, baseEnd_7267432] using wordTrace_append hprefix tailTrace_7267432
  have hstable : (prefixWord ++ tailWord_7267432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267432).length < 2 ^ (prefixWord ++ tailWord_7267432).sum := by decide
  have hdescent : baseEnd_7267432 < baseStart_7267432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267438 : List Nat := [4, 1, 2, 2, 1, 2, 2, 1, 3, 1, 4]
def baseStart_7267438 : Nat := 118140960795 + 7267438 * 2 ^ 59
def prefixEnd_7267438 : Nat := 4983230072969 + 3 ^ 40 * 7267438 * 2
def baseEnd_7267438 : Nat := 3731688820749842349102667

theorem tailTrace_7267438 : CollatzResearch.WordTrace tailWord_7267438 prefixEnd_7267438 3731688820749842349102667 := by
  unfold tailWord_7267438
  simp only [CollatzResearch.WordTrace]
  refine ⟨33133154980665097555019371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176710159896880520293436645 33133154980665097555019371)
  ·
    refine ⟨49699732470997646332529057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33133154980665097555019371 49699732470997646332529057)
    ·
      refine ⟨37274799353248234749396793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49699732470997646332529057 37274799353248234749396793)
      ·
        refine ⟨27956099514936176062047595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37274799353248234749396793 27956099514936176062047595)
        ·
          refine ⟨41934149272404264093071393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27956099514936176062047595 41934149272404264093071393)
          ·
            refine ⟨31450611954303198069803545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41934149272404264093071393 31450611954303198069803545)
            ·
              refine ⟨23587958965727398552352659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31450611954303198069803545 23587958965727398552352659)
              ·
                refine ⟨35381938448591097828528989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23587958965727398552352659 35381938448591097828528989)
                ·
                  refine ⟨13268226918221661685698371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35381938448591097828528989 13268226918221661685698371)
                  ·
                    refine ⟨19902340377332492528547557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13268226918221661685698371 19902340377332492528547557)
                    ·
                      refine ⟨3731688820749842349102667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19902340377332492528547557 3731688820749842349102667)
                      ·
                        rfl

theorem cell23_7267438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_7267438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267438 prefixEnd_7267438 := by exact prefixLift 7267438
  have htrace : WordTrace (prefixWord ++ tailWord_7267438) baseStart_7267438 baseEnd_7267438 := by
    simpa [prefixWord, tailWord_7267438, baseEnd_7267438] using wordTrace_append hprefix tailTrace_7267438
  have hstable : (prefixWord ++ tailWord_7267438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267438).length < 2 ^ (prefixWord ++ tailWord_7267438).sum := by decide
  have hdescent : baseEnd_7267438 < baseStart_7267438 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267461 : List Nat := [1, 3, 1, 1, 6, 1, 10]
def baseStart_7267461 : Nat := 118140960795 + 7267461 * 2 ^ 59
def prefixEnd_7267461 : Nat := 4983230072969 + 3 ^ 40 * 7267461 * 2
def baseEnd_7267461 : Nat := 46070378158085132828581

theorem tailTrace_7267461 : CollatzResearch.WordTrace tailWord_7267461 prefixEnd_7267461 46070378158085132828581 := by
  unfold tailWord_7267461
  simp only [CollatzResearch.WordTrace]
  refine ⟨265066078724237455368242237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176710719149491636912161491 265066078724237455368242237)
  ·
    refine ⟨99399779521589045763090839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265066078724237455368242237 99399779521589045763090839)
    ·
      refine ⟨149099669282383568644636259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99399779521589045763090839 149099669282383568644636259)
      ·
        refine ⟨223649503923575352966954389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149099669282383568644636259 223649503923575352966954389)
        ·
          refine ⟨10483570496417594670325987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 223649503923575352966954389 10483570496417594670325987)
          ·
            refine ⟨15725355744626392005488981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10483570496417594670325987 15725355744626392005488981)
            ·
              refine ⟨46070378158085132828581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15725355744626392005488981 46070378158085132828581)
              ·
                rfl

theorem cell23_7267461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 10].length) (baseStart_7267461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267461 prefixEnd_7267461 := by exact prefixLift 7267461
  have htrace : WordTrace (prefixWord ++ tailWord_7267461) baseStart_7267461 baseEnd_7267461 := by
    simpa [prefixWord, tailWord_7267461, baseEnd_7267461] using wordTrace_append hprefix tailTrace_7267461
  have hstable : (prefixWord ++ tailWord_7267461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267461).length < 2 ^ (prefixWord ++ tailWord_7267461).sum := by decide
  have hdescent : baseEnd_7267461 < baseStart_7267461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267465 : List Nat := [1, 2, 1, 1, 4, 5, 1, 2, 2, 4]
def baseStart_7267465 : Nat := 118140960795 + 7267465 * 2 ^ 59
def prefixEnd_7267465 : Nat := 4983230072969 + 3 ^ 40 * 7267465 * 2
def baseEnd_7267465 : Nat := 1243900894909171247821681

theorem tailTrace_7267465 : CollatzResearch.WordTrace tailWord_7267465 prefixEnd_7267465 1243900894909171247821681 := by
  unfold tailWord_7267465
  simp only [CollatzResearch.WordTrace]
  refine ⟨265066224616222964051387849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176710816410815309367591899 265066224616222964051387849)
  ·
    refine ⟨198799668462167223038540887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265066224616222964051387849 198799668462167223038540887)
    ·
      refine ⟨298199502693250834557811331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198799668462167223038540887 298199502693250834557811331)
      ·
        refine ⟨447299254039876251836716997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298199502693250834557811331 447299254039876251836716997)
        ·
          refine ⟨83868610132476797219384437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 447299254039876251836716997 83868610132476797219384437)
          ·
            refine ⟨7862682199919699739317291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83868610132476797219384437 7862682199919699739317291)
            ·
              refine ⟨11794023299879549608975937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7862682199919699739317291 11794023299879549608975937)
              ·
                refine ⟨8845517474909662206731953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11794023299879549608975937 8845517474909662206731953)
                ·
                  refine ⟨6634138106182246655048965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8845517474909662206731953 6634138106182246655048965)
                  ·
                    refine ⟨1243900894909171247821681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6634138106182246655048965 1243900894909171247821681)
                    ·
                      rfl

theorem cell23_7267465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 2, 4].length) (baseStart_7267465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267465 prefixEnd_7267465 := by exact prefixLift 7267465
  have htrace : WordTrace (prefixWord ++ tailWord_7267465) baseStart_7267465 baseEnd_7267465 := by
    simpa [prefixWord, tailWord_7267465, baseEnd_7267465] using wordTrace_append hprefix tailTrace_7267465
  have hstable : (prefixWord ++ tailWord_7267465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267465).length < 2 ^ (prefixWord ++ tailWord_7267465).sum := by decide
  have hdescent : baseEnd_7267465 < baseStart_7267465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267482 : List Nat := [3, 1, 1, 5, 1, 2, 3, 1, 2, 4]
def baseStart_7267482 : Nat := 118140960795 + 7267482 * 2 ^ 59
def prefixEnd_7267482 : Nat := 4983230072969 + 3 ^ 40 * 7267482 * 2
def baseEnd_7267482 : Nat := 1243903804632880058984155

theorem tailTrace_7267482 : CollatzResearch.WordTrace tailWord_7267482 prefixEnd_7267482 1243903804632880058984155 := by
  unfold tailWord_7267482
  simp only [CollatzResearch.WordTrace]
  refine ⟨66266711164290343988689175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176711229771440917303171133 66266711164290343988689175)
  ·
    refine ⟨99400066746435515983033763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66266711164290343988689175 99400066746435515983033763)
    ·
      refine ⟨149100100119653273974550645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99400066746435515983033763 149100100119653273974550645)
      ·
        refine ⟨13978134386217494435114123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149100100119653273974550645 13978134386217494435114123)
        ·
          refine ⟨20967201579326241652671185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13978134386217494435114123 20967201579326241652671185)
          ·
            refine ⟨15725401184494681239503389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20967201579326241652671185 15725401184494681239503389)
            ·
              refine ⟨5897025444185505464813771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15725401184494681239503389 5897025444185505464813771)
              ·
                refine ⟨8845538166278258197220657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5897025444185505464813771 8845538166278258197220657)
                ·
                  refine ⟨6634153624708693647915493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8845538166278258197220657 6634153624708693647915493)
                  ·
                    refine ⟨1243903804632880058984155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6634153624708693647915493 1243903804632880058984155)
                    ·
                      rfl

theorem cell23_7267482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 2, 4].length) (baseStart_7267482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267482 prefixEnd_7267482 := by exact prefixLift 7267482
  have htrace : WordTrace (prefixWord ++ tailWord_7267482) baseStart_7267482 baseEnd_7267482 := by
    simpa [prefixWord, tailWord_7267482, baseEnd_7267482] using wordTrace_append hprefix tailTrace_7267482
  have hstable : (prefixWord ++ tailWord_7267482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267482).length < 2 ^ (prefixWord ++ tailWord_7267482).sum := by decide
  have hdescent : baseEnd_7267482 < baseStart_7267482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267495 : List Nat := [1, 1, 6, 2, 1, 3, 2, 7]
def baseStart_7267495 : Nat := 118140960795 + 7267495 * 2 ^ 59
def prefixEnd_7267495 : Nat := 4983230072969 + 3 ^ 40 * 7267495 * 2
def baseEnd_7267495 : Nat := 138211781079524023188515

theorem tailTrace_7267495 : CollatzResearch.WordTrace tailWord_7267495 prefixEnd_7267495 138211781079524023188515 := by
  unfold tailWord_7267495
  simp only [CollatzResearch.WordTrace]
  refine ⟨265067318806114279174979939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176711545870742852783319959 265067318806114279174979939)
  ·
    refine ⟨397600978209171418762469909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265067318806114279174979939 397600978209171418762469909)
    ·
      refine ⟨18637545853554910254490777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 397600978209171418762469909 18637545853554910254490777)
      ·
        refine ⟨13978159390166182690868083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18637545853554910254490777 13978159390166182690868083)
        ·
          refine ⟨20967239085249274036302125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13978159390166182690868083 20967239085249274036302125)
          ·
            refine ⟨7862714656968477763613297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20967239085249274036302125 7862714656968477763613297)
            ·
              refine ⟨5897035992726358322709973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7862714656968477763613297 5897035992726358322709973)
              ·
                refine ⟨138211781079524023188515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5897035992726358322709973 138211781079524023188515)
                ·
                  rfl

theorem cell23_7267495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 7].length) (baseStart_7267495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267495 prefixEnd_7267495 := by exact prefixLift 7267495
  have htrace : WordTrace (prefixWord ++ tailWord_7267495) baseStart_7267495 baseEnd_7267495 := by
    simpa [prefixWord, tailWord_7267495, baseEnd_7267495] using wordTrace_append hprefix tailTrace_7267495
  have hstable : (prefixWord ++ tailWord_7267495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267495).length < 2 ^ (prefixWord ++ tailWord_7267495).sum := by decide
  have hdescent : baseEnd_7267495 < baseStart_7267495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267505 : List Nat := [1, 2, 2, 5, 1, 1, 1, 2, 4, 1, 3]
def baseStart_7267505 : Nat := 118140960795 + 7267505 * 2 ^ 59
def prefixEnd_7267505 : Nat := 4983230072969 + 3 ^ 40 * 7267505 * 2
def baseEnd_7267505 : Nat := 3731723223953693586964859

theorem tailTrace_7267505 : CollatzResearch.WordTrace tailWord_7267505 prefixEnd_7267505 3731723223953693586964859 := by
  unfold tailWord_7267505
  simp only [CollatzResearch.WordTrace]
  refine ⟨265067683536078050882843969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176711789024052033921895979 265067683536078050882843969)
  ·
    refine ⟨198800762652058538162132977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265067683536078050882843969 198800762652058538162132977)
    ·
      refine ⟨149100571989043903621599733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198800762652058538162132977 149100571989043903621599733)
      ·
        refine ⟨13978178623972865964524975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149100571989043903621599733 13978178623972865964524975)
        ·
          refine ⟨20967267935959298946787463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13978178623972865964524975 20967267935959298946787463)
          ·
            refine ⟨31450901903938948420181195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20967267935959298946787463 31450901903938948420181195)
            ·
              refine ⟨47176352855908422630271793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31450901903938948420181195 47176352855908422630271793)
              ·
                refine ⟨35382264641931316972703845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47176352855908422630271793 35382264641931316972703845)
                ·
                  refine ⟨6634174620362121932381971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35382264641931316972703845 6634174620362121932381971)
                  ·
                    refine ⟨9951261930543182898572957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6634174620362121932381971 9951261930543182898572957)
                    ·
                      refine ⟨3731723223953693586964859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9951261930543182898572957 3731723223953693586964859)
                      ·
                        rfl

theorem cell23_7267505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_7267505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267505 prefixEnd_7267505 := by exact prefixLift 7267505
  have htrace : WordTrace (prefixWord ++ tailWord_7267505) baseStart_7267505 baseEnd_7267505 := by
    simpa [prefixWord, tailWord_7267505, baseEnd_7267505] using wordTrace_append hprefix tailTrace_7267505
  have hstable : (prefixWord ++ tailWord_7267505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267505).length < 2 ^ (prefixWord ++ tailWord_7267505).sum := by decide
  have hdescent : baseEnd_7267505 < baseStart_7267505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267533 : List Nat := [1, 6, 2, 2, 2, 1, 2, 1, 2, 4]
def baseStart_7267533 : Nat := 118140960795 + 7267533 * 2 ^ 59
def prefixEnd_7267533 : Nat := 4983230072969 + 3 ^ 40 * 7267533 * 2
def baseEnd_7267533 : Nat := 1243912533804006492471577

theorem tailTrace_7267533 : CollatzResearch.WordTrace tailWord_7267533 prefixEnd_7267533 1243912533804006492471577 := by
  unfold tailWord_7267533
  simp only [CollatzResearch.WordTrace]
  refine ⟨265068704779976611664863253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176712469853317741109908835 265068704779976611664863253)
  ·
    refine ⟨12425095536561403671790465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 265068704779976611664863253 12425095536561403671790465)
    ·
      refine ⟨9318821652421052753842849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12425095536561403671790465 9318821652421052753842849)
      ·
        refine ⟨6989116239315789565382137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9318821652421052753842849 6989116239315789565382137)
        ·
          refine ⟨5241837179486842174036603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6989116239315789565382137 5241837179486842174036603)
          ·
            refine ⟨7862755769230263261054905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5241837179486842174036603 7862755769230263261054905)
            ·
              refine ⟨5897066826922697445791179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7862755769230263261054905 5897066826922697445791179)
              ·
                refine ⟨8845600240384046168686769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5897066826922697445791179 8845600240384046168686769)
                ·
                  refine ⟨6634200180288034626515077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8845600240384046168686769 6634200180288034626515077)
                  ·
                    refine ⟨1243912533804006492471577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6634200180288034626515077 1243912533804006492471577)
                    ·
                      rfl

theorem cell23_7267533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_7267533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267533 prefixEnd_7267533 := by exact prefixLift 7267533
  have htrace : WordTrace (prefixWord ++ tailWord_7267533) baseStart_7267533 baseEnd_7267533 := by
    simpa [prefixWord, tailWord_7267533, baseEnd_7267533] using wordTrace_append hprefix tailTrace_7267533
  have hstable : (prefixWord ++ tailWord_7267533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267533).length < 2 ^ (prefixWord ++ tailWord_7267533).sum := by decide
  have hdescent : baseEnd_7267533 < baseStart_7267533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267551 : List Nat := [1, 1, 2, 3, 2, 1, 2, 4, 7]
def baseStart_7267551 : Nat := 118140960795 + 7267551 * 2 ^ 59
def prefixEnd_7267551 : Nat := 4983230072969 + 3 ^ 40 * 7267551 * 2
def baseEnd_7267551 : Nat := 414638538229311156332183

theorem tailTrace_7267551 : CollatzResearch.WordTrace tailWord_7267551 prefixEnd_7267551 414638538229311156332183 := by
  unfold tailWord_7267551
  simp only [CollatzResearch.WordTrace]
  refine ⟨265069361293911400739018507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176712907529274267159345671 265069361293911400739018507)
  ·
    refine ⟨397604041940867101108527761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265069361293911400739018507 397604041940867101108527761)
    ·
      refine ⟨298203031455650325831395821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397604041940867101108527761 298203031455650325831395821)
      ·
        refine ⟨111826136795868872186773433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298203031455650325831395821 111826136795868872186773433)
        ·
          refine ⟨83869602596901654140080075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111826136795868872186773433 83869602596901654140080075)
          ·
            refine ⟨125804403895352481210120113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83869602596901654140080075 125804403895352481210120113)
            ·
              refine ⟨94353302921514360907590085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125804403895352481210120113 94353302921514360907590085)
              ·
                refine ⟨17691244297783942670173141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94353302921514360907590085 17691244297783942670173141)
                ·
                  refine ⟨414638538229311156332183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17691244297783942670173141 414638538229311156332183)
                  ·
                    rfl

theorem cell23_7267551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 7].length) (baseStart_7267551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267551 prefixEnd_7267551 := by exact prefixLift 7267551
  have htrace : WordTrace (prefixWord ++ tailWord_7267551) baseStart_7267551 baseEnd_7267551 := by
    simpa [prefixWord, tailWord_7267551, baseEnd_7267551] using wordTrace_append hprefix tailTrace_7267551
  have hstable : (prefixWord ++ tailWord_7267551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267551).length < 2 ^ (prefixWord ++ tailWord_7267551).sum := by decide
  have hdescent : baseEnd_7267551 < baseStart_7267551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267578 : List Nat := [3, 1, 1, 1, 1, 4, 2, 2, 2, 3, 3]
def baseStart_7267578 : Nat := 118140960795 + 7267578 * 2 ^ 59
def prefixEnd_7267578 : Nat := 4983230072969 + 3 ^ 40 * 7267578 * 2
def baseEnd_7267578 : Nat := 3731760708041471801352023

theorem tailTrace_7267578 : CollatzResearch.WordTrace tailWord_7267578 prefixEnd_7267578 3731760708041471801352023 := by
  unfold tailWord_7267578
  simp only [CollatzResearch.WordTrace]
  refine ⟨66267586516203396087562847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176713564043209056233500925 66267586516203396087562847)
  ·
    refine ⟨99401379774305094131344271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66267586516203396087562847 99401379774305094131344271)
    ·
      refine ⟨149102069661457641197016407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99401379774305094131344271 149102069661457641197016407)
      ·
        refine ⟨223653104492186461795524611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149102069661457641197016407 223653104492186461795524611)
        ·
          refine ⟨335479656738279692693286917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223653104492186461795524611 335479656738279692693286917)
          ·
            refine ⟨62902435638427442379991297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 335479656738279692693286917 62902435638427442379991297)
            ·
              refine ⟨47176826728820581784993473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62902435638427442379991297 47176826728820581784993473)
              ·
                refine ⟨35382620046615436338745105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47176826728820581784993473 35382620046615436338745105)
                ·
                  refine ⟨26536965034961577254058829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35382620046615436338745105 26536965034961577254058829)
                  ·
                    refine ⟨9951361888110591470272061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26536965034961577254058829 9951361888110591470272061)
                    ·
                      refine ⟨3731760708041471801352023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9951361888110591470272061 3731760708041471801352023)
                      ·
                        rfl

theorem cell23_7267578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 2, 3, 3].length) (baseStart_7267578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267578 prefixEnd_7267578 := by exact prefixLift 7267578
  have htrace : WordTrace (prefixWord ++ tailWord_7267578) baseStart_7267578 baseEnd_7267578 := by
    simpa [prefixWord, tailWord_7267578, baseEnd_7267578] using wordTrace_append hprefix tailTrace_7267578
  have hstable : (prefixWord ++ tailWord_7267578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267578).length < 2 ^ (prefixWord ++ tailWord_7267578).sum := by decide
  have hdescent : baseEnd_7267578 < baseStart_7267578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267581 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 5, 7]
def baseStart_7267581 : Nat := 118140960795 + 7267581 * 2 ^ 59
def prefixEnd_7267581 : Nat := 4983230072969 + 3 ^ 40 * 7267581 * 2
def baseEnd_7267581 : Nat := 1243920749494478429871503

theorem tailTrace_7267581 : CollatzResearch.WordTrace tailWord_7267581 prefixEnd_7267581 1243920749494478429871503 := by
  unfold tailWord_7267581
  simp only [CollatzResearch.WordTrace]
  refine ⟨265070455483802715862610597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176713636989201810575073731 265070455483802715862610597)
  ·
    refine ⟨49700710403213009224239487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265070455483802715862610597 49700710403213009224239487)
    ·
      refine ⟨74551065604819513836359231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49700710403213009224239487 74551065604819513836359231)
      ·
        refine ⟨111826598407229270754538847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74551065604819513836359231 111826598407229270754538847)
        ·
          refine ⟨167739897610843906131808271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111826598407229270754538847 167739897610843906131808271)
          ·
            refine ⟨251609846416265859197712407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167739897610843906131808271 251609846416265859197712407)
            ·
              refine ⟨377414769624398788796568611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251609846416265859197712407 377414769624398788796568611)
              ·
                refine ⟨566122154436598183194852917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377414769624398788796568611 566122154436598183194852917)
                ·
                  refine ⟨53073951978431079674517461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 566122154436598183194852917 53073951978431079674517461)
                  ·
                    refine ⟨1243920749494478429871503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53073951978431079674517461 1243920749494478429871503)
                    ·
                      rfl

theorem cell23_7267581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_7267581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267581 prefixEnd_7267581 := by exact prefixLift 7267581
  have htrace : WordTrace (prefixWord ++ tailWord_7267581) baseStart_7267581 baseEnd_7267581 := by
    simpa [prefixWord, tailWord_7267581, baseEnd_7267581] using wordTrace_append hprefix tailTrace_7267581
  have hstable : (prefixWord ++ tailWord_7267581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267581).length < 2 ^ (prefixWord ++ tailWord_7267581).sum := by decide
  have hdescent : baseEnd_7267581 < baseStart_7267581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267585 : List Nat := [1, 2, 4, 1, 1, 4, 1, 4, 5]
def baseStart_7267585 : Nat := 118140960795 + 7267585 * 2 ^ 59
def prefixEnd_7267585 : Nat := 4983230072969 + 3 ^ 40 * 7267585 * 2
def baseEnd_7267585 : Nat := 414640478045117030440499

theorem tailTrace_7267585 : CollatzResearch.WordTrace tailWord_7267585 prefixEnd_7267585 414640478045117030440499 := by
  unfold tailWord_7267585
  simp only [CollatzResearch.WordTrace]
  refine ⟨265070601375788224545756209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176713734250525483030504139 265070601375788224545756209)
  ·
    refine ⟨198802951031841168409317157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265070601375788224545756209 198802951031841168409317157)
    ·
      refine ⟨37275553318470219076746967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198802951031841168409317157 37275553318470219076746967)
      ·
        refine ⟨55913329977705328615120451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37275553318470219076746967 55913329977705328615120451)
        ·
          refine ⟨83869994966557992922680677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55913329977705328615120451 83869994966557992922680677)
          ·
            refine ⟨15725624056229623673002627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83869994966557992922680677 15725624056229623673002627)
            ·
              refine ⟨23588436084344435509503941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15725624056229623673002627 23588436084344435509503941)
              ·
                refine ⟨4422831765814581658031989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23588436084344435509503941 4422831765814581658031989)
                ·
                  refine ⟨414640478045117030440499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4422831765814581658031989 414640478045117030440499)
                  ·
                    rfl

theorem cell23_7267585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 4, 5].length) (baseStart_7267585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267585 prefixEnd_7267585 := by exact prefixLift 7267585
  have htrace : WordTrace (prefixWord ++ tailWord_7267585) baseStart_7267585 baseEnd_7267585 := by
    simpa [prefixWord, tailWord_7267585, baseEnd_7267585] using wordTrace_append hprefix tailTrace_7267585
  have hstable : (prefixWord ++ tailWord_7267585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267585).length < 2 ^ (prefixWord ++ tailWord_7267585).sum := by decide
  have hdescent : baseEnd_7267585 < baseStart_7267585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267602 : List Nat := [3, 2, 4, 2, 1, 1, 1, 2, 7]
def baseStart_7267602 : Nat := 118140960795 + 7267602 * 2 ^ 59
def prefixEnd_7267602 : Nat := 4983230072969 + 3 ^ 40 * 7267602 * 2
def baseEnd_7267602 : Nat := 414641447953019967494657

theorem tailTrace_7267602 : CollatzResearch.WordTrace tailWord_7267602 prefixEnd_7267602 414641447953019967494657 := by
  unfold tailWord_7267602
  simp only [CollatzResearch.WordTrace]
  refine ⟨66267805354181659112281265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176714147611151090966083373 66267805354181659112281265)
  ·
    refine ⟨49700854015636244334210949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66267805354181659112281265 49700854015636244334210949)
    ·
      refine ⟨9318910127931795812664553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49700854015636244334210949 9318910127931795812664553)
      ·
        refine ⟨6989182595948846859498415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9318910127931795812664553 6989182595948846859498415)
        ·
          refine ⟨10483773893923270289247623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6989182595948846859498415 10483773893923270289247623)
          ·
            refine ⟨15725660840884905433871435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10483773893923270289247623 15725660840884905433871435)
            ·
              refine ⟨23588491261327358150807153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15725660840884905433871435 23588491261327358150807153)
              ·
                refine ⟨17691368445995518613105365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23588491261327358150807153 17691368445995518613105365)
                ·
                  refine ⟨414641447953019967494657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17691368445995518613105365 414641447953019967494657)
                  ·
                    rfl

theorem cell23_7267602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 7].length) (baseStart_7267602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267602 prefixEnd_7267602 := by exact prefixLift 7267602
  have htrace : WordTrace (prefixWord ++ tailWord_7267602) baseStart_7267602 baseEnd_7267602 := by
    simpa [prefixWord, tailWord_7267602, baseEnd_7267602] using wordTrace_append hprefix tailTrace_7267602
  have hstable : (prefixWord ++ tailWord_7267602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267602).length < 2 ^ (prefixWord ++ tailWord_7267602).sum := by decide
  have hdescent : baseEnd_7267602 < baseStart_7267602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267628 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 7, 4]
def baseStart_7267628 : Nat := 118140960795 + 7267628 * 2 ^ 59
def prefixEnd_7267628 : Nat := 4983230072969 + 3 ^ 40 * 7267628 * 2
def baseEnd_7267628 : Nat := 1243928794024732201908931

theorem tailTrace_7267628 : CollatzResearch.WordTrace tailWord_7267628 prefixEnd_7267628 1243928794024732201908931 := by
  unfold tailWord_7267628
  simp only [CollatzResearch.WordTrace]
  refine ⟨132536084857316221444785769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176714779809754961926381025 132536084857316221444785769)
  ·
    refine ⟨99402063642987166083589327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132536084857316221444785769 99402063642987166083589327)
    ·
      refine ⟨149103095464480749125383991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99402063642987166083589327 149103095464480749125383991)
      ·
        refine ⟨223654643196721123688075987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149103095464480749125383991 223654643196721123688075987)
        ·
          refine ⟨335481964795081685532113981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223654643196721123688075987 335481964795081685532113981)
          ·
            refine ⟨125805736798155632074542743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 335481964795081685532113981 125805736798155632074542743)
            ·
              refine ⟨188708605197233448111814115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125805736798155632074542743 188708605197233448111814115)
              ·
                refine ⟨283062907795850172167721173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188708605197233448111814115 283062907795850172167721173)
                ·
                  refine ⟨6634286901465238410180965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 283062907795850172167721173 6634286901465238410180965)
                  ·
                    refine ⟨1243928794024732201908931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6634286901465238410180965 1243928794024732201908931)
                    ·
                      rfl

theorem cell23_7267628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 4].length) (baseStart_7267628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267628 prefixEnd_7267628 := by exact prefixLift 7267628
  have htrace : WordTrace (prefixWord ++ tailWord_7267628) baseStart_7267628 baseEnd_7267628 := by
    simpa [prefixWord, tailWord_7267628, baseEnd_7267628] using wordTrace_append hprefix tailTrace_7267628
  have hstable : (prefixWord ++ tailWord_7267628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267628).length < 2 ^ (prefixWord ++ tailWord_7267628).sum := by decide
  have hdescent : baseEnd_7267628 < baseStart_7267628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267635 : List Nat := [1, 1, 1, 2, 5, 2, 1, 2, 2, 4, 2]
def baseStart_7267635 : Nat := 118140960795 + 7267635 * 2 ^ 59
def prefixEnd_7267635 : Nat := 4983230072969 + 3 ^ 40 * 7267635 * 2
def baseEnd_7267635 : Nat := 3731789976438778078339261

theorem tailTrace_7267635 : CollatzResearch.WordTrace tailWord_7267635 prefixEnd_7267635 3731789976438778078339261 := by
  unfold tailWord_7267635
  simp only [CollatzResearch.WordTrace]
  refine ⟨265072425025607083085076359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176714950017071388723384239 265072425025607083085076359)
  ·
    refine ⟨397608637538410624627614539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265072425025607083085076359 397608637538410624627614539)
    ·
      refine ⟨596412956307615936941421809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397608637538410624627614539 596412956307615936941421809)
      ·
        refine ⟨447309717230711952706066357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 596412956307615936941421809 447309717230711952706066357)
        ·
          refine ⟨41935285990379245566193721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 447309717230711952706066357 41935285990379245566193721)
          ·
            refine ⟨31451464492784434174645291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41935285990379245566193721 31451464492784434174645291)
            ·
              refine ⟨47177196739176651261967937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31451464492784434174645291 47177196739176651261967937)
              ·
                refine ⟨35382897554382488446475953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47177196739176651261967937 35382897554382488446475953)
                ·
                  refine ⟨26537173165786866334856965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35382897554382488446475953 26537173165786866334856965)
                  ·
                    refine ⟨4975719968585037437785681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26537173165786866334856965 4975719968585037437785681)
                    ·
                      refine ⟨3731789976438778078339261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4975719968585037437785681 3731789976438778078339261)
                      ·
                        rfl

theorem cell23_7267635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 4, 2].length) (baseStart_7267635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267635 prefixEnd_7267635 := by exact prefixLift 7267635
  have htrace : WordTrace (prefixWord ++ tailWord_7267635) baseStart_7267635 baseEnd_7267635 := by
    simpa [prefixWord, tailWord_7267635, baseEnd_7267635] using wordTrace_append hprefix tailTrace_7267635
  have hstable : (prefixWord ++ tailWord_7267635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267635).length < 2 ^ (prefixWord ++ tailWord_7267635).sum := by decide
  have hdescent : baseEnd_7267635 < baseStart_7267635 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267658 : List Nat := [3, 1, 2, 1, 1, 1, 1, 7, 6]
def baseStart_7267658 : Nat := 118140960795 + 7267658 * 2 ^ 59
def prefixEnd_7267658 : Nat := 4983230072969 + 3 ^ 40 * 7267658 * 2
def baseEnd_7267658 : Nat := 414644642943759054261295

theorem tailTrace_7267658 : CollatzResearch.WordTrace tailWord_7267658 prefixEnd_7267658 414644642943759054261295 := by
  unfold tailWord_7267658
  simp only [CollatzResearch.WordTrace]
  refine ⟨66268315976130939503290907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176715509269682505342109085 66268315976130939503290907)
  ·
    refine ⟨99402473964196409254936361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66268315976130939503290907 99402473964196409254936361)
    ·
      refine ⟨74551855473147306941202271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99402473964196409254936361 74551855473147306941202271)
      ·
        refine ⟨111827783209720960411803407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74551855473147306941202271 111827783209720960411803407)
        ·
          refine ⟨167741674814581440617705111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111827783209720960411803407 167741674814581440617705111)
          ·
            refine ⟨251612512221872160926557667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167741674814581440617705111 251612512221872160926557667)
            ·
              refine ⟨377418768332808241389836501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251612512221872160926557667 377418768332808241389836501)
              ·
                refine ⟨8845752382800193157574293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 377418768332808241389836501 8845752382800193157574293)
                ·
                  refine ⟨414644642943759054261295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8845752382800193157574293 414644642943759054261295)
                  ·
                    rfl

theorem cell23_7267658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 6].length) (baseStart_7267658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267658 prefixEnd_7267658 := by exact prefixLift 7267658
  have htrace : WordTrace (prefixWord ++ tailWord_7267658) baseStart_7267658 baseEnd_7267658 := by
    simpa [prefixWord, tailWord_7267658, baseEnd_7267658] using wordTrace_append hprefix tailTrace_7267658
  have hstable : (prefixWord ++ tailWord_7267658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267658).length < 2 ^ (prefixWord ++ tailWord_7267658).sum := by decide
  have hdescent : baseEnd_7267658 < baseStart_7267658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267670 : List Nat := [5, 2, 3, 1, 2, 1, 1, 3, 5]
def baseStart_7267670 : Nat := 118140960795 + 7267670 * 2 ^ 59
def prefixEnd_7267670 : Nat := 4983230072969 + 3 ^ 40 * 7267670 * 2
def baseEnd_7267670 : Nat := 414645327584631715711289

theorem tailTrace_7267670 : CollatzResearch.WordTrace tailWord_7267670 prefixEnd_7267670 414645327584631715711289 := by
  unfold tailWord_7267670
  simp only [CollatzResearch.WordTrace]
  refine ⟨16567106348780017753912529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176715801053653522708400309 16567106348780017753912529)
  ·
    refine ⟨12425329761585013315434397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16567106348780017753912529 12425329761585013315434397)
    ·
      refine ⟨4659498660594379993287899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12425329761585013315434397 4659498660594379993287899)
      ·
        refine ⟨6989247990891569989931849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4659498660594379993287899 6989247990891569989931849)
        ·
          refine ⟨5241935993168677492448887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6989247990891569989931849 5241935993168677492448887)
          ·
            refine ⟨7862903989753016238673331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5241935993168677492448887 7862903989753016238673331)
            ·
              refine ⟨11794355984629524358009997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7862903989753016238673331 11794355984629524358009997)
              ·
                refine ⟨4422883494236071634253749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11794355984629524358009997 4422883494236071634253749)
                ·
                  refine ⟨414645327584631715711289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4422883494236071634253749 414645327584631715711289)
                  ·
                    rfl

theorem cell23_7267670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_7267670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267670 prefixEnd_7267670 := by exact prefixLift 7267670
  have htrace : WordTrace (prefixWord ++ tailWord_7267670) baseStart_7267670 baseEnd_7267670 := by
    simpa [prefixWord, tailWord_7267670, baseEnd_7267670] using wordTrace_append hprefix tailTrace_7267670
  have hstable : (prefixWord ++ tailWord_7267670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267670).length < 2 ^ (prefixWord ++ tailWord_7267670).sum := by decide
  have hdescent : baseEnd_7267670 < baseStart_7267670 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267765 : List Nat := [1, 3, 3, 2, 2, 1, 3, 8]
def baseStart_7267765 : Nat := 118140960795 + 7267765 * 2 ^ 59
def prefixEnd_7267765 : Nat := 4983230072969 + 3 ^ 40 * 7267765 * 2
def baseEnd_7267765 : Nat := 138216915886068984063469

theorem tailTrace_7267765 : CollatzResearch.WordTrace tailWord_7267765 prefixEnd_7267765 138216915886068984063469 := by
  unfold tailWord_7267765
  simp only [CollatzResearch.WordTrace]
  refine ⟨265077166515136115287308749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176718111010090743524872499 265077166515136115287308749)
  ·
    refine ⟨99403937443176043232740781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265077166515136115287308749 99403937443176043232740781)
    ·
      refine ⟨37276476541191016212277793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99403937443176043232740781 37276476541191016212277793)
      ·
        refine ⟨27957357405893262159208345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37276476541191016212277793 27957357405893262159208345)
        ·
          refine ⟨20968018054419946619406259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27957357405893262159208345 20968018054419946619406259)
          ·
            refine ⟨31452027081629919929109389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20968018054419946619406259 31452027081629919929109389)
            ·
              refine ⟨11794510155611219973416021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31452027081629919929109389 11794510155611219973416021)
              ·
                refine ⟨138216915886068984063469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11794510155611219973416021 138216915886068984063469)
                ·
                  rfl

theorem cell23_7267765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 8].length) (baseStart_7267765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267765 prefixEnd_7267765 := by exact prefixLift 7267765
  have htrace : WordTrace (prefixWord ++ tailWord_7267765) baseStart_7267765 baseEnd_7267765 := by
    simpa [prefixWord, tailWord_7267765, baseEnd_7267765] using wordTrace_append hprefix tailTrace_7267765
  have hstable : (prefixWord ++ tailWord_7267765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267765).length < 2 ^ (prefixWord ++ tailWord_7267765).sum := by decide
  have hdescent : baseEnd_7267765 < baseStart_7267765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267768 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 6]
def baseStart_7267768 : Nat := 118140960795 + 7267768 * 2 ^ 59
def prefixEnd_7267768 : Nat := 4983230072969 + 3 ^ 40 * 7267768 * 2
def baseEnd_7267768 : Nat := 3731858269365826057976149

theorem tailTrace_7267768 : CollatzResearch.WordTrace tailWord_7267768 prefixEnd_7267768 3731858269365826057976149 := by
  unfold tailWord_7267768
  simp only [CollatzResearch.WordTrace]
  refine ⟨132538637967062623399833979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176718183956083497866445305 132538637967062623399833979)
  ·
    refine ⟨198807956950593935099750969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132538637967062623399833979 198807956950593935099750969)
    ·
      refine ⟨149105967712945451324813227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198807956950593935099750969 149105967712945451324813227)
      ·
        refine ⟨223658951569418176987219841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149105967712945451324813227 223658951569418176987219841)
        ·
          refine ⟨167744213677063632740414881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223658951569418176987219841 167744213677063632740414881)
          ·
            refine ⟨125808160257797724555311161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167744213677063632740414881 125808160257797724555311161)
            ·
              refine ⟨94356120193348293416483371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125808160257797724555311161 94356120193348293416483371)
              ·
                refine ⟨141534180290022440124725057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94356120193348293416483371 141534180290022440124725057)
                ·
                  refine ⟨106150635217516830093543793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141534180290022440124725057 106150635217516830093543793)
                  ·
                    refine ⟨79612976413137622570157845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106150635217516830093543793 79612976413137622570157845)
                    ·
                      refine ⟨3731858269365826057976149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79612976413137622570157845 3731858269365826057976149)
                      ·
                        rfl

theorem cell23_7267768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_7267768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267768 prefixEnd_7267768 := by exact prefixLift 7267768
  have htrace : WordTrace (prefixWord ++ tailWord_7267768) baseStart_7267768 baseEnd_7267768 := by
    simpa [prefixWord, tailWord_7267768, baseEnd_7267768] using wordTrace_append hprefix tailTrace_7267768
  have hstable : (prefixWord ++ tailWord_7267768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267768).length < 2 ^ (prefixWord ++ tailWord_7267768).sum := by decide
  have hdescent : baseEnd_7267768 < baseStart_7267768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267809 : List Nat := [1, 2, 3, 1, 2, 3, 3, 2, 2, 1, 3]
def baseStart_7267809 : Nat := 118140960795 + 7267809 * 2 ^ 59
def prefixEnd_7267809 : Nat := 4983230072969 + 3 ^ 40 * 7267809 * 2
def baseEnd_7267809 : Nat := 3731879322072660397563461

theorem tailTrace_7267809 : CollatzResearch.WordTrace tailWord_7267809 prefixEnd_7267809 3731879322072660397563461 := by
  unfold tailWord_7267809
  simp only [CollatzResearch.WordTrace]
  refine ⟨265078771326976710801910481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176719180884651140534606987 265078771326976710801910481)
  ·
    refine ⟨198809078495232533101432861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265078771326976710801910481 198809078495232533101432861)
    ·
      refine ⟨74553404435712199913037323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198809078495232533101432861 74553404435712199913037323)
      ·
        refine ⟨111830106653568299869555985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74553404435712199913037323 111830106653568299869555985)
        ·
          refine ⟨83872579990176224902166989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111830106653568299869555985 83872579990176224902166989)
          ·
            refine ⟨31452217496316084338312621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83872579990176224902166989 31452217496316084338312621)
            ·
              refine ⟨11794581561118531626867233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31452217496316084338312621 11794581561118531626867233)
              ·
                refine ⟨8845936170838898720150425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11794581561118531626867233 8845936170838898720150425)
                ·
                  refine ⟨6634452128129174040112819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8845936170838898720150425 6634452128129174040112819)
                  ·
                    refine ⟨9951678192193761060169229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6634452128129174040112819 9951678192193761060169229)
                    ·
                      refine ⟨3731879322072660397563461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9951678192193761060169229 3731879322072660397563461)
                      ·
                        rfl

theorem cell23_7267809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 2, 1, 3].length) (baseStart_7267809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267809 prefixEnd_7267809 := by exact prefixLift 7267809
  have htrace : WordTrace (prefixWord ++ tailWord_7267809) baseStart_7267809 baseEnd_7267809 := by
    simpa [prefixWord, tailWord_7267809, baseEnd_7267809] using wordTrace_append hprefix tailTrace_7267809
  have hstable : (prefixWord ++ tailWord_7267809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267809).length < 2 ^ (prefixWord ++ tailWord_7267809).sum := by decide
  have hdescent : baseEnd_7267809 < baseStart_7267809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267825 : List Nat := [1, 2, 2, 2, 3, 2, 2, 1, 2, 6]
def baseStart_7267825 : Nat := 118140960795 + 7267825 * 2 ^ 59
def prefixEnd_7267825 : Nat := 4983230072969 + 3 ^ 40 * 7267825 * 2
def baseEnd_7267825 : Nat := 1243962512587710778321129

theorem tailTrace_7267825 : CollatzResearch.WordTrace tailWord_7267825 prefixEnd_7267825 1243962512587710778321129 := by
  unfold tailWord_7267825
  simp only [CollatzResearch.WordTrace]
  refine ⟨265079354894918745534492929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176719569929945830356328619 265079354894918745534492929)
  ·
    refine ⟨198809516171189059150869697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265079354894918745534492929 198809516171189059150869697)
    ·
      refine ⟨149107137128391794363152273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198809516171189059150869697 149107137128391794363152273)
      ·
        refine ⟨111830352846293845772364205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149107137128391794363152273 111830352846293845772364205)
        ·
          refine ⟨41936382317360192164636577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111830352846293845772364205 41936382317360192164636577)
          ·
            refine ⟨31452286738020144123477433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41936382317360192164636577 31452286738020144123477433)
            ·
              refine ⟨23589215053515108092608075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31452286738020144123477433 23589215053515108092608075)
              ·
                refine ⟨35383822580272662138912113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23589215053515108092608075 35383822580272662138912113)
                ·
                  refine ⟨26537866935204496604184085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35383822580272662138912113 26537866935204496604184085)
                  ·
                    refine ⟨1243962512587710778321129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26537866935204496604184085 1243962512587710778321129)
                    ·
                      rfl

theorem cell23_7267825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 6].length) (baseStart_7267825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267825 prefixEnd_7267825 := by exact prefixLift 7267825
  have htrace : WordTrace (prefixWord ++ tailWord_7267825) baseStart_7267825 baseEnd_7267825 := by
    simpa [prefixWord, tailWord_7267825, baseEnd_7267825] using wordTrace_append hprefix tailTrace_7267825
  have hstable : (prefixWord ++ tailWord_7267825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267825).length < 2 ^ (prefixWord ++ tailWord_7267825).sum := by decide
  have hdescent : baseEnd_7267825 < baseStart_7267825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267852 : List Nat := [2, 2, 1, 2, 5, 1, 1, 1, 2, 1, 5]
def baseStart_7267852 : Nat := 118140960795 + 7267852 * 2 ^ 59
def prefixEnd_7267852 : Nat := 4983230072969 + 3 ^ 40 * 7267852 * 2
def baseEnd_7267852 : Nat := 3731901401740803729325763

theorem tailTrace_7267852 : CollatzResearch.WordTrace tailWord_7267852 prefixEnd_7267852 3731901401740803729325763 := by
  unfold tailWord_7267852
  simp only [CollatzResearch.WordTrace]
  refine ⟨132540169832910464572862905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176720226443880619430483873 132540169832910464572862905)
  ·
    refine ⟨99405127374682848429647179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132540169832910464572862905 99405127374682848429647179)
    ·
      refine ⟨149107691062024272644470769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99405127374682848429647179 149107691062024272644470769)
      ·
        refine ⟨111830768296518204483353077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149107691062024272644470769 111830768296518204483353077)
        ·
          refine ⟨10484134527798581670314351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111830768296518204483353077 10484134527798581670314351)
          ·
            refine ⟨15726201791697872505471527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10484134527798581670314351 15726201791697872505471527)
            ·
              refine ⟨23589302687546808758207291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15726201791697872505471527 23589302687546808758207291)
              ·
                refine ⟨35383954031320213137310937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23589302687546808758207291 35383954031320213137310937)
                ·
                  refine ⟨26537965523490159852983203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35383954031320213137310937 26537965523490159852983203)
                  ·
                    refine ⟨39806948285235239779474805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26537965523490159852983203 39806948285235239779474805)
                    ·
                      refine ⟨3731901401740803729325763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39806948285235239779474805 3731901401740803729325763)
                      ·
                        rfl

theorem cell23_7267852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_7267852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267852 prefixEnd_7267852 := by exact prefixLift 7267852
  have htrace : WordTrace (prefixWord ++ tailWord_7267852) baseStart_7267852 baseEnd_7267852 := by
    simpa [prefixWord, tailWord_7267852, baseEnd_7267852] using wordTrace_append hprefix tailTrace_7267852
  have hstable : (prefixWord ++ tailWord_7267852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267852).length < 2 ^ (prefixWord ++ tailWord_7267852).sum := by decide
  have hdescent : baseEnd_7267852 < baseStart_7267852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267872 : List Nat := [2, 1, 1, 6, 1, 1, 3, 1, 7]
def baseStart_7267872 : Nat := 118140960795 + 7267872 * 2 ^ 59
def prefixEnd_7267872 : Nat := 4983230072969 + 3 ^ 40 * 7267872 * 2
def baseEnd_7267872 : Nat := 414656852372654850119519

theorem tailTrace_7267872 : CollatzResearch.WordTrace tailWord_7267872 prefixEnd_7267872 414656852372654850119519 := by
  unfold tailWord_7267872
  simp only [CollatzResearch.WordTrace]
  refine ⟨132540534562874236280726935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176720712750498981707635913 132540534562874236280726935)
  ·
    refine ⟨198810801844311354421090403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132540534562874236280726935 198810801844311354421090403)
    ·
      refine ⟨298216202766467031631635605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198810801844311354421090403 298216202766467031631635605)
      ·
        refine ⟨13978884504678142107732919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 298216202766467031631635605 13978884504678142107732919)
        ·
          refine ⟨20968326757017213161599379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13978884504678142107732919 20968326757017213161599379)
          ·
            refine ⟨31452490135525819742399069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20968326757017213161599379 31452490135525819742399069)
            ·
              refine ⟨11794683800822182403399651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31452490135525819742399069 11794683800822182403399651)
              ·
                refine ⟨17692025701233273605099477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11794683800822182403399651 17692025701233273605099477)
                ·
                  refine ⟨414656852372654850119519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17692025701233273605099477 414656852372654850119519)
                  ·
                    rfl

theorem cell23_7267872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 7].length) (baseStart_7267872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267872 prefixEnd_7267872 := by exact prefixLift 7267872
  have htrace : WordTrace (prefixWord ++ tailWord_7267872) baseStart_7267872 baseEnd_7267872 := by
    simpa [prefixWord, tailWord_7267872, baseEnd_7267872] using wordTrace_append hprefix tailTrace_7267872
  have hstable : (prefixWord ++ tailWord_7267872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267872).length < 2 ^ (prefixWord ++ tailWord_7267872).sum := by decide
  have hdescent : baseEnd_7267872 < baseStart_7267872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267882 : List Nat := [3, 1, 4, 1, 1, 1, 2, 1, 1, 5, 3]
def baseStart_7267882 : Nat := 118140960795 + 7267882 * 2 ^ 59
def prefixEnd_7267882 : Nat := 4983230072969 + 3 ^ 40 * 7267882 * 2
def baseEnd_7267882 : Nat := 3731916806160438611950625

theorem tailTrace_7267882 : CollatzResearch.WordTrace tailWord_7267882 prefixEnd_7267882 3731916806160438611950625 := by
  unfold tailWord_7267882
  simp only [CollatzResearch.WordTrace]
  refine ⟨66270358463928061067329475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176720955903808162846211933 66270358463928061067329475)
  ·
    refine ⟨99405537695892091600994213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66270358463928061067329475 99405537695892091600994213)
    ·
      refine ⟨18638538317979767175186415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99405537695892091600994213 18638538317979767175186415)
      ·
        refine ⟨27957807476969650762779623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18638538317979767175186415 27957807476969650762779623)
        ·
          refine ⟨41936711215454476144169435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27957807476969650762779623 41936711215454476144169435)
          ·
            refine ⟨62905066823181714216254153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41936711215454476144169435 62905066823181714216254153)
            ·
              refine ⟨47178800117386285662190615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62905066823181714216254153 47178800117386285662190615)
              ·
                refine ⟨70768200176079428493285923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47178800117386285662190615 70768200176079428493285923)
                ·
                  refine ⟨106152300264119142739928885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70768200176079428493285923 106152300264119142739928885)
                  ·
                    refine ⟨9951778149761169631868333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 106152300264119142739928885 9951778149761169631868333)
                    ·
                      refine ⟨3731916806160438611950625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9951778149761169631868333 3731916806160438611950625)
                      ·
                        rfl

theorem cell23_7267882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_7267882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267882 prefixEnd_7267882 := by exact prefixLift 7267882
  have htrace : WordTrace (prefixWord ++ tailWord_7267882) baseStart_7267882 baseEnd_7267882 := by
    simpa [prefixWord, tailWord_7267882, baseEnd_7267882] using wordTrace_append hprefix tailTrace_7267882
  have hstable : (prefixWord ++ tailWord_7267882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267882).length < 2 ^ (prefixWord ++ tailWord_7267882).sum := by decide
  have hdescent : baseEnd_7267882 < baseStart_7267882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267925 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 1, 5, 5]
def baseStart_7267925 : Nat := 118140960795 + 7267925 * 2 ^ 59
def prefixEnd_7267925 : Nat := 4983230072969 + 3 ^ 40 * 7267925 * 2
def baseEnd_7267925 : Nat := 3731938885828581943712927

theorem tailTrace_7267925 : CollatzResearch.WordTrace tailWord_7267925 prefixEnd_7267925 3731938885828581943712927 := by
  unfold tailWord_7267925
  simp only [CollatzResearch.WordTrace]
  refine ⟨265083002194556462613133229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176722001463037641742088819 265083002194556462613133229)
  ·
    refine ⟨99406125822958673479924961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265083002194556462613133229 99406125822958673479924961)
    ·
      refine ⟨74554594367219005109943721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99406125822958673479924961 74554594367219005109943721)
      ·
        refine ⟨55915945775414253832457791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74554594367219005109943721 55915945775414253832457791)
        ·
          refine ⟨83873918663121380748686687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55915945775414253832457791 83873918663121380748686687)
          ·
            refine ⟨125810877994682071123030031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83873918663121380748686687 125810877994682071123030031)
            ·
              refine ⟨188716316992023106684545047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125810877994682071123030031 188716316992023106684545047)
              ·
                refine ⟨283074475488034660026817571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188716316992023106684545047 283074475488034660026817571)
                ·
                  refine ⟨424611713232051990040226357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 283074475488034660026817571 424611713232051990040226357)
                  ·
                    refine ⟨39807348115504874066271221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 424611713232051990040226357 39807348115504874066271221)
                    ·
                      refine ⟨3731938885828581943712927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39807348115504874066271221 3731938885828581943712927)
                      ·
                        rfl

theorem cell23_7267925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_7267925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267925 prefixEnd_7267925 := by exact prefixLift 7267925
  have htrace : WordTrace (prefixWord ++ tailWord_7267925) baseStart_7267925 baseEnd_7267925 := by
    simpa [prefixWord, tailWord_7267925, baseEnd_7267925] using wordTrace_append hprefix tailTrace_7267925
  have hstable : (prefixWord ++ tailWord_7267925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267925).length < 2 ^ (prefixWord ++ tailWord_7267925).sum := by decide
  have hdescent : baseEnd_7267925 < baseStart_7267925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267935 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 4]
def baseStart_7267935 : Nat := 118140960795 + 7267935 * 2 ^ 59
def prefixEnd_7267935 : Nat := 4983230072969 + 3 ^ 40 * 7267935 * 2
def baseEnd_7267935 : Nat := 3731944020635126904587881

theorem tailTrace_7267935 : CollatzResearch.WordTrace tailWord_7267935 prefixEnd_7267935 3731944020635126904587881 := by
  unfold tailWord_7267935
  simp only [CollatzResearch.WordTrace]
  refine ⟨265083366924520234320997259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176722244616346822880664839 265083366924520234320997259)
  ·
    refine ⟨397625050386780351481495889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265083366924520234320997259 397625050386780351481495889)
    ·
      refine ⟨298218787790085263611121917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397625050386780351481495889 298218787790085263611121917)
      ·
        refine ⟨111832045421281973854170719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298218787790085263611121917 111832045421281973854170719)
        ·
          refine ⟨167748068131922960781256079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111832045421281973854170719 167748068131922960781256079)
          ·
            refine ⟨251622102197884441171884119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167748068131922960781256079 251622102197884441171884119)
            ·
              refine ⟨377433153296826661757826179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251622102197884441171884119 377433153296826661757826179)
              ·
                refine ⟨566149729945239992636739269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377433153296826661757826179 566149729945239992636739269)
                ·
                  refine ⟨106153074364732498619388613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 566149729945239992636739269 106153074364732498619388613)
                  ·
                    refine ⟨19903701443387343491135365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106153074364732498619388613 19903701443387343491135365)
                    ·
                      refine ⟨3731944020635126904587881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19903701443387343491135365 3731944020635126904587881)
                      ·
                        rfl

theorem cell23_7267935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_7267935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267935 prefixEnd_7267935 := by exact prefixLift 7267935
  have htrace : WordTrace (prefixWord ++ tailWord_7267935) baseStart_7267935 baseEnd_7267935 := by
    simpa [prefixWord, tailWord_7267935, baseEnd_7267935] using wordTrace_append hprefix tailTrace_7267935
  have hstable : (prefixWord ++ tailWord_7267935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267935).length < 2 ^ (prefixWord ++ tailWord_7267935).sum := by decide
  have hdescent : baseEnd_7267935 < baseStart_7267935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267939 : List Nat := [1, 1, 1, 5, 1, 4, 1, 1, 2, 4, 2]
def baseStart_7267939 : Nat := 118140960795 + 7267939 * 2 ^ 59
def prefixEnd_7267939 : Nat := 4983230072969 + 3 ^ 40 * 7267939 * 2
def baseEnd_7267939 : Nat := 3731946074557744888937863

theorem tailTrace_7267939 : CollatzResearch.WordTrace tailWord_7267939 prefixEnd_7267939 3731946074557744888937863 := by
  unfold tailWord_7267939
  simp only [CollatzResearch.WordTrace]
  refine ⟨265083512816505743004142871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176722341877670495336095247 265083512816505743004142871)
  ·
    refine ⟨397625269224758614506214307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265083512816505743004142871 397625269224758614506214307)
    ·
      refine ⟨596437903837137921759321461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397625269224758614506214307 596437903837137921759321461)
      ·
        refine ⟨55916053484731680164936387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 596437903837137921759321461 55916053484731680164936387)
        ·
          refine ⟨83874080227097520247404581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55916053484731680164936387 83874080227097520247404581)
          ·
            refine ⟨15726390042580785046388359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83874080227097520247404581 15726390042580785046388359)
            ·
              refine ⟨23589585063871177569582539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15726390042580785046388359 23589585063871177569582539)
              ·
                refine ⟨35384377595806766354373809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23589585063871177569582539 35384377595806766354373809)
                ·
                  refine ⟨26538283196855074765780357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35384377595806766354373809 26538283196855074765780357)
                  ·
                    refine ⟨4975928099410326518583817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26538283196855074765780357 4975928099410326518583817)
                    ·
                      refine ⟨3731946074557744888937863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4975928099410326518583817 3731946074557744888937863)
                      ·
                        rfl

theorem cell23_7267939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_7267939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267939 prefixEnd_7267939 := by exact prefixLift 7267939
  have htrace : WordTrace (prefixWord ++ tailWord_7267939) baseStart_7267939 baseEnd_7267939 := by
    simpa [prefixWord, tailWord_7267939, baseEnd_7267939] using wordTrace_append hprefix tailTrace_7267939
  have hstable : (prefixWord ++ tailWord_7267939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267939).length < 2 ^ (prefixWord ++ tailWord_7267939).sum := by decide
  have hdescent : baseEnd_7267939 < baseStart_7267939 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267982 : List Nat := [4, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6]
def baseStart_7267982 : Nat := 118140960795 + 7267982 * 2 ^ 59
def prefixEnd_7267982 : Nat := 4983230072969 + 3 ^ 40 * 7267982 * 2
def baseEnd_7267982 : Nat := 3731968154225888220700165

theorem tailTrace_7267982 : CollatzResearch.WordTrace tailWord_7267982 prefixEnd_7267982 3731968154225888220700165 := by
  unfold tailWord_7267982
  simp only [CollatzResearch.WordTrace]
  refine ⟨33135635144418745168494775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176723387436899974231972133 33135635144418745168494775)
  ·
    refine ⟨49703452716628117752742163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33135635144418745168494775 49703452716628117752742163)
    ·
      refine ⟨74555179074942176629113245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49703452716628117752742163 74555179074942176629113245)
      ·
        refine ⟨27958192153103316235917467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74555179074942176629113245 27958192153103316235917467)
        ·
          refine ⟨41937288229654974353876201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27958192153103316235917467 41937288229654974353876201)
          ·
            refine ⟨31452966172241230765407151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41937288229654974353876201 31452966172241230765407151)
            ·
              refine ⟨47179449258361846148110727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31452966172241230765407151 47179449258361846148110727)
              ·
                refine ⟨70769173887542769222166091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47179449258361846148110727 70769173887542769222166091)
                ·
                  refine ⟨106153760831314153833249137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70769173887542769222166091 106153760831314153833249137)
                  ·
                    refine ⟨79615320623485615374936853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106153760831314153833249137 79615320623485615374936853)
                    ·
                      refine ⟨3731968154225888220700165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79615320623485615374936853 3731968154225888220700165)
                      ·
                        rfl

theorem cell23_7267982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_7267982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267982 prefixEnd_7267982 := by exact prefixLift 7267982
  have htrace : WordTrace (prefixWord ++ tailWord_7267982) baseStart_7267982 baseEnd_7267982 := by
    simpa [prefixWord, tailWord_7267982, baseEnd_7267982] using wordTrace_append hprefix tailTrace_7267982
  have hstable : (prefixWord ++ tailWord_7267982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267982).length < 2 ^ (prefixWord ++ tailWord_7267982).sum := by decide
  have hdescent : baseEnd_7267982 < baseStart_7267982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267985 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 7]
def baseStart_7267985 : Nat := 118140960795 + 7267985 * 2 ^ 59
def prefixEnd_7267985 : Nat := 4983230072969 + 3 ^ 40 * 7267985 * 2
def baseEnd_7267985 : Nat := 3731969694667851708962651

theorem tailTrace_7267985 : CollatzResearch.WordTrace tailWord_7267985 prefixEnd_7267985 3731969694667851708962651 := by
  unfold tailWord_7267985
  simp only [CollatzResearch.WordTrace]
  refine ⟨265085190574339092860317409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176723460382892728573544939 265085190574339092860317409)
  ·
    refine ⟨198813892930754319645238057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265085190574339092860317409 198813892930754319645238057)
    ·
      refine ⟨149110419698065739733928543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198813892930754319645238057 149110419698065739733928543)
      ·
        refine ⟨223665629547098609600892815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149110419698065739733928543 223665629547098609600892815)
        ·
          refine ⟨335498444320647914401339223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223665629547098609600892815 335498444320647914401339223)
          ·
            refine ⟨503247666480971871602008835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335498444320647914401339223 503247666480971871602008835)
            ·
              refine ⟨754871499721457807403013253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503247666480971871602008835 754871499721457807403013253)
              ·
                refine ⟨141538406197773338888064985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 754871499721457807403013253 141538406197773338888064985)
                ·
                  refine ⟨106153804648330004166048739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141538406197773338888064985 106153804648330004166048739)
                  ·
                    refine ⟨159230706972495006249073109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106153804648330004166048739 159230706972495006249073109)
                    ·
                      refine ⟨3731969694667851708962651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 159230706972495006249073109 3731969694667851708962651)
                      ·
                        rfl

theorem cell23_7267985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_7267985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267985 prefixEnd_7267985 := by exact prefixLift 7267985
  have htrace : WordTrace (prefixWord ++ tailWord_7267985) baseStart_7267985 baseEnd_7267985 := by
    simpa [prefixWord, tailWord_7267985, baseEnd_7267985] using wordTrace_append hprefix tailTrace_7267985
  have hstable : (prefixWord ++ tailWord_7267985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267985).length < 2 ^ (prefixWord ++ tailWord_7267985).sum := by decide
  have hdescent : baseEnd_7267985 < baseStart_7267985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7267996 : List Nat := [2, 2, 3, 2, 3, 1, 3, 1, 6]
def baseStart_7267996 : Nat := 118140960795 + 7267996 * 2 ^ 59
def prefixEnd_7267996 : Nat := 4983230072969 + 3 ^ 40 * 7267996 * 2
def baseEnd_7267996 : Nat := 414663926995005685102789

theorem tailTrace_7267996 : CollatzResearch.WordTrace tailWord_7267996 prefixEnd_7267996 414663926995005685102789 := by
  unfold tailWord_7267996
  simp only [CollatzResearch.WordTrace]
  refine ⟨132542795888649620869483921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176723727851532827825978561 132542795888649620869483921)
  ·
    refine ⟨99407096916487215652112941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132542795888649620869483921 99407096916487215652112941)
    ·
      refine ⟨37277661343682705869542353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99407096916487215652112941 37277661343682705869542353)
      ·
        refine ⟨27958246007762029402156765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37277661343682705869542353 27958246007762029402156765)
        ·
          refine ⟨10484342252910761025808787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27958246007762029402156765 10484342252910761025808787)
          ·
            refine ⟨15726513379366141538713181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10484342252910761025808787 15726513379366141538713181)
            ·
              refine ⟨5897442517262303077017443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15726513379366141538713181 5897442517262303077017443)
              ·
                refine ⟨8846163775893454615526165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5897442517262303077017443 8846163775893454615526165)
                ·
                  refine ⟨414663926995005685102789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8846163775893454615526165 414663926995005685102789)
                  ·
                    rfl

theorem cell23_7267996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 6].length) (baseStart_7267996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7267996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7267996 prefixEnd_7267996 := by exact prefixLift 7267996
  have htrace : WordTrace (prefixWord ++ tailWord_7267996) baseStart_7267996 baseEnd_7267996 := by
    simpa [prefixWord, tailWord_7267996, baseEnd_7267996] using wordTrace_append hprefix tailTrace_7267996
  have hstable : (prefixWord ++ tailWord_7267996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7267996).length < 2 ^ (prefixWord ++ tailWord_7267996).sum := by decide
  have hdescent : baseEnd_7267996 < baseStart_7267996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7267996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268023 : List Nat := [1, 1, 3, 1, 5, 1, 3, 3, 1, 1, 3]
def baseStart_7268023 : Nat := 118140960795 + 7268023 * 2 ^ 59
def prefixEnd_7268023 : Nat := 4983230072969 + 3 ^ 40 * 7268023 * 2
def baseEnd_7268023 : Nat := 3731989206932722560287477

theorem tailTrace_7268023 : CollatzResearch.WordTrace tailWord_7268023 prefixEnd_7268023 3731989206932722560287477 := by
  unfold tailWord_7268023
  simp only [CollatzResearch.WordTrace]
  refine ⟨265086576548201425350200723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176724384365467616900133815 265086576548201425350200723)
  ·
    refine ⟨397629864822302138025301085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265086576548201425350200723 397629864822302138025301085)
    ·
      refine ⟨149111199308363301759487907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 397629864822302138025301085 149111199308363301759487907)
      ·
        refine ⟨223666798962544952639231861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149111199308363301759487907 223666798962544952639231861)
        ·
          refine ⟨20968762402738589309927987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 223666798962544952639231861 20968762402738589309927987)
          ·
            refine ⟨31453143604107883964891981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20968762402738589309927987 31453143604107883964891981)
            ·
              refine ⟨11794928851540456486834493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31453143604107883964891981 11794928851540456486834493)
              ·
                refine ⟨4423098319327671182562935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11794928851540456486834493 4423098319327671182562935)
                ·
                  refine ⟨6634647478991506773844403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4423098319327671182562935 6634647478991506773844403)
                  ·
                    refine ⟨9951971218487260160766605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6634647478991506773844403 9951971218487260160766605)
                    ·
                      refine ⟨3731989206932722560287477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9951971218487260160766605 3731989206932722560287477)
                      ·
                        rfl

theorem cell23_7268023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 3, 1, 1, 3].length) (baseStart_7268023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268023 prefixEnd_7268023 := by exact prefixLift 7268023
  have htrace : WordTrace (prefixWord ++ tailWord_7268023) baseStart_7268023 baseEnd_7268023 := by
    simpa [prefixWord, tailWord_7268023, baseEnd_7268023] using wordTrace_append hprefix tailTrace_7268023
  have hstable : (prefixWord ++ tailWord_7268023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268023).length < 2 ^ (prefixWord ++ tailWord_7268023).sum := by decide
  have hdescent : baseEnd_7268023 < baseStart_7268023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268029 : List Nat := [1, 4, 1, 2, 1, 2, 1, 5, 1, 1, 4]
def baseStart_7268029 : Nat := 118140960795 + 7268029 * 2 ^ 59
def prefixEnd_7268029 : Nat := 4983230072969 + 3 ^ 40 * 7268029 * 2
def baseEnd_7268029 : Nat := 3731992287816649536812449

theorem tailTrace_7268029 : CollatzResearch.WordTrace tailWord_7268029 prefixEnd_7268029 3731992287816649536812449 := by
  unfold tailWord_7268029
  simp only [CollatzResearch.WordTrace]
  refine ⟨265086795386179688374919141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176724530257453125583279427 265086795386179688374919141)
  ·
    refine ⟨49703774134908691570297339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265086795386179688374919141 49703774134908691570297339)
    ·
      refine ⟨74555661202363037355446009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49703774134908691570297339 74555661202363037355446009)
      ·
        refine ⟨55916745901772278016584507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74555661202363037355446009 55916745901772278016584507)
        ·
          refine ⟨83875118852658417024876761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55916745901772278016584507 83875118852658417024876761)
          ·
            refine ⟨62906339139493812768657571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83875118852658417024876761 62906339139493812768657571)
            ·
              refine ⟨94359508709240719152986357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62906339139493812768657571 94359508709240719152986357)
              ·
                refine ⟨8846203941491317420592471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94359508709240719152986357 8846203941491317420592471)
                ·
                  refine ⟨13269305912236976130888707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8846203941491317420592471 13269305912236976130888707)
                  ·
                    refine ⟨19903958868355464196333061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13269305912236976130888707 19903958868355464196333061)
                    ·
                      refine ⟨3731992287816649536812449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19903958868355464196333061 3731992287816649536812449)
                      ·
                        rfl

theorem cell23_7268029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_7268029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268029 prefixEnd_7268029 := by exact prefixLift 7268029
  have htrace : WordTrace (prefixWord ++ tailWord_7268029) baseStart_7268029 baseEnd_7268029 := by
    simpa [prefixWord, tailWord_7268029, baseEnd_7268029] using wordTrace_append hprefix tailTrace_7268029
  have hstable : (prefixWord ++ tailWord_7268029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268029).length < 2 ^ (prefixWord ++ tailWord_7268029).sum := by decide
  have hdescent : baseEnd_7268029 < baseStart_7268029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268034 : List Nat := [3, 5, 1, 2, 1, 1, 3, 2, 1, 4]
def baseStart_7268034 : Nat := 118140960795 + 7268034 * 2 ^ 59
def prefixEnd_7268034 : Nat := 4983230072969 + 3 ^ 40 * 7268034 * 2
def baseEnd_7268034 : Nat := 1243998285073307339083309

theorem tailTrace_7268034 : CollatzResearch.WordTrace tailWord_7268034 prefixEnd_7268034 1243998285073307339083309 := by
  unfold tailWord_7268034
  simp only [CollatzResearch.WordTrace]
  refine ⟨66271744437790393557212789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176724651834107716152567437 66271744437790393557212789)
  ·
    refine ⟨6212976041042849395988699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66271744437790393557212789 6212976041042849395988699)
    ·
      refine ⟨9319464061564274093983049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6212976041042849395988699 9319464061564274093983049)
      ·
        refine ⟨6989598046173205570487287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9319464061564274093983049 6989598046173205570487287)
        ·
          refine ⟨10484397069259808355730931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6989598046173205570487287 10484397069259808355730931)
          ·
            refine ⟨15726595603889712533596397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10484397069259808355730931 15726595603889712533596397)
            ·
              refine ⟨5897473351458642200098649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15726595603889712533596397 5897473351458642200098649)
              ·
                refine ⟨4423105013593981650073987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5897473351458642200098649 4423105013593981650073987)
                ·
                  refine ⟨6634657520390972475110981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4423105013593981650073987 6634657520390972475110981)
                  ·
                    refine ⟨1243998285073307339083309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6634657520390972475110981 1243998285073307339083309)
                    ·
                      rfl

theorem cell23_7268034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_7268034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268034 prefixEnd_7268034 := by exact prefixLift 7268034
  have htrace : WordTrace (prefixWord ++ tailWord_7268034) baseStart_7268034 baseEnd_7268034 := by
    simpa [prefixWord, tailWord_7268034, baseEnd_7268034] using wordTrace_append hprefix tailTrace_7268034
  have hstable : (prefixWord ++ tailWord_7268034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268034).length < 2 ^ (prefixWord ++ tailWord_7268034).sum := by decide
  have hdescent : baseEnd_7268034 < baseStart_7268034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268039 : List Nat := [1, 1, 4, 1, 1, 1, 4, 4, 2, 4]
def baseStart_7268039 : Nat := 118140960795 + 7268039 * 2 ^ 59
def prefixEnd_7268039 : Nat := 4983230072969 + 3 ^ 40 * 7268039 * 2
def baseEnd_7268039 : Nat := 1243999140874398165895801

theorem tailTrace_7268039 : CollatzResearch.WordTrace tailWord_7268039 prefixEnd_7268039 1243999140874398165895801 := by
  unfold tailWord_7268039
  simp only [CollatzResearch.WordTrace]
  refine ⟨265087160116143460082783171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176724773410762306721855447 265087160116143460082783171)
  ·
    refine ⟨397630740174215190124174757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265087160116143460082783171 397630740174215190124174757)
    ·
      refine ⟨74555763782665348148282767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 397630740174215190124174757 74555763782665348148282767)
      ·
        refine ⟨111833645673998022222424151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74555763782665348148282767 111833645673998022222424151)
        ·
          refine ⟨167750468510997033333636227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111833645673998022222424151 167750468510997033333636227)
          ·
            refine ⟨251625702766495550000454341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167750468510997033333636227 251625702766495550000454341)
            ·
              refine ⟨47179819268717915625085189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 251625702766495550000454341 47179819268717915625085189)
              ·
                refine ⟨8846216112884609179703473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47179819268717915625085189 8846216112884609179703473)
                ·
                  refine ⟨6634662084663456884777605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8846216112884609179703473 6634662084663456884777605)
                  ·
                    refine ⟨1243999140874398165895801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6634662084663456884777605 1243999140874398165895801)
                    ·
                      rfl

theorem cell23_7268039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_7268039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268039 prefixEnd_7268039 := by exact prefixLift 7268039
  have htrace : WordTrace (prefixWord ++ tailWord_7268039) baseStart_7268039 baseEnd_7268039 := by
    simpa [prefixWord, tailWord_7268039, baseEnd_7268039] using wordTrace_append hprefix tailTrace_7268039
  have hstable : (prefixWord ++ tailWord_7268039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268039).length < 2 ^ (prefixWord ++ tailWord_7268039).sum := by decide
  have hdescent : baseEnd_7268039 < baseStart_7268039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268060 : List Nat := [2, 2, 5, 1, 3, 1, 1, 2, 1, 5]
def baseStart_7268060 : Nat := 118140960795 + 7268060 * 2 ^ 59
def prefixEnd_7268060 : Nat := 4983230072969 + 3 ^ 40 * 7268060 * 2
def baseEnd_7268060 : Nat := 1244002735238979638508269

theorem tailTrace_7268060 : CollatzResearch.WordTrace tailWord_7268060 prefixEnd_7268060 1244002735238979638508269 := by
  unfold tailWord_7268060
  simp only [CollatzResearch.WordTrace]
  refine ⟨132543963024533690334648817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176725284032711587112865089 132543963024533690334648817)
  ·
    refine ⟨99407972268400267750986613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132543963024533690334648817 99407972268400267750986613)
    ·
      refine ⟨9319497400162525101654995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99407972268400267750986613 9319497400162525101654995)
      ·
        refine ⟨13979246100243787652482493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9319497400162525101654995 13979246100243787652482493)
        ·
          refine ⟨5242217287591420369680935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13979246100243787652482493 5242217287591420369680935)
          ·
            refine ⟨7863325931387130554521403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5242217287591420369680935 7863325931387130554521403)
            ·
              refine ⟨11794988897080695831782105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7863325931387130554521403 11794988897080695831782105)
              ·
                refine ⟨8846241672810521873836579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11794988897080695831782105 8846241672810521873836579)
                ·
                  refine ⟨13269362509215782810754869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8846241672810521873836579 13269362509215782810754869)
                  ·
                    refine ⟨1244002735238979638508269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13269362509215782810754869 1244002735238979638508269)
                    ·
                      rfl

theorem cell23_7268060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_7268060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268060 prefixEnd_7268060 := by exact prefixLift 7268060
  have htrace : WordTrace (prefixWord ++ tailWord_7268060) baseStart_7268060 baseEnd_7268060 := by
    simpa [prefixWord, tailWord_7268060, baseEnd_7268060] using wordTrace_append hprefix tailTrace_7268060
  have hstable : (prefixWord ++ tailWord_7268060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268060).length < 2 ^ (prefixWord ++ tailWord_7268060).sum := by decide
  have hdescent : baseEnd_7268060 < baseStart_7268060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268079 : List Nat := [1, 1, 2, 1, 5, 1, 3, 2, 1, 3, 3]
def baseStart_7268079 : Nat := 118140960795 + 7268079 * 2 ^ 59
def prefixEnd_7268079 : Nat := 4983230072969 + 3 ^ 40 * 7268079 * 2
def baseEnd_7268079 : Nat := 3732017961849374341187219

theorem tailTrace_7268079 : CollatzResearch.WordTrace tailWord_7268079 prefixEnd_7268079 3732017961849374341187219 := by
  unfold tailWord_7268079
  simp only [CollatzResearch.WordTrace]
  refine ⟨265088619035998546914239291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176725746023999031276159527 265088619035998546914239291)
  ·
    refine ⟨397632928553997820371358937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265088619035998546914239291 397632928553997820371358937)
    ·
      refine ⟨298224696415498365278519203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397632928553997820371358937 298224696415498365278519203)
      ·
        refine ⟨447337044623247547917778805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298224696415498365278519203 447337044623247547917778805)
        ·
          refine ⟨41937847933429457617291763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 447337044623247547917778805 41937847933429457617291763)
          ·
            refine ⟨62906771900144186425937645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41937847933429457617291763 62906771900144186425937645)
            ·
              refine ⟨23590039462554069909726617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62906771900144186425937645 23590039462554069909726617)
              ·
                refine ⟨17692529596915552432294963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23590039462554069909726617 17692529596915552432294963)
                ·
                  refine ⟨26538794395373328648442445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17692529596915552432294963 26538794395373328648442445)
                  ·
                    refine ⟨9952047898264998243165917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26538794395373328648442445 9952047898264998243165917)
                    ·
                      refine ⟨3732017961849374341187219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9952047898264998243165917 3732017961849374341187219)
                      ·
                        rfl

theorem cell23_7268079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 3, 3].length) (baseStart_7268079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268079 prefixEnd_7268079 := by exact prefixLift 7268079
  have htrace : WordTrace (prefixWord ++ tailWord_7268079) baseStart_7268079 baseEnd_7268079 := by
    simpa [prefixWord, tailWord_7268079, baseEnd_7268079] using wordTrace_append hprefix tailTrace_7268079
  have hstable : (prefixWord ++ tailWord_7268079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268079).length < 2 ^ (prefixWord ++ tailWord_7268079).sum := by decide
  have hdescent : baseEnd_7268079 < baseStart_7268079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268106 : List Nat := [3, 1, 2, 2, 1, 3, 1, 2, 3, 3, 2]
def baseStart_7268106 : Nat := 118140960795 + 7268106 * 2 ^ 59
def prefixEnd_7268106 : Nat := 4983230072969 + 3 ^ 40 * 7268106 * 2
def baseEnd_7268106 : Nat := 3732031825827045735549595

theorem tailTrace_7268106 : CollatzResearch.WordTrace tailWord_7268106 prefixEnd_7268106 3732031825827045735549595 := by
  unfold tailWord_7268106
  simp only [CollatzResearch.WordTrace]
  refine ⟨66272400951725182631368043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176726402537933820350314781 66272400951725182631368043)
  ·
    refine ⟨99408601427587773947052065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66272400951725182631368043 99408601427587773947052065)
    ·
      refine ⟨74556451070690830460289049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99408601427587773947052065 74556451070690830460289049)
      ·
        refine ⟨55917338303018122845216787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74556451070690830460289049 55917338303018122845216787)
        ·
          refine ⟨83876007454527184267825181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55917338303018122845216787 83876007454527184267825181)
          ·
            refine ⟨31453502795447694100434443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83876007454527184267825181 31453502795447694100434443)
            ·
              refine ⟨47180254193171541150651665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31453502795447694100434443 47180254193171541150651665)
              ·
                refine ⟨35385190644878655862988749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47180254193171541150651665 35385190644878655862988749)
                ·
                  refine ⟨13269446491829495948620781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35385190644878655862988749 13269446491829495948620781)
                  ·
                    refine ⟨4976042434436060980732793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13269446491829495948620781 4976042434436060980732793)
                    ·
                      refine ⟨3732031825827045735549595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4976042434436060980732793 3732031825827045735549595)
                      ·
                        rfl

theorem cell23_7268106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_7268106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268106 prefixEnd_7268106 := by exact prefixLift 7268106
  have htrace : WordTrace (prefixWord ++ tailWord_7268106) baseStart_7268106 baseEnd_7268106 := by
    simpa [prefixWord, tailWord_7268106, baseEnd_7268106] using wordTrace_append hprefix tailTrace_7268106
  have hstable : (prefixWord ++ tailWord_7268106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268106).length < 2 ^ (prefixWord ++ tailWord_7268106).sum := by decide
  have hdescent : baseEnd_7268106 < baseStart_7268106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268140 : List Nat := [2, 2, 1, 1, 1, 7, 2, 1, 1, 3, 2]
def baseStart_7268140 : Nat := 118140960795 + 7268140 * 2 ^ 59
def prefixEnd_7268140 : Nat := 4983230072969 + 3 ^ 40 * 7268140 * 2
def baseEnd_7268140 : Nat := 3732049284169298602524439

theorem tailTrace_7268140 : CollatzResearch.WordTrace tailWord_7268140 prefixEnd_7268140 3732049284169298602524439 := by
  unfold tailWord_7268140
  simp only [CollatzResearch.WordTrace]
  refine ⟨132545421944388777166104937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176727229259185036221473249 132545421944388777166104937)
  ·
    refine ⟨99409066458291582874578703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132545421944388777166104937 99409066458291582874578703)
    ·
      refine ⟨149113599687437374311868055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99409066458291582874578703 149113599687437374311868055)
      ·
        refine ⟨223670399531156061467802083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149113599687437374311868055 223670399531156061467802083)
        ·
          refine ⟨335505599296734092201703125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223670399531156061467802083 335505599296734092201703125)
          ·
            refine ⟨7863412483517205285977417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 335505599296734092201703125 7863412483517205285977417)
            ·
              refine ⟨5897559362637903964483063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7863412483517205285977417 5897559362637903964483063)
              ·
                refine ⟨8846339043956855946724595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5897559362637903964483063 8846339043956855946724595)
                ·
                  refine ⟨13269508565935283920086893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8846339043956855946724595 13269508565935283920086893)
                  ·
                    refine ⟨4976065712225731470032585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13269508565935283920086893 4976065712225731470032585)
                    ·
                      refine ⟨3732049284169298602524439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4976065712225731470032585 3732049284169298602524439)
                      ·
                        rfl

theorem cell23_7268140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 3, 2].length) (baseStart_7268140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268140 prefixEnd_7268140 := by exact prefixLift 7268140
  have htrace : WordTrace (prefixWord ++ tailWord_7268140) baseStart_7268140 baseEnd_7268140 := by
    simpa [prefixWord, tailWord_7268140, baseEnd_7268140] using wordTrace_append hprefix tailTrace_7268140
  have hstable : (prefixWord ++ tailWord_7268140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268140).length < 2 ^ (prefixWord ++ tailWord_7268140).sum := by decide
  have hdescent : baseEnd_7268140 < baseStart_7268140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268169 : List Nat := [1, 2, 1, 1, 2, 4, 1, 3, 2, 3, 3]
def baseStart_7268169 : Nat := 118140960795 + 7268169 * 2 ^ 59
def prefixEnd_7268169 : Nat := 4983230072969 + 3 ^ 40 * 7268169 * 2
def baseEnd_7268169 : Nat := 3732064175108278989061805

theorem tailTrace_7268169 : CollatzResearch.WordTrace tailWord_7268169 prefixEnd_7268169 3732064175108278989061805 := by
  unfold tailWord_7268169
  simp only [CollatzResearch.WordTrace]
  refine ⟨265091901605672492285015561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176727934403781661523343707 265091901605672492285015561)
  ·
    refine ⟨198818926204254369213761671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265091901605672492285015561 198818926204254369213761671)
    ·
      refine ⟨298228389306381553820642507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198818926204254369213761671 298228389306381553820642507)
      ·
        refine ⟨447342583959572330730963761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298228389306381553820642507 447342583959572330730963761)
        ·
          refine ⟨335506937969679248048222821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447342583959572330730963761 335506937969679248048222821)
          ·
            refine ⟨62907550869314859009041779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 335506937969679248048222821 62907550869314859009041779)
            ·
              refine ⟨94361326303972288513562669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62907550869314859009041779 94361326303972288513562669)
              ·
                refine ⟨35385497363989608192586001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94361326303972288513562669 35385497363989608192586001)
                ·
                  refine ⟨26539123022992206144439501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35385497363989608192586001 26539123022992206144439501)
                  ·
                    refine ⟨9952171133622077304164813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26539123022992206144439501 9952171133622077304164813)
                    ·
                      refine ⟨3732064175108278989061805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9952171133622077304164813 3732064175108278989061805)
                      ·
                        rfl

theorem cell23_7268169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 3, 3].length) (baseStart_7268169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268169 prefixEnd_7268169 := by exact prefixLift 7268169
  have htrace : WordTrace (prefixWord ++ tailWord_7268169) baseStart_7268169 baseEnd_7268169 := by
    simpa [prefixWord, tailWord_7268169, baseEnd_7268169] using wordTrace_append hprefix tailTrace_7268169
  have hstable : (prefixWord ++ tailWord_7268169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268169).length < 2 ^ (prefixWord ++ tailWord_7268169).sum := by decide
  have hdescent : baseEnd_7268169 < baseStart_7268169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268170 : List Nat := [3, 1, 2, 1, 1, 1, 7, 1, 2, 2, 2]
def baseStart_7268170 : Nat := 118140960795 + 7268170 * 2 ^ 59
def prefixEnd_7268170 : Nat := 4983230072969 + 3 ^ 40 * 7268170 * 2
def baseEnd_7268170 : Nat := 3732064688588933485149301

theorem tailTrace_7268170 : CollatzResearch.WordTrace tailWord_7268170 prefixEnd_7268170 3732064688588933485149301 := by
  unfold tailWord_7268170
  simp only [CollatzResearch.WordTrace]
  refine ⟨66272984519667217363950491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176727958719112579637201309 66272984519667217363950491)
  ·
    refine ⟨99409476779500826045925737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66272984519667217363950491 99409476779500826045925737)
    ·
      refine ⟨74557107584625619534444303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99409476779500826045925737 74557107584625619534444303)
      ·
        refine ⟨111835661376938429301666455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74557107584625619534444303 111835661376938429301666455)
        ·
          refine ⟨167753492065407643952499683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111835661376938429301666455 167753492065407643952499683)
          ·
            refine ⟨251630238098111465928749525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167753492065407643952499683 251630238098111465928749525)
            ·
              refine ⟨5897583705424487482705067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 251630238098111465928749525 5897583705424487482705067)
              ·
                refine ⟨8846375558136731224057601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5897583705424487482705067 8846375558136731224057601)
                ·
                  refine ⟨6634781668602548418043201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8846375558136731224057601 6634781668602548418043201)
                  ·
                    refine ⟨4976086251451911313532401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6634781668602548418043201 4976086251451911313532401)
                    ·
                      refine ⟨3732064688588933485149301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4976086251451911313532401 3732064688588933485149301)
                      ·
                        rfl

theorem cell23_7268170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 2, 2, 2].length) (baseStart_7268170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268170 prefixEnd_7268170 := by exact prefixLift 7268170
  have htrace : WordTrace (prefixWord ++ tailWord_7268170) baseStart_7268170 baseEnd_7268170 := by
    simpa [prefixWord, tailWord_7268170, baseEnd_7268170] using wordTrace_append hprefix tailTrace_7268170
  have hstable : (prefixWord ++ tailWord_7268170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268170).length < 2 ^ (prefixWord ++ tailWord_7268170).sum := by decide
  have hdescent : baseEnd_7268170 < baseStart_7268170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268199 : List Nat := [1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 5]
def baseStart_7268199 : Nat := 118140960795 + 7268199 * 2 ^ 59
def prefixEnd_7268199 : Nat := 4983230072969 + 3 ^ 40 * 7268199 * 2
def baseEnd_7268199 : Nat := 3732079579527913871686667

theorem tailTrace_7268199 : CollatzResearch.WordTrace tailWord_7268199 prefixEnd_7268199 3732079579527913871686667 := by
  unfold tailWord_7268199
  simp only [CollatzResearch.WordTrace]
  refine ⟨265092995795563807408607651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176728663863709204939071767 265092995795563807408607651)
  ·
    refine ⟨397639493693345711112911477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265092995795563807408607651 397639493693345711112911477)
    ·
      refine ⟨37278702533751160416835451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 397639493693345711112911477 37278702533751160416835451)
      ·
        refine ⟨55918053800626740625253177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37278702533751160416835451 55918053800626740625253177)
        ·
          refine ⟨41938540350470055468939883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55918053800626740625253177 41938540350470055468939883)
          ·
            refine ⟨62907810525705083203409825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41938540350470055468939883 62907810525705083203409825)
            ·
              refine ⟨47180857894278812402557369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62907810525705083203409825 47180857894278812402557369)
              ·
                refine ⟨35385643420709109301918027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47180857894278812402557369 35385643420709109301918027)
                ·
                  refine ⟨53078465131063663952877041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35385643420709109301918027 53078465131063663952877041)
                  ·
                    refine ⟨39808848848297747964657781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53078465131063663952877041 39808848848297747964657781)
                    ·
                      refine ⟨3732079579527913871686667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39808848848297747964657781 3732079579527913871686667)
                      ·
                        rfl

theorem cell23_7268199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_7268199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268199 prefixEnd_7268199 := by exact prefixLift 7268199
  have htrace : WordTrace (prefixWord ++ tailWord_7268199) baseStart_7268199 baseEnd_7268199 := by
    simpa [prefixWord, tailWord_7268199, baseEnd_7268199] using wordTrace_append hprefix tailTrace_7268199
  have hstable : (prefixWord ++ tailWord_7268199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268199).length < 2 ^ (prefixWord ++ tailWord_7268199).sum := by decide
  have hdescent : baseEnd_7268199 < baseStart_7268199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268206 : List Nat := [4, 1, 2, 3, 1, 1, 1, 1, 4, 5]
def baseStart_7268206 : Nat := 118140960795 + 7268206 * 2 ^ 59
def prefixEnd_7268206 : Nat := 4983230072969 + 3 ^ 40 * 7268206 * 2
def baseEnd_7268206 : Nat := 1244027724630831781433045

theorem tailTrace_7268206 : CollatzResearch.WordTrace tailWord_7268206 prefixEnd_7268206 1244027724630831781433045 := by
  unfold tailWord_7268206
  simp only [CollatzResearch.WordTrace]
  refine ⟨33136656388317305950514059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176728834071025631736074981 33136656388317305950514059)
  ·
    refine ⟨49704984582475958925771089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33136656388317305950514059 49704984582475958925771089)
    ·
      refine ⟨37278738436856969194328317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49704984582475958925771089 37278738436856969194328317)
      ·
        refine ⟨13979526913821363447873119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37278738436856969194328317 13979526913821363447873119)
        ·
          refine ⟨20969290370732045171809679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13979526913821363447873119 20969290370732045171809679)
          ·
            refine ⟨31453935556098067757714519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20969290370732045171809679 31453935556098067757714519)
            ·
              refine ⟨47180903334147101636571779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31453935556098067757714519 47180903334147101636571779)
              ·
                refine ⟨70771355001220652454857669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47180903334147101636571779 70771355001220652454857669)
                ·
                  refine ⟨13269629062728872335285813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70771355001220652454857669 13269629062728872335285813)
                  ·
                    refine ⟨1244027724630831781433045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13269629062728872335285813 1244027724630831781433045)
                    ·
                      rfl

theorem cell23_7268206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_7268206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268206 prefixEnd_7268206 := by exact prefixLift 7268206
  have htrace : WordTrace (prefixWord ++ tailWord_7268206) baseStart_7268206 baseEnd_7268206 := by
    simpa [prefixWord, tailWord_7268206, baseEnd_7268206] using wordTrace_append hprefix tailTrace_7268206
  have hstable : (prefixWord ++ tailWord_7268206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268206).length < 2 ^ (prefixWord ++ tailWord_7268206).sum := by decide
  have hdescent : baseEnd_7268206 < baseStart_7268206 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268263 : List Nat := [1, 1, 6, 1, 2, 1, 2, 2, 2, 2, 3]
def baseStart_7268263 : Nat := 118140960795 + 7268263 * 2 ^ 59
def prefixEnd_7268263 : Nat := 4983230072969 + 3 ^ 40 * 7268263 * 2
def baseEnd_7268263 : Nat := 3732112442289801621286373

theorem tailTrace_7268263 : CollatzResearch.WordTrace tailWord_7268263 prefixEnd_7268263 3732112442289801621286373 := by
  unfold tailWord_7268263
  simp only [CollatzResearch.WordTrace]
  refine ⟨265095330067331946338937443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176730220044887964225958295 265095330067331946338937443)
  ·
    refine ⟨397642995100997919508406165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265095330067331946338937443 397642995100997919508406165)
    ·
      refine ⟨18639515395359277476956539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 397642995100997919508406165 18639515395359277476956539)
      ·
        refine ⟨27959273093038916215434809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18639515395359277476956539 27959273093038916215434809)
        ·
          refine ⟨20969454819779187161576107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27959273093038916215434809 20969454819779187161576107)
          ·
            refine ⟨31454182229668780742364161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20969454819779187161576107 31454182229668780742364161)
            ·
              refine ⟨23590636672251585556773121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31454182229668780742364161 23590636672251585556773121)
              ·
                refine ⟨17692977504188689167579841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23590636672251585556773121 17692977504188689167579841)
                ·
                  refine ⟨13269733128141516875684881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17692977504188689167579841 13269733128141516875684881)
                  ·
                    refine ⟨9952299846106137656763661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13269733128141516875684881 9952299846106137656763661)
                    ·
                      refine ⟨3732112442289801621286373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9952299846106137656763661 3732112442289801621286373)
                      ·
                        rfl

theorem cell23_7268263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_7268263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268263 prefixEnd_7268263 := by exact prefixLift 7268263
  have htrace : WordTrace (prefixWord ++ tailWord_7268263) baseStart_7268263 baseEnd_7268263 := by
    simpa [prefixWord, tailWord_7268263, baseEnd_7268263] using wordTrace_append hprefix tailTrace_7268263
  have hstable : (prefixWord ++ tailWord_7268263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268263).length < 2 ^ (prefixWord ++ tailWord_7268263).sum := by decide
  have hdescent : baseEnd_7268263 < baseStart_7268263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268296 : List Nat := [2, 1, 3, 1, 4, 1, 2, 1, 3, 5]
def baseStart_7268296 : Nat := 118140960795 + 7268296 * 2 ^ 59
def prefixEnd_7268296 : Nat := 4983230072969 + 3 ^ 40 * 7268296 * 2
def baseEnd_7268296 : Nat := 1244043129050466664057907

theorem tailTrace_7268296 : CollatzResearch.WordTrace tailWord_7268296 prefixEnd_7268296 1244043129050466664057907 := by
  unfold tailWord_7268296
  simp only [CollatzResearch.WordTrace]
  refine ⟨132548266838106196487444371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176731022450808261983259161 132548266838106196487444371)
  ·
    refine ⟨198822400257159294731166557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132548266838106196487444371 198822400257159294731166557)
    ·
      refine ⟨74558400096434735524187459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198822400257159294731166557 74558400096434735524187459)
      ·
        refine ⟨111837600144652103286281189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74558400096434735524187459 111837600144652103286281189)
        ·
          refine ⟨20969550027122269366177723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111837600144652103286281189 20969550027122269366177723)
          ·
            refine ⟨31454325040683404049266585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20969550027122269366177723 31454325040683404049266585)
            ·
              refine ⟨23590743780512553036949939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31454325040683404049266585 23590743780512553036949939)
              ·
                refine ⟨35386115670768829555424909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23590743780512553036949939 35386115670768829555424909)
                ·
                  refine ⟨13269793376538311083284341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35386115670768829555424909 13269793376538311083284341)
                  ·
                    refine ⟨1244043129050466664057907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13269793376538311083284341 1244043129050466664057907)
                    ·
                      rfl

theorem cell23_7268296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_7268296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268296 prefixEnd_7268296 := by exact prefixLift 7268296
  have htrace : WordTrace (prefixWord ++ tailWord_7268296) baseStart_7268296 baseEnd_7268296 := by
    simpa [prefixWord, tailWord_7268296, baseEnd_7268296] using wordTrace_append hprefix tailTrace_7268296
  have hstable : (prefixWord ++ tailWord_7268296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268296).length < 2 ^ (prefixWord ++ tailWord_7268296).sum := by decide
  have hdescent : baseEnd_7268296 < baseStart_7268296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268313 : List Nat := [1, 2, 1, 2, 6, 1, 1, 3, 1, 5]
def baseStart_7268313 : Nat := 118140960795 + 7268313 * 2 ^ 59
def prefixEnd_7268313 : Nat := 4983230072969 + 3 ^ 40 * 7268313 * 2
def baseEnd_7268313 : Nat := 1244046038774175475220381

theorem tailTrace_7268313 : CollatzResearch.WordTrace tailWord_7268313 prefixEnd_7268313 1244046038774175475220381 := by
  unfold tailWord_7268313
  simp only [CollatzResearch.WordTrace]
  refine ⟨265097153717150804878257593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176731435811433869918838395 265097153717150804878257593)
  ·
    refine ⟨198822865287863103658693195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265097153717150804878257593 198822865287863103658693195)
    ·
      refine ⟨298234297931794655488039793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198822865287863103658693195 298234297931794655488039793)
      ·
        refine ⟨223675723448845991616029845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298234297931794655488039793 223675723448845991616029845)
        ·
          refine ⟨10484799536664655857001399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 223675723448845991616029845 10484799536664655857001399)
          ·
            refine ⟨15727199304996983785502099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10484799536664655857001399 15727199304996983785502099)
            ·
              refine ⟨23590798957495475678253149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15727199304996983785502099 23590798957495475678253149)
              ·
                refine ⟨8846549609060803379344931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23590798957495475678253149 8846549609060803379344931)
                ·
                  refine ⟨13269824413591205069017397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8846549609060803379344931 13269824413591205069017397)
                  ·
                    refine ⟨1244046038774175475220381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13269824413591205069017397 1244046038774175475220381)
                    ·
                      rfl

theorem cell23_7268313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 5].length) (baseStart_7268313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268313 prefixEnd_7268313 := by exact prefixLift 7268313
  have htrace : WordTrace (prefixWord ++ tailWord_7268313) baseStart_7268313 baseEnd_7268313 := by
    simpa [prefixWord, tailWord_7268313, baseEnd_7268313] using wordTrace_append hprefix tailTrace_7268313
  have hstable : (prefixWord ++ tailWord_7268313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268313).length < 2 ^ (prefixWord ++ tailWord_7268313).sum := by decide
  have hdescent : baseEnd_7268313 < baseStart_7268313 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268329 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 1, 8, 4]
def baseStart_7268329 : Nat := 118140960795 + 7268329 * 2 ^ 59
def prefixEnd_7268329 : Nat := 4983230072969 + 3 ^ 40 * 7268329 * 2
def baseEnd_7268329 : Nat := 3732146332012998363061069

theorem tailTrace_7268329 : CollatzResearch.WordTrace tailWord_7268329 prefixEnd_7268329 3732146332012998363061069 := by
  unfold tailWord_7268329
  simp only [CollatzResearch.WordTrace]
  refine ⟨265097737285092839610840041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176731824856728559740560027 265097737285092839610840041)
  ·
    refine ⟨198823302963819629708130031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265097737285092839610840041 198823302963819629708130031)
    ·
      refine ⟨298234954445729444562195047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198823302963819629708130031 298234954445729444562195047)
      ·
        refine ⟨447352431668594166843292571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298234954445729444562195047 447352431668594166843292571)
        ·
          refine ⟨671028647502891250264938857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447352431668594166843292571 671028647502891250264938857)
          ·
            refine ⟨503271485627168437698704143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 671028647502891250264938857 503271485627168437698704143)
            ·
              refine ⟨754907228440752656548056215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503271485627168437698704143 754907228440752656548056215)
              ·
                refine ⟨1132360842661128984822084323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 754907228440752656548056215 1132360842661128984822084323)
                ·
                  refine ⟨1698541263991693477233126485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1132360842661128984822084323 1698541263991693477233126485)
                  ·
                    refine ⟨19904780437402657936325701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1698541263991693477233126485 19904780437402657936325701)
                    ·
                      refine ⟨3732146332012998363061069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19904780437402657936325701 3732146332012998363061069)
                      ·
                        rfl

theorem cell23_7268329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 8, 4].length) (baseStart_7268329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268329 prefixEnd_7268329 := by exact prefixLift 7268329
  have htrace : WordTrace (prefixWord ++ tailWord_7268329) baseStart_7268329 baseEnd_7268329 := by
    simpa [prefixWord, tailWord_7268329, baseEnd_7268329] using wordTrace_append hprefix tailTrace_7268329
  have hstable : (prefixWord ++ tailWord_7268329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268329).length < 2 ^ (prefixWord ++ tailWord_7268329).sum := by decide
  have hdescent : baseEnd_7268329 < baseStart_7268329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268336 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 3]
def baseStart_7268336 : Nat := 118140960795 + 7268336 * 2 ^ 59
def prefixEnd_7268336 : Nat := 4983230072969 + 3 ^ 40 * 7268336 * 2
def baseEnd_7268336 : Nat := 3732149926377579835673537

theorem tailTrace_7268336 : CollatzResearch.WordTrace tailWord_7268336 prefixEnd_7268336 3732149926377579835673537 := by
  unfold tailWord_7268336
  simp only [CollatzResearch.WordTrace]
  refine ⟨132548996298033739903172431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176731995064044986537563241 132548996298033739903172431)
  ·
    refine ⟨198823494447050609854758647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132548996298033739903172431 198823494447050609854758647)
    ·
      refine ⟨298235241670575914782137971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198823494447050609854758647 298235241670575914782137971)
      ·
        refine ⟨447352862505863872173206957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298235241670575914782137971 447352862505863872173206957)
        ·
          refine ⟨167757323439698952064952609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 447352862505863872173206957 167757323439698952064952609)
          ·
            refine ⟨125817992579774214048714457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167757323439698952064952609 125817992579774214048714457)
            ·
              refine ⟨94363494434830660536535843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125817992579774214048714457 94363494434830660536535843)
              ·
                refine ⟨141545241652245990804803765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94363494434830660536535843 141545241652245990804803765)
                ·
                  refine ⟨13269866404898061637950353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141545241652245990804803765 13269866404898061637950353)
                  ·
                    refine ⟨9952399803673546228462765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13269866404898061637950353 9952399803673546228462765)
                    ·
                      refine ⟨3732149926377579835673537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9952399803673546228462765 3732149926377579835673537)
                      ·
                        rfl

theorem cell23_7268336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 3].length) (baseStart_7268336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268336 prefixEnd_7268336 := by exact prefixLift 7268336
  have htrace : WordTrace (prefixWord ++ tailWord_7268336) baseStart_7268336 baseEnd_7268336 := by
    simpa [prefixWord, tailWord_7268336, baseEnd_7268336] using wordTrace_append hprefix tailTrace_7268336
  have hstable : (prefixWord ++ tailWord_7268336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268336).length < 2 ^ (prefixWord ++ tailWord_7268336).sum := by decide
  have hdescent : baseEnd_7268336 < baseStart_7268336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268350 : List Nat := [4, 2, 2, 2, 1, 1, 1, 4, 1, 1, 4]
def baseStart_7268350 : Nat := 118140960795 + 7268350 * 2 ^ 59
def prefixEnd_7268350 : Nat := 4983230072969 + 3 ^ 40 * 7268350 * 2
def baseEnd_7268350 : Nat := 3732157115106742780898473

theorem tailTrace_7268350 : CollatzResearch.WordTrace tailWord_7268350 prefixEnd_7268350 3732157115106742780898473 := by
  unfold tailWord_7268350
  simp only [CollatzResearch.WordTrace]
  refine ⟨33137312902252095024669313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176732335478677840131569669 33137312902252095024669313)
  ·
    refine ⟨24852984676689071268501985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33137312902252095024669313 24852984676689071268501985)
    ·
      refine ⟨18639738507516803451376489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24852984676689071268501985 18639738507516803451376489)
      ·
        refine ⟨13979803880637602588532367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18639738507516803451376489 13979803880637602588532367)
        ·
          refine ⟨20969705820956403882798551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13979803880637602588532367 20969705820956403882798551)
          ·
            refine ⟨31454558731434605824197827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20969705820956403882798551 31454558731434605824197827)
            ·
              refine ⟨47181838097151908736296741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31454558731434605824197827 47181838097151908736296741)
              ·
                refine ⟨8846594643215982888055639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47181838097151908736296741 8846594643215982888055639)
                ·
                  refine ⟨13269891964823974332083459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8846594643215982888055639 13269891964823974332083459)
                  ·
                    refine ⟨19904837947235961498125189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13269891964823974332083459 19904837947235961498125189)
                    ·
                      refine ⟨3732157115106742780898473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19904837947235961498125189 3732157115106742780898473)
                      ·
                        rfl

theorem cell23_7268350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_7268350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268350 prefixEnd_7268350 := by exact prefixLift 7268350
  have htrace : WordTrace (prefixWord ++ tailWord_7268350) baseStart_7268350 baseEnd_7268350 := by
    simpa [prefixWord, tailWord_7268350, baseEnd_7268350] using wordTrace_append hprefix tailTrace_7268350
  have hstable : (prefixWord ++ tailWord_7268350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268350).length < 2 ^ (prefixWord ++ tailWord_7268350).sum := by decide
  have hdescent : baseEnd_7268350 < baseStart_7268350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268369 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 3, 9]
def baseStart_7268369 : Nat := 118140960795 + 7268369 * 2 ^ 59
def prefixEnd_7268369 : Nat := 4983230072969 + 3 ^ 40 * 7268369 * 2
def baseEnd_7268369 : Nat := 1244055623746392735520295

theorem tailTrace_7268369 : CollatzResearch.WordTrace tailWord_7268369 prefixEnd_7268369 1244055623746392735520295 := by
  unfold tailWord_7268369
  simp only [CollatzResearch.WordTrace]
  refine ⟨265099196204947926442296161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176732797469965284294864107 265099196204947926442296161)
  ·
    refine ⟨198824397153710944831722121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265099196204947926442296161 198824397153710944831722121)
    ·
      refine ⟨149118297865283208623791591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198824397153710944831722121 149118297865283208623791591)
      ·
        refine ⟨223677446797924812935687387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149118297865283208623791591 223677446797924812935687387)
        ·
          refine ⟨335516170196887219403531081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223677446797924812935687387 335516170196887219403531081)
          ·
            refine ⟨251637127647665414552648311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335516170196887219403531081 251637127647665414552648311)
            ·
              refine ⟨377455691471498121828972467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251637127647665414552648311 377455691471498121828972467)
              ·
                refine ⟨566183537207247182743458701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377455691471498121828972467 566183537207247182743458701)
                ·
                  refine ⟨212318826452717693528797013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 566183537207247182743458701 212318826452717693528797013)
                  ·
                    refine ⟨1244055623746392735520295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 212318826452717693528797013 1244055623746392735520295)
                    ·
                      rfl

theorem cell23_7268369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 9].length) (baseStart_7268369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268369 prefixEnd_7268369 := by exact prefixLift 7268369
  have htrace : WordTrace (prefixWord ++ tailWord_7268369) baseStart_7268369 baseEnd_7268369 := by
    simpa [prefixWord, tailWord_7268369, baseEnd_7268369] using wordTrace_append hprefix tailTrace_7268369
  have hstable : (prefixWord ++ tailWord_7268369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268369).length < 2 ^ (prefixWord ++ tailWord_7268369).sum := by decide
  have hdescent : baseEnd_7268369 < baseStart_7268369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268373 : List Nat := [1, 3, 2, 1, 6, 1, 9]
def baseStart_7268373 : Nat := 118140960795 + 7268373 * 2 ^ 59
def prefixEnd_7268373 : Nat := 4983230072969 + 3 ^ 40 * 7268373 * 2
def baseEnd_7268373 : Nat := 46076159569898718406307

theorem tailTrace_7268373 : CollatzResearch.WordTrace tailWord_7268373 prefixEnd_7268373 46076159569898718406307 := by
  unfold tailWord_7268373
  simp only [CollatzResearch.WordTrace]
  refine ⟨265099342096933435125441773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176732894731288956750294515 265099342096933435125441773)
  ·
    refine ⟨99412253286350038172040665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265099342096933435125441773 99412253286350038172040665)
    ·
      refine ⟨74559189964762528629030499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99412253286350038172040665 74559189964762528629030499)
      ·
        refine ⟨111838784947143792943545749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74559189964762528629030499 111838784947143792943545749)
        ·
          refine ⟨5242443044397365294228707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 111838784947143792943545749 5242443044397365294228707)
          ·
            refine ⟨7863664566596047941343061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5242443044397365294228707 7863664566596047941343061)
            ·
              refine ⟨46076159569898718406307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7863664566596047941343061 46076159569898718406307)
              ·
                rfl

theorem cell23_7268373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 9].length) (baseStart_7268373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268373 prefixEnd_7268373 := by exact prefixLift 7268373
  have htrace : WordTrace (prefixWord ++ tailWord_7268373) baseStart_7268373 baseEnd_7268373 := by
    simpa [prefixWord, tailWord_7268373, baseEnd_7268373] using wordTrace_append hprefix tailTrace_7268373
  have hstable : (prefixWord ++ tailWord_7268373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268373).length < 2 ^ (prefixWord ++ tailWord_7268373).sum := by decide
  have hdescent : baseEnd_7268373 < baseStart_7268373 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268383 : List Nat := [1, 1, 2, 4, 1, 2, 1, 3, 4, 1, 3]
def baseStart_7268383 : Nat := 118140960795 + 7268383 * 2 ^ 59
def prefixEnd_7268383 : Nat := 4983230072969 + 3 ^ 40 * 7268383 * 2
def baseEnd_7268383 : Nat := 3732174059968341151785821

theorem tailTrace_7268383 : CollatzResearch.WordTrace tailWord_7268383 prefixEnd_7268383 3732174059968341151785821 := by
  unfold tailWord_7268383
  simp only [CollatzResearch.WordTrace]
  refine ⟨265099706826897206833305803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176733137884598137888870535 265099706826897206833305803)
  ·
    refine ⟨397649560240345810249958705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265099706826897206833305803 397649560240345810249958705)
    ·
      refine ⟨298237170180259357687469029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397649560240345810249958705 298237170180259357687469029)
      ·
        refine ⟨55919469408798629566400443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 298237170180259357687469029 55919469408798629566400443)
        ·
          refine ⟨83879204113197944349600665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55919469408798629566400443 83879204113197944349600665)
          ·
            refine ⟨62909403084898458262200499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83879204113197944349600665 62909403084898458262200499)
            ·
              refine ⟨94364104627347687393300749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62909403084898458262200499 94364104627347687393300749)
              ·
                refine ⟨35386539235255382772487781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94364104627347687393300749 35386539235255382772487781)
                ·
                  refine ⟨6634976106610384269841459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35386539235255382772487781 6634976106610384269841459)
                  ·
                    refine ⟨9952464159915576404762189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6634976106610384269841459 9952464159915576404762189)
                    ·
                      refine ⟨3732174059968341151785821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9952464159915576404762189 3732174059968341151785821)
                      ·
                        rfl

theorem cell23_7268383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_7268383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268383 prefixEnd_7268383 := by exact prefixLift 7268383
  have htrace : WordTrace (prefixWord ++ tailWord_7268383) baseStart_7268383 baseEnd_7268383 := by
    simpa [prefixWord, tailWord_7268383, baseEnd_7268383] using wordTrace_append hprefix tailTrace_7268383
  have hstable : (prefixWord ++ tailWord_7268383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268383).length < 2 ^ (prefixWord ++ tailWord_7268383).sum := by decide
  have hdescent : baseEnd_7268383 < baseStart_7268383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268386 : List Nat := [3, 3, 1, 1, 1, 2, 2, 1, 2, 7]
def baseStart_7268386 : Nat := 118140960795 + 7268386 * 2 ^ 59
def prefixEnd_7268386 : Nat := 4983230072969 + 3 ^ 40 * 7268386 * 2
def baseEnd_7268386 : Nat := 1244058533470101546682769

theorem tailTrace_7268386 : CollatzResearch.WordTrace tailWord_7268386 prefixEnd_7268386 1244058533470101546682769 := by
  unfold tailWord_7268386
  simp only [CollatzResearch.WordTrace]
  refine ⟨66274954061471584586416253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176733210830590892230443341 66274954061471584586416253)
  ·
    refine ⟨24853107773051844219906095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66274954061471584586416253 24853107773051844219906095)
    ·
      refine ⟨37279661659577766329859143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24853107773051844219906095 37279661659577766329859143)
      ·
        refine ⟨55919492489366649494788715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37279661659577766329859143 55919492489366649494788715)
        ·
          refine ⟨83879238734049974242183073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55919492489366649494788715 83879238734049974242183073)
          ·
            refine ⟨62909429050537480681637305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83879238734049974242183073 62909429050537480681637305)
            ·
              refine ⟨47182071787903110511227979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62909429050537480681637305 47182071787903110511227979)
              ·
                refine ⟨70773107681854665766841969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47182071787903110511227979 70773107681854665766841969)
                ·
                  refine ⟨53079830761390999325131477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70773107681854665766841969 53079830761390999325131477)
                  ·
                    refine ⟨1244058533470101546682769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53079830761390999325131477 1244058533470101546682769)
                    ·
                      rfl

theorem cell23_7268386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_7268386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268386 prefixEnd_7268386 := by exact prefixLift 7268386
  have htrace : WordTrace (prefixWord ++ tailWord_7268386) baseStart_7268386 baseEnd_7268386 := by
    simpa [prefixWord, tailWord_7268386, baseEnd_7268386] using wordTrace_append hprefix tailTrace_7268386
  have hstable : (prefixWord ++ tailWord_7268386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268386).length < 2 ^ (prefixWord ++ tailWord_7268386).sum := by decide
  have hdescent : baseEnd_7268386 < baseStart_7268386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268400 : List Nat := [2, 1, 1, 1, 2, 6, 1, 3, 2, 1, 3]
def baseStart_7268400 : Nat := 118140960795 + 7268400 * 2 ^ 59
def prefixEnd_7268400 : Nat := 4983230072969 + 3 ^ 40 * 7268400 * 2
def baseEnd_7268400 : Nat := 3732182789139467585273243

theorem tailTrace_7268400 : CollatzResearch.WordTrace tailWord_7268400 prefixEnd_7268400 3732182789139467585273243 := by
  unfold tailWord_7268400
  simp only [CollatzResearch.WordTrace]
  refine ⟨132550163433917809368337327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176733551245223745824449769 132550163433917809368337327)
  ·
    refine ⟨198825245150876714052505991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132550163433917809368337327 198825245150876714052505991)
    ·
      refine ⟨298237867726315071078758987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198825245150876714052505991 298237867726315071078758987)
      ·
        refine ⟨447356801589472606618138481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298237867726315071078758987 447356801589472606618138481)
        ·
          refine ⟨335517601192104454963603861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447356801589472606618138481 335517601192104454963603861)
          ·
            refine ⟨15727387555879896326418931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 335517601192104454963603861 15727387555879896326418931)
            ·
              refine ⟨23591081333819844489628397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15727387555879896326418931 23591081333819844489628397)
              ·
                refine ⟨8846655500182441683610649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23591081333819844489628397 8846655500182441683610649)
                ·
                  refine ⟨6634991625136831262707987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8846655500182441683610649 6634991625136831262707987)
                  ·
                    refine ⟨9952487437705246894061981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6634991625136831262707987 9952487437705246894061981)
                    ·
                      refine ⟨3732182789139467585273243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9952487437705246894061981 3732182789139467585273243)
                      ·
                        rfl

theorem cell23_7268400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 2, 1, 3].length) (baseStart_7268400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268400 prefixEnd_7268400 := by exact prefixLift 7268400
  have htrace : WordTrace (prefixWord ++ tailWord_7268400) baseStart_7268400 baseEnd_7268400 := by
    simpa [prefixWord, tailWord_7268400, baseEnd_7268400] using wordTrace_append hprefix tailTrace_7268400
  have hstable : (prefixWord ++ tailWord_7268400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268400).length < 2 ^ (prefixWord ++ tailWord_7268400).sum := by decide
  have hdescent : baseEnd_7268400 < baseStart_7268400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268404 : List Nat := [2, 5, 1, 2, 2, 2, 1, 2, 1, 2, 3]
def baseStart_7268404 : Nat := 118140960795 + 7268404 * 2 ^ 59
def prefixEnd_7268404 : Nat := 4983230072969 + 3 ^ 40 * 7268404 * 2
def baseEnd_7268404 : Nat := 3732184843062085569623225

theorem tailTrace_7268404 : CollatzResearch.WordTrace tailWord_7268404 prefixEnd_7268404 3732184843062085569623225 := by
  unfold tailWord_7268404
  simp only [CollatzResearch.WordTrace]
  refine ⟨132550236379910563709910133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176733648506547418279880177 132550236379910563709910133)
  ·
    refine ⟨12426584660616615347804075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132550236379910563709910133 12426584660616615347804075)
    ·
      refine ⟨18639876990924923021706113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12426584660616615347804075 18639876990924923021706113)
      ·
        refine ⟨13979907743193692266279585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18639876990924923021706113 13979907743193692266279585)
        ·
          refine ⟨10484930807395269199709689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13979907743193692266279585 10484930807395269199709689)
          ·
            refine ⟨7863698105546451899782267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10484930807395269199709689 7863698105546451899782267)
            ·
              refine ⟨11795547158319677849673401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7863698105546451899782267 11795547158319677849673401)
              ·
                refine ⟨8846660368739758387255051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11795547158319677849673401 8846660368739758387255051)
                ·
                  refine ⟨13269990553109637580882577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8846660368739758387255051 13269990553109637580882577)
                  ·
                    refine ⟨9952492914832228185661933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13269990553109637580882577 9952492914832228185661933)
                    ·
                      refine ⟨3732184843062085569623225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9952492914832228185661933 3732184843062085569623225)
                      ·
                        rfl

theorem cell23_7268404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_7268404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268404 prefixEnd_7268404 := by exact prefixLift 7268404
  have htrace : WordTrace (prefixWord ++ tailWord_7268404) baseStart_7268404 baseEnd_7268404 := by
    simpa [prefixWord, tailWord_7268404, baseEnd_7268404] using wordTrace_append hprefix tailTrace_7268404
  have hstable : (prefixWord ++ tailWord_7268404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268404).length < 2 ^ (prefixWord ++ tailWord_7268404).sum := by decide
  have hdescent : baseEnd_7268404 < baseStart_7268404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268436 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 2, 3, 6]
def baseStart_7268436 : Nat := 118140960795 + 7268436 * 2 ^ 59
def prefixEnd_7268436 : Nat := 4983230072969 + 3 ^ 40 * 7268436 * 2
def baseEnd_7268436 : Nat := 3732201274443029444423077

theorem tailTrace_7268436 : CollatzResearch.WordTrace tailWord_7268436 prefixEnd_7268436 3732201274443029444423077 := by
  unfold tailWord_7268436
  simp only [CollatzResearch.WordTrace]
  refine ⟨132550819947852598442492581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176734426597136797923323441 132550819947852598442492581)
  ·
    refine ⟨24853278740222362207967359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132550819947852598442492581 24853278740222362207967359)
    ·
      refine ⟨37279918110333543311951039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24853278740222362207967359 37279918110333543311951039)
      ·
        refine ⟨55919877165500314967926559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37279918110333543311951039 55919877165500314967926559)
        ·
          refine ⟨83879815748250472451889839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55919877165500314967926559 83879815748250472451889839)
          ·
            refine ⟨125819723622375708677834759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83879815748250472451889839 125819723622375708677834759)
            ·
              refine ⟨188729585433563563016752139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125819723622375708677834759 188729585433563563016752139)
              ·
                refine ⟨283094378150345344525128209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188729585433563563016752139 283094378150345344525128209)
                ·
                  refine ⟨212320783612759008393846157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283094378150345344525128209 212320783612759008393846157)
                  ·
                    refine ⟨79620293854784628147692309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 212320783612759008393846157 79620293854784628147692309)
                    ·
                      refine ⟨3732201274443029444423077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79620293854784628147692309 3732201274443029444423077)
                      ·
                        rfl

theorem cell23_7268436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_7268436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268436 prefixEnd_7268436 := by exact prefixLift 7268436
  have htrace : WordTrace (prefixWord ++ tailWord_7268436) baseStart_7268436 baseEnd_7268436 := by
    simpa [prefixWord, tailWord_7268436, baseEnd_7268436] using wordTrace_append hprefix tailTrace_7268436
  have hstable : (prefixWord ++ tailWord_7268436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268436).length < 2 ^ (prefixWord ++ tailWord_7268436).sum := by decide
  have hdescent : baseEnd_7268436 < baseStart_7268436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268450 : List Nat := [3, 3, 2, 2, 2, 1, 1, 1, 2, 6]
def baseStart_7268450 : Nat := 118140960795 + 7268450 * 2 ^ 59
def prefixEnd_7268450 : Nat := 4983230072969 + 3 ^ 40 * 7268450 * 2
def baseEnd_7268450 : Nat := 1244069487724064129882671

theorem tailTrace_7268450 : CollatzResearch.WordTrace tailWord_7268450 prefixEnd_7268450 1244069487724064129882671 := by
  unfold tailWord_7268450
  simp only [CollatzResearch.WordTrace]
  refine ⟨66275537629413619318998701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176734767011769651517329869 66275537629413619318998701)
  ·
    refine ⟨24853326611030107244624513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66275537629413619318998701 24853326611030107244624513)
    ·
      refine ⟨18639994958272580433468385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24853326611030107244624513 18639994958272580433468385)
      ·
        refine ⟨13979996218704435325101289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18639994958272580433468385 13979996218704435325101289)
        ·
          refine ⟨10484997164028326493825967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13979996218704435325101289 10484997164028326493825967)
          ·
            refine ⟨15727495746042489740738951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10484997164028326493825967 15727495746042489740738951)
            ·
              refine ⟨23591243619063734611108427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15727495746042489740738951 23591243619063734611108427)
              ·
                refine ⟨35386865428595601916662641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23591243619063734611108427 35386865428595601916662641)
                ·
                  refine ⟨26540149071446701437496981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35386865428595601916662641 26540149071446701437496981)
                  ·
                    refine ⟨1244069487724064129882671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26540149071446701437496981 1244069487724064129882671)
                    ·
                      rfl

theorem cell23_7268450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_7268450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268450 prefixEnd_7268450 := by exact prefixLift 7268450
  have htrace : WordTrace (prefixWord ++ tailWord_7268450) baseStart_7268450 baseEnd_7268450 := by
    simpa [prefixWord, tailWord_7268450, baseEnd_7268450] using wordTrace_append hprefix tailTrace_7268450
  have hstable : (prefixWord ++ tailWord_7268450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268450).length < 2 ^ (prefixWord ++ tailWord_7268450).sum := by decide
  have hdescent : baseEnd_7268450 < baseStart_7268450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268453 : List Nat := [1, 3, 1, 3, 2, 3, 1, 1, 2, 2, 4]
def baseStart_7268453 : Nat := 118140960795 + 7268453 * 2 ^ 59
def prefixEnd_7268453 : Nat := 4983230072969 + 3 ^ 40 * 7268453 * 2
def baseEnd_7268453 : Nat := 3732210003614155877910499

theorem tailTrace_7268453 : CollatzResearch.WordTrace tailWord_7268453 prefixEnd_7268453 3732210003614155877910499 := by
  unfold tailWord_7268453
  simp only [CollatzResearch.WordTrace]
  refine ⟨265102259936643608788354013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176734839957762405858902675 265102259936643608788354013)
  ·
    refine ⟨99413347476241353295632755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265102259936643608788354013 99413347476241353295632755)
    ·
      refine ⟨149120021214362029943449133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99413347476241353295632755 149120021214362029943449133)
      ·
        refine ⟨55920007955385761228793425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149120021214362029943449133 55920007955385761228793425)
        ·
          refine ⟨41940005966539320921595069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55920007955385761228793425 41940005966539320921595069)
          ·
            refine ⟨15727502237452245345598151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41940005966539320921595069 15727502237452245345598151)
            ·
              refine ⟨23591253356178368018397227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15727502237452245345598151 23591253356178368018397227)
              ·
                refine ⟨35386880034267552027595841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23591253356178368018397227 35386880034267552027595841)
                ·
                  refine ⟨26540160025700664020696881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35386880034267552027595841 26540160025700664020696881)
                  ·
                    refine ⟨19905120019275498015522661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26540160025700664020696881 19905120019275498015522661)
                    ·
                      refine ⟨3732210003614155877910499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19905120019275498015522661 3732210003614155877910499)
                      ·
                        rfl

theorem cell23_7268453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_7268453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268453 prefixEnd_7268453 := by exact prefixLift 7268453
  have htrace : WordTrace (prefixWord ++ tailWord_7268453) baseStart_7268453 baseEnd_7268453 := by
    simpa [prefixWord, tailWord_7268453, baseEnd_7268453] using wordTrace_append hprefix tailTrace_7268453
  have hstable : (prefixWord ++ tailWord_7268453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268453).length < 2 ^ (prefixWord ++ tailWord_7268453).sum := by decide
  have hdescent : baseEnd_7268453 < baseStart_7268453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268513 : List Nat := [1, 2, 3, 3, 1, 2, 1, 2, 1, 3, 4]
def baseStart_7268513 : Nat := 118140960795 + 7268513 * 2 ^ 59
def prefixEnd_7268513 : Nat := 4983230072969 + 3 ^ 40 * 7268513 * 2
def baseEnd_7268513 : Nat := 3732240812453425643160223

theorem tailTrace_7268513 : CollatzResearch.WordTrace tailWord_7268513 prefixEnd_7268513 3732240812453425643160223 := by
  unfold tailWord_7268513
  simp only [CollatzResearch.WordTrace]
  refine ⟨265104448316426239035538193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176736298877617492690358795 265104448316426239035538193)
  ·
    refine ⟨198828336237319679276653645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265104448316426239035538193 198828336237319679276653645)
    ·
      refine ⟨74560626088994879728745117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198828336237319679276653645 74560626088994879728745117)
      ·
        refine ⟨27960234783373079898279419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74560626088994879728745117 27960234783373079898279419)
        ·
          refine ⟨41940352175059619847419129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27960234783373079898279419 41940352175059619847419129)
          ·
            refine ⟨31455264131294714885564347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41940352175059619847419129 31455264131294714885564347)
            ·
              refine ⟨47182896196942072328346521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31455264131294714885564347 47182896196942072328346521)
              ·
                refine ⟨35387172147706554246259891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47182896196942072328346521 35387172147706554246259891)
                ·
                  refine ⟨53080758221559831369389837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35387172147706554246259891 53080758221559831369389837)
                  ·
                    refine ⟨19905284333084936763521189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53080758221559831369389837 19905284333084936763521189)
                    ·
                      refine ⟨3732240812453425643160223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19905284333084936763521189 3732240812453425643160223)
                      ·
                        rfl

theorem cell23_7268513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_7268513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268513 prefixEnd_7268513 := by exact prefixLift 7268513
  have htrace : WordTrace (prefixWord ++ tailWord_7268513) baseStart_7268513 baseEnd_7268513 := by
    simpa [prefixWord, tailWord_7268513, baseEnd_7268513] using wordTrace_append hprefix tailTrace_7268513
  have hstable : (prefixWord ++ tailWord_7268513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268513).length < 2 ^ (prefixWord ++ tailWord_7268513).sum := by decide
  have hdescent : baseEnd_7268513 < baseStart_7268513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268536 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 10]
def baseStart_7268536 : Nat := 118140960795 + 7268536 * 2 ^ 59
def prefixEnd_7268536 : Nat := 4983230072969 + 3 ^ 40 * 7268536 * 2
def baseEnd_7268536 : Nat := 414694735834275450352513

theorem tailTrace_7268536 : CollatzResearch.WordTrace tailWord_7268536 prefixEnd_7268536 414694735834275450352513 := by
  unfold tailWord_7268536
  simp only [CollatzResearch.WordTrace]
  refine ⟨132552643597671456981812731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176736858130228609309083641 132552643597671456981812731)
  ·
    refine ⟨198828965396507185472719097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132552643597671456981812731 198828965396507185472719097)
    ·
      refine ⟨149121724047380389104539323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198828965396507185472719097 149121724047380389104539323)
      ·
        refine ⟨223682586071070583656808985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149121724047380389104539323 223682586071070583656808985)
        ·
          refine ⟨167761939553302937742606739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223682586071070583656808985 167761939553302937742606739)
          ·
            refine ⟨251642909329954406613910109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167761939553302937742606739 251642909329954406613910109)
            ·
              refine ⟨94366090998732902480216291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 251642909329954406613910109 94366090998732902480216291)
              ·
                refine ⟨141549136498099353720324437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94366090998732902480216291 141549136498099353720324437)
                ·
                  refine ⟨414694735834275450352513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 141549136498099353720324437 414694735834275450352513)
                  ·
                    rfl

theorem cell23_7268536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 10].length) (baseStart_7268536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268536 prefixEnd_7268536 := by exact prefixLift 7268536
  have htrace : WordTrace (prefixWord ++ tailWord_7268536) baseStart_7268536 baseEnd_7268536 := by
    simpa [prefixWord, tailWord_7268536, baseEnd_7268536] using wordTrace_append hprefix tailTrace_7268536
  have hstable : (prefixWord ++ tailWord_7268536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268536).length < 2 ^ (prefixWord ++ tailWord_7268536).sum := by decide
  have hdescent : baseEnd_7268536 < baseStart_7268536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268570 : List Nat := [3, 1, 1, 2, 2, 1, 6, 1, 6]
def baseStart_7268570 : Nat := 118140960795 + 7268570 * 2 ^ 59
def prefixEnd_7268570 : Nat := 4983230072969 + 3 ^ 40 * 7268570 * 2
def baseEnd_7268570 : Nat := 414696675650081324460829

theorem tailTrace_7268570 : CollatzResearch.WordTrace tailWord_7268570 prefixEnd_7268570 414696675650081324460829 := by
  unfold tailWord_7268570
  simp only [CollatzResearch.WordTrace]
  refine ⟨66276631819304934442590791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176737684851479825180242109 66276631819304934442590791)
  ·
    refine ⟨99414947728957401663886187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66276631819304934442590791 99414947728957401663886187)
    ·
      refine ⟨149122421593436102495829281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99414947728957401663886187 149122421593436102495829281)
      ·
        refine ⟨111841816195077076871871961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149122421593436102495829281 111841816195077076871871961)
        ·
          refine ⟨83881362146307807653903971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111841816195077076871871961 83881362146307807653903971)
          ·
            refine ⟨125822043219461711480855957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83881362146307807653903971 125822043219461711480855957)
            ·
              refine ⟨5897908275912267725665123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 125822043219461711480855957 5897908275912267725665123)
              ·
                refine ⟨8846862413868401588497685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5897908275912267725665123 8846862413868401588497685)
                ·
                  refine ⟨414696675650081324460829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8846862413868401588497685 414696675650081324460829)
                  ·
                    rfl

theorem cell23_7268570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 6].length) (baseStart_7268570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268570 prefixEnd_7268570 := by exact prefixLift 7268570
  have htrace : WordTrace (prefixWord ++ tailWord_7268570) baseStart_7268570 baseEnd_7268570 := by
    simpa [prefixWord, tailWord_7268570, baseEnd_7268570] using wordTrace_append hprefix tailTrace_7268570
  have hstable : (prefixWord ++ tailWord_7268570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268570).length < 2 ^ (prefixWord ++ tailWord_7268570).sum := by decide
  have hdescent : baseEnd_7268570 < baseStart_7268570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268580 : List Nat := [2, 3, 1, 1, 1, 2, 1, 3, 5, 1, 3]
def baseStart_7268580 : Nat := 118140960795 + 7268580 * 2 ^ 59
def prefixEnd_7268580 : Nat := 4983230072969 + 3 ^ 40 * 7268580 * 2
def baseEnd_7268580 : Nat := 3732275215657276881022415

theorem tailTrace_7268580 : CollatzResearch.WordTrace tailWord_7268580 prefixEnd_7268580 3732275215657276881022415 := by
  unfold tailWord_7268580
  simp only [CollatzResearch.WordTrace]
  refine ⟨132553446003591754739113597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176737928004789006318818129 132553446003591754739113597)
  ·
    refine ⟨49707542251346908027167599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132553446003591754739113597 49707542251346908027167599)
    ·
      refine ⟨74561313377020362040751399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49707542251346908027167599 74561313377020362040751399)
      ·
        refine ⟨111841970065530543061127099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74561313377020362040751399 111841970065530543061127099)
        ·
          refine ⟨167762955098295814591690649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111841970065530543061127099 167762955098295814591690649)
          ·
            refine ⟨125822216323721860943767987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167762955098295814591690649 125822216323721860943767987)
            ·
              refine ⟨188733324485582791415651981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125822216323721860943767987 188733324485582791415651981)
              ·
                refine ⟨70774996682093546780869493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188733324485582791415651981 70774996682093546780869493)
                ·
                  refine ⟨6635155938946270010706515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70774996682093546780869493 6635155938946270010706515)
                  ·
                    refine ⟨9952733908419405016059773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6635155938946270010706515 9952733908419405016059773)
                    ·
                      refine ⟨3732275215657276881022415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9952733908419405016059773 3732275215657276881022415)
                      ·
                        rfl

theorem cell23_7268580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 5, 1, 3].length) (baseStart_7268580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268580 prefixEnd_7268580 := by exact prefixLift 7268580
  have htrace : WordTrace (prefixWord ++ tailWord_7268580) baseStart_7268580 baseEnd_7268580 := by
    simpa [prefixWord, tailWord_7268580, baseEnd_7268580] using wordTrace_append hprefix tailTrace_7268580
  have hstable : (prefixWord ++ tailWord_7268580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268580).length < 2 ^ (prefixWord ++ tailWord_7268580).sum := by decide
  have hdescent : baseEnd_7268580 < baseStart_7268580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268623 : List Nat := [1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 5]
def baseStart_7268623 : Nat := 118140960795 + 7268623 * 2 ^ 59
def prefixEnd_7268623 : Nat := 4983230072969 + 3 ^ 40 * 7268623 * 2
def baseEnd_7268623 : Nat := 3732297295325420212784717

theorem tailTrace_7268623 : CollatzResearch.WordTrace tailWord_7268623 prefixEnd_7268623 3732297295325420212784717 := by
  unfold tailWord_7268623
  simp only [CollatzResearch.WordTrace]
  refine ⟨265108460346027727822042523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176738973564018485214695015 265108460346027727822042523)
  ·
    refine ⟨397662690519041591733063785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265108460346027727822042523 397662690519041591733063785)
    ·
      refine ⟨298247017889281193799797839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397662690519041591733063785 298247017889281193799797839)
      ·
        refine ⟨447370526833921790699696759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298247017889281193799797839 447370526833921790699696759)
        ·
          refine ⟨671055790250882686049545139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447370526833921790699696759 671055790250882686049545139)
          ·
            refine ⟨1006583685376324029074317709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671055790250882686049545139 1006583685376324029074317709)
            ·
              refine ⟨377468882016121510902869141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1006583685376324029074317709 377468882016121510902869141)
              ·
                refine ⟨17693853844505695823571991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 377468882016121510902869141 17693853844505695823571991)
                ·
                  refine ⟨26540780766758543735357987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17693853844505695823571991 26540780766758543735357987)
                  ·
                    refine ⟨39811171150137815603036981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26540780766758543735357987 39811171150137815603036981)
                    ·
                      refine ⟨3732297295325420212784717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39811171150137815603036981 3732297295325420212784717)
                      ·
                        rfl

theorem cell23_7268623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 5].length) (baseStart_7268623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268623 prefixEnd_7268623 := by exact prefixLift 7268623
  have htrace : WordTrace (prefixWord ++ tailWord_7268623) baseStart_7268623 baseEnd_7268623 := by
    simpa [prefixWord, tailWord_7268623, baseEnd_7268623] using wordTrace_append hprefix tailTrace_7268623
  have hstable : (prefixWord ++ tailWord_7268623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268623).length < 2 ^ (prefixWord ++ tailWord_7268623).sum := by decide
  have hdescent : baseEnd_7268623 < baseStart_7268623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268660 : List Nat := [2, 5, 1, 1, 1, 3, 10]
def baseStart_7268660 : Nat := 118140960795 + 7268660 * 2 ^ 59
def prefixEnd_7268660 : Nat := 4983230072969 + 3 ^ 40 * 7268660 * 2
def baseEnd_7268660 : Nat := 46077978939625142815087

theorem tailTrace_7268660 : CollatzResearch.WordTrace tailWord_7268660 prefixEnd_7268660 46077978939625142815087 := by
  unfold tailWord_7268660
  simp only [CollatzResearch.WordTrace]
  refine ⟨132554904923446841570569717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176739873231262455427426289 132554904923446841570569717)
  ·
    refine ⟨12427022336573141397240911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132554904923446841570569717 12427022336573141397240911)
    ·
      refine ⟨18640533504859712095861367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12427022336573141397240911 18640533504859712095861367)
      ·
        refine ⟨27960800257289568143792051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18640533504859712095861367 27960800257289568143792051)
        ·
          refine ⟨41941200385934352215688077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27960800257289568143792051 41941200385934352215688077)
          ·
            refine ⟨15727950144725382080883029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41941200385934352215688077 15727950144725382080883029)
            ·
              refine ⟨46077978939625142815087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15727950144725382080883029 46077978939625142815087)
              ·
                rfl

theorem cell23_7268660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 10].length) (baseStart_7268660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268660 prefixEnd_7268660 := by exact prefixLift 7268660
  have htrace : WordTrace (prefixWord ++ tailWord_7268660) baseStart_7268660 baseEnd_7268660 := by
    simpa [prefixWord, tailWord_7268660, baseEnd_7268660] using wordTrace_append hprefix tailTrace_7268660
  have hstable : (prefixWord ++ tailWord_7268660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268660).length < 2 ^ (prefixWord ++ tailWord_7268660).sum := by decide
  have hdescent : baseEnd_7268660 < baseStart_7268660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268703 : List Nat := [1, 1, 2, 3, 1, 2, 2, 2, 1, 8]
def baseStart_7268703 : Nat := 118140960795 + 7268703 * 2 ^ 59
def prefixEnd_7268703 : Nat := 4983230072969 + 3 ^ 40 * 7268703 * 2
def baseEnd_7268703 : Nat := 1244112791259259966594783

theorem tailTrace_7268703 : CollatzResearch.WordTrace tailWord_7268703 prefixEnd_7268703 1244112791259259966594783 := by
  unfold tailWord_7268703
  simp only [CollatzResearch.WordTrace]
  refine ⟨265111378185737901484954763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176740918790491934323303175 265111378185737901484954763)
  ·
    refine ⟨397667067278606852227432145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265111378185737901484954763 397667067278606852227432145)
    ·
      refine ⟨298250300458955139170574109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397667067278606852227432145 298250300458955139170574109)
      ·
        refine ⟨111843862672108177188965291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298250300458955139170574109 111843862672108177188965291)
        ·
          refine ⟨167765794008162265783447937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111843862672108177188965291 167765794008162265783447937)
          ·
            refine ⟨125824345506121699337585953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167765794008162265783447937 125824345506121699337585953)
            ·
              refine ⟨94368259129591274503189465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125824345506121699337585953 94368259129591274503189465)
              ·
                refine ⟨70776194347193455877392099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94368259129591274503189465 70776194347193455877392099)
                ·
                  refine ⟨106164291520790183816088149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70776194347193455877392099 106164291520790183816088149)
                  ·
                    refine ⟨1244112791259259966594783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 106164291520790183816088149 1244112791259259966594783)
                    ·
                      rfl

theorem cell23_7268703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 8].length) (baseStart_7268703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268703 prefixEnd_7268703 := by exact prefixLift 7268703
  have htrace : WordTrace (prefixWord ++ tailWord_7268703) baseStart_7268703 baseEnd_7268703 := by
    simpa [prefixWord, tailWord_7268703, baseEnd_7268703] using wordTrace_append hprefix tailTrace_7268703
  have hstable : (prefixWord ++ tailWord_7268703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268703).length < 2 ^ (prefixWord ++ tailWord_7268703).sum := by decide
  have hdescent : baseEnd_7268703 < baseStart_7268703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268738 : List Nat := [3, 4, 2, 1, 2, 1, 1, 3, 2, 1, 3]
def baseStart_7268738 : Nat := 118140960795 + 7268738 * 2 ^ 59
def prefixEnd_7268738 : Nat := 4983230072969 + 3 ^ 40 * 7268738 * 2
def baseEnd_7268738 : Nat := 3732356345600687262846689

theorem tailTrace_7268738 : CollatzResearch.WordTrace tailWord_7268738 prefixEnd_7268738 3732356345600687262846689 := by
  unfold tailWord_7268738
  simp only [CollatzResearch.WordTrace]
  refine ⟨66278163685152775615619717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176741769827074068308319245 66278163685152775615619717)
  ·
    refine ⟨12427155690966145427928697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66278163685152775615619717 12427155690966145427928697)
    ·
      refine ⟨9320366768224609070946523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12427155690966145427928697 9320366768224609070946523)
      ·
        refine ⟨13980550152336913606419785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9320366768224609070946523 13980550152336913606419785)
        ·
          refine ⟨10485412614252685204814839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13980550152336913606419785 10485412614252685204814839)
          ·
            refine ⟨15728118921379027807222259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10485412614252685204814839 15728118921379027807222259)
            ·
              refine ⟨23592178382068541710833389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15728118921379027807222259 23592178382068541710833389)
              ·
                refine ⟨8847066893275703141562521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23592178382068541710833389 8847066893275703141562521)
                ·
                  refine ⟨6635300169956777356171891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8847066893275703141562521 6635300169956777356171891)
                  ·
                    refine ⟨9952950254935166034257837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6635300169956777356171891 9952950254935166034257837)
                    ·
                      refine ⟨3732356345600687262846689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9952950254935166034257837 3732356345600687262846689)
                      ·
                        rfl

theorem cell23_7268738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_7268738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268738 prefixEnd_7268738 := by exact prefixLift 7268738
  have htrace : WordTrace (prefixWord ++ tailWord_7268738) baseStart_7268738 baseEnd_7268738 := by
    simpa [prefixWord, tailWord_7268738, baseEnd_7268738] using wordTrace_append hprefix tailTrace_7268738
  have hstable : (prefixWord ++ tailWord_7268738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268738).length < 2 ^ (prefixWord ++ tailWord_7268738).sum := by decide
  have hdescent : baseEnd_7268738 < baseStart_7268738 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268740 : List Nat := [2, 3, 2, 1, 1, 2, 2, 1, 1, 4, 4]
def baseStart_7268740 : Nat := 118140960795 + 7268740 * 2 ^ 59
def prefixEnd_7268740 : Nat := 4983230072969 + 3 ^ 40 * 7268740 * 2
def baseEnd_7268740 : Nat := 3732357372561996255021679

theorem tailTrace_7268740 : CollatzResearch.WordTrace tailWord_7268740 prefixEnd_7268740 3732357372561996255021679 := by
  unfold tailWord_7268740
  simp only [CollatzResearch.WordTrace]
  refine ⟨132556363843301928402025837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176741818457735904536034449 132556363843301928402025837)
  ·
    refine ⟨49708636441238223150759689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132556363843301928402025837 49708636441238223150759689)
    ·
      refine ⟨37281477330928667363069767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49708636441238223150759689 37281477330928667363069767)
      ·
        refine ⟨55922215996393001044604651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37281477330928667363069767 55922215996393001044604651)
        ·
          refine ⟨83883323994589501566906977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55922215996393001044604651 83883323994589501566906977)
          ·
            refine ⟨62912492995942126175180233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83883323994589501566906977 62912492995942126175180233)
            ·
              refine ⟨47184369746956594631385175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62912492995942126175180233 47184369746956594631385175)
              ·
                refine ⟨70776554620434891947077763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47184369746956594631385175 70776554620434891947077763)
                ·
                  refine ⟨106164831930652337920616645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70776554620434891947077763 106164831930652337920616645)
                  ·
                    refine ⟨19905905986997313360115621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106164831930652337920616645 19905905986997313360115621)
                    ·
                      refine ⟨3732357372561996255021679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19905905986997313360115621 3732357372561996255021679)
                      ·
                        rfl

theorem cell23_7268740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_7268740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268740 prefixEnd_7268740 := by exact prefixLift 7268740
  have htrace : WordTrace (prefixWord ++ tailWord_7268740) baseStart_7268740 baseEnd_7268740 := by
    simpa [prefixWord, tailWord_7268740, baseEnd_7268740] using wordTrace_append hprefix tailTrace_7268740
  have hstable : (prefixWord ++ tailWord_7268740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268740).length < 2 ^ (prefixWord ++ tailWord_7268740).sum := by decide
  have hdescent : baseEnd_7268740 < baseStart_7268740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268767 : List Nat := [1, 1, 2, 5, 1, 1, 2, 5, 5]
def baseStart_7268767 : Nat := 118140960795 + 7268767 * 2 ^ 59
def prefixEnd_7268767 : Nat := 4983230072969 + 3 ^ 40 * 7268767 * 2
def baseEnd_7268767 : Nat := 414707915171074183264895

theorem tailTrace_7268767 : CollatzResearch.WordTrace tailWord_7268767 prefixEnd_7268767 414707915171074183264895 := by
  unfold tailWord_7268767
  simp only [CollatzResearch.WordTrace]
  refine ⟨265113712457506040415284555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176742474971670693610189703 265113712457506040415284555)
  ·
    refine ⟨397670568686259060622926833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265113712457506040415284555 397670568686259060622926833)
    ·
      refine ⟨298252926514694295467195125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397670568686259060622926833 298252926514694295467195125)
      ·
        refine ⟨27961211860752590200049543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 298252926514694295467195125 27961211860752590200049543)
        ·
          refine ⟨41941817791128885300074315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27961211860752590200049543 41941817791128885300074315)
          ·
            refine ⟨62912726686693327950111473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41941817791128885300074315 62912726686693327950111473)
            ·
              refine ⟨47184545015019995962583605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62912726686693327950111473 47184545015019995962583605)
              ·
                refine ⟨4423551095158124621492213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47184545015019995962583605 4423551095158124621492213)
                ·
                  refine ⟨414707915171074183264895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4423551095158124621492213 414707915171074183264895)
                  ·
                    rfl

theorem cell23_7268767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 5, 5].length) (baseStart_7268767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268767 prefixEnd_7268767 := by exact prefixLift 7268767
  have htrace : WordTrace (prefixWord ++ tailWord_7268767) baseStart_7268767 baseEnd_7268767 := by
    simpa [prefixWord, tailWord_7268767, baseEnd_7268767] using wordTrace_append hprefix tailTrace_7268767
  have hstable : (prefixWord ++ tailWord_7268767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268767).length < 2 ^ (prefixWord ++ tailWord_7268767).sum := by decide
  have hdescent : baseEnd_7268767 < baseStart_7268767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268800 : List Nat := [2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 4]
def baseStart_7268800 : Nat := 118140960795 + 7268800 * 2 ^ 59
def prefixEnd_7268800 : Nat := 4983230072969 + 3 ^ 40 * 7268800 * 2
def baseEnd_7268800 : Nat := 3732388181401266020271403

theorem tailTrace_7268800 : CollatzResearch.WordTrace tailWord_7268800 prefixEnd_7268800 3732388181401266020271403 := by
  unfold tailWord_7268800
  simp only [CollatzResearch.WordTrace]
  refine ⟨132557458033193243525617927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176743277377590991367490569 132557458033193243525617927)
  ·
    refine ⟨198836187049789865288426891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132557458033193243525617927 198836187049789865288426891)
    ·
      refine ⟨298254280574684797932640337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198836187049789865288426891 298254280574684797932640337)
      ·
        refine ⟨223690710431013598449480253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298254280574684797932640337 223690710431013598449480253)
        ·
          refine ⟨83884016411630099418555095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223690710431013598449480253 83884016411630099418555095)
          ·
            refine ⟨125826024617445149127832643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83884016411630099418555095 125826024617445149127832643)
            ·
              refine ⟨188739036926167723691748965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125826024617445149127832643 188739036926167723691748965)
              ·
                refine ⟨35388569423656448192202931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188739036926167723691748965 35388569423656448192202931)
                ·
                  refine ⟨53082854135484672288304397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35388569423656448192202931 53082854135484672288304397)
                  ·
                    refine ⟨19906070300806752108114149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53082854135484672288304397 19906070300806752108114149)
                    ·
                      refine ⟨3732388181401266020271403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19906070300806752108114149 3732388181401266020271403)
                      ·
                        rfl

theorem cell23_7268800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_7268800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268800 prefixEnd_7268800 := by exact prefixLift 7268800
  have htrace : WordTrace (prefixWord ++ tailWord_7268800) baseStart_7268800 baseEnd_7268800 := by
    simpa [prefixWord, tailWord_7268800, baseEnd_7268800] using wordTrace_append hprefix tailTrace_7268800
  have hstable : (prefixWord ++ tailWord_7268800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268800).length < 2 ^ (prefixWord ++ tailWord_7268800).sum := by decide
  have hdescent : baseEnd_7268800 < baseStart_7268800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268801 : List Nat := [1, 2, 7, 1, 1, 1, 1, 2, 7]
def baseStart_7268801 : Nat := 118140960795 + 7268801 * 2 ^ 59
def prefixEnd_7268801 : Nat := 4983230072969 + 3 ^ 40 * 7268801 * 2
def baseEnd_7268801 : Nat := 414709854986880057373211

theorem tailTrace_7268801 : CollatzResearch.WordTrace tailWord_7268801 prefixEnd_7268801 414709854986880057373211 := by
  unfold tailWord_7268801
  simp only [CollatzResearch.WordTrace]
  refine ⟨265114952539382864222022257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176743301692921909481348171 265114952539382864222022257)
  ·
    refine ⟨198836214404537148166516693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265114952539382864222022257 198836214404537148166516693)
    ·
      refine ⟨4660223775106339410152735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 198836214404537148166516693 4660223775106339410152735)
      ·
        refine ⟨6990335662659509115229103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4660223775106339410152735 6990335662659509115229103)
        ·
          refine ⟨10485503493989263672843655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6990335662659509115229103 10485503493989263672843655)
          ·
            refine ⟨15728255240983895509265483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10485503493989263672843655 15728255240983895509265483)
            ·
              refine ⟨23592382861475843263898225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15728255240983895509265483 23592382861475843263898225)
              ·
                refine ⟨17694287146106882447923669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23592382861475843263898225 17694287146106882447923669)
                ·
                  refine ⟨414709854986880057373211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17694287146106882447923669 414709854986880057373211)
                  ·
                    rfl

theorem cell23_7268801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 7].length) (baseStart_7268801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268801 prefixEnd_7268801 := by exact prefixLift 7268801
  have htrace : WordTrace (prefixWord ++ tailWord_7268801) baseStart_7268801 baseEnd_7268801 := by
    simpa [prefixWord, tailWord_7268801, baseEnd_7268801] using wordTrace_append hprefix tailTrace_7268801
  have hstable : (prefixWord ++ tailWord_7268801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268801).length < 2 ^ (prefixWord ++ tailWord_7268801).sum := by decide
  have hdescent : baseEnd_7268801 < baseStart_7268801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268844 : List Nat := [2, 2, 1, 1, 2, 1, 3, 6, 1, 4]
def baseStart_7268844 : Nat := 118140960795 + 7268844 * 2 ^ 59
def prefixEnd_7268844 : Nat := 4983230072969 + 3 ^ 40 * 7268844 * 2
def baseEnd_7268844 : Nat := 1244136924850021282707067

theorem tailTrace_7268844 : CollatzResearch.WordTrace tailWord_7268844 prefixEnd_7268844 1244136924850021282707067 := by
  unfold tailWord_7268844
  simp only [CollatzResearch.WordTrace]
  refine ⟨132558260439113541282918793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176744347252151388377225057 132558260439113541282918793)
  ·
    refine ⟨99418695329335155962189095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132558260439113541282918793 99418695329335155962189095)
    ·
      refine ⟨149128042994002733943283643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99418695329335155962189095 149128042994002733943283643)
      ·
        refine ⟨223692064491004100914925465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149128042994002733943283643 223692064491004100914925465)
        ·
          refine ⟨167769048368253075686194099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223692064491004100914925465 167769048368253075686194099)
          ·
            refine ⟨251653572552379613529291149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167769048368253075686194099 251653572552379613529291149)
            ·
              refine ⟨94370089707142355073484181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 251653572552379613529291149 94370089707142355073484181)
              ·
                refine ⟨4423597955022297894069571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94370089707142355073484181 4423597955022297894069571)
                ·
                  refine ⟨6635396932533446841104357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4423597955022297894069571 6635396932533446841104357)
                  ·
                    refine ⟨1244136924850021282707067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6635396932533446841104357 1244136924850021282707067)
                    ·
                      rfl

theorem cell23_7268844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 6, 1, 4].length) (baseStart_7268844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268844 prefixEnd_7268844 := by exact prefixLift 7268844
  have htrace : WordTrace (prefixWord ++ tailWord_7268844) baseStart_7268844 baseEnd_7268844 := by
    simpa [prefixWord, tailWord_7268844, baseEnd_7268844] using wordTrace_append hprefix tailTrace_7268844
  have hstable : (prefixWord ++ tailWord_7268844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268844).length < 2 ^ (prefixWord ++ tailWord_7268844).sum := by decide
  have hdescent : baseEnd_7268844 < baseStart_7268844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268860 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 3, 2, 6]
def baseStart_7268860 : Nat := 118140960795 + 7268860 * 2 ^ 59
def prefixEnd_7268860 : Nat := 4983230072969 + 3 ^ 40 * 7268860 * 2
def baseEnd_7268860 : Nat := 3732418990240535785521127

theorem tailTrace_7268860 : CollatzResearch.WordTrace tailWord_7268860 prefixEnd_7268860 3732418990240535785521127 := by
  unfold tailWord_7268860
  simp only [CollatzResearch.WordTrace]
  refine ⟨132558552223084558649210017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176744736297446078198946689 132558552223084558649210017)
  ·
    refine ⟨99418914167313418986907513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132558552223084558649210017 99418914167313418986907513)
    ·
      refine ⟨74564185625485064240180635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99418914167313418986907513 74564185625485064240180635)
      ·
        refine ⟨111846278438227596360270953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74564185625485064240180635 111846278438227596360270953)
        ·
          refine ⟨83884708828670697270203215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111846278438227596360270953 83884708828670697270203215)
          ·
            refine ⟨125827063243006045905304823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83884708828670697270203215 125827063243006045905304823)
            ·
              refine ⟨188740594864509068857957235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125827063243006045905304823 188740594864509068857957235)
              ·
                refine ⟨283110892296763603286935853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188740594864509068857957235 283110892296763603286935853)
                ·
                  refine ⟨106166584611286351232600945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 283110892296763603286935853 106166584611286351232600945)
                  ·
                    refine ⟨79624938458464763424450709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106166584611286351232600945 79624938458464763424450709)
                    ·
                      refine ⟨3732418990240535785521127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79624938458464763424450709 3732418990240535785521127)
                      ·
                        rfl

theorem cell23_7268860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_7268860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268860 prefixEnd_7268860 := by exact prefixLift 7268860
  have htrace : WordTrace (prefixWord ++ tailWord_7268860) baseStart_7268860 baseEnd_7268860 := by
    simpa [prefixWord, tailWord_7268860, baseEnd_7268860] using wordTrace_append hprefix tailTrace_7268860
  have hstable : (prefixWord ++ tailWord_7268860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268860).length < 2 ^ (prefixWord ++ tailWord_7268860).sum := by decide
  have hdescent : baseEnd_7268860 < baseStart_7268860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268878 : List Nat := [4, 1, 1, 2, 3, 3, 1, 3, 1, 4]
def baseStart_7268878 : Nat := 118140960795 + 7268878 * 2 ^ 59
def prefixEnd_7268878 : Nat := 4983230072969 + 3 ^ 40 * 7268878 * 2
def baseEnd_7268878 : Nat := 1244142744297438905032015

theorem tailTrace_7268878 : CollatzResearch.WordTrace tailWord_7268878 prefixEnd_7268878 1244142744297438905032015 := by
  unfold tailWord_7268878
  simp only [CollatzResearch.WordTrace]
  refine ⟨33139720120012988296571911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176745173973402604248383525 33139720120012988296571911)
  ·
    refine ⟨49709580180019482444857867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33139720120012988296571911 49709580180019482444857867)
    ·
      refine ⟨74564370270029223667286801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49709580180019482444857867 74564370270029223667286801)
      ·
        refine ⟨55923277702521917750465101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74564370270029223667286801 55923277702521917750465101)
        ·
          refine ⟨20971229138445719156424413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55923277702521917750465101 20971229138445719156424413)
          ·
            refine ⟨7864210926917144683659155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20971229138445719156424413 7864210926917144683659155)
            ·
              refine ⟨11796316390375717025488733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7864210926917144683659155 11796316390375717025488733)
              ·
                refine ⟨4423618646390893884558275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11796316390375717025488733 4423618646390893884558275)
                ·
                  refine ⟨6635427969586340826837413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4423618646390893884558275 6635427969586340826837413)
                  ·
                    refine ⟨1244142744297438905032015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6635427969586340826837413 1244142744297438905032015)
                    ·
                      rfl

theorem cell23_7268878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 3, 1, 4].length) (baseStart_7268878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268878 prefixEnd_7268878 := by exact prefixLift 7268878
  have htrace : WordTrace (prefixWord ++ tailWord_7268878) baseStart_7268878 baseEnd_7268878 := by
    simpa [prefixWord, tailWord_7268878, baseEnd_7268878] using wordTrace_append hprefix tailTrace_7268878
  have hstable : (prefixWord ++ tailWord_7268878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268878).length < 2 ^ (prefixWord ++ tailWord_7268878).sum := by decide
  have hdescent : baseEnd_7268878 < baseStart_7268878 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268901 : List Nat := [1, 3, 1, 2, 2, 1, 2, 6, 1, 1, 3]
def baseStart_7268901 : Nat := 118140960795 + 7268901 * 2 ^ 59
def prefixEnd_7268901 : Nat := 4983230072969 + 3 ^ 40 * 7268901 * 2
def baseEnd_7268901 : Nat := 3732440042947370125108439

theorem tailTrace_7268901 : CollatzResearch.WordTrace tailWord_7268901 prefixEnd_7268901 3732440042947370125108439 := by
  unfold tailWord_7268901
  simp only [CollatzResearch.WordTrace]
  refine ⟨265118599839020581300662557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176745733226013720867108371 265118599839020581300662557)
  ·
    refine ⟨99419474939632717987748459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265118599839020581300662557 99419474939632717987748459)
    ·
      refine ⟨149129212409449076981622689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99419474939632717987748459 149129212409449076981622689)
      ·
        refine ⟨111846909307086807736217017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149129212409449076981622689 111846909307086807736217017)
        ·
          refine ⟨83885181980315105802162763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111846909307086807736217017 83885181980315105802162763)
          ·
            refine ⟨125827772970472658703244145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83885181980315105802162763 125827772970472658703244145)
            ·
              refine ⟨94370829727854494027433109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125827772970472658703244145 94370829727854494027433109)
              ·
                refine ⟨4423632643493179407535927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94370829727854494027433109 4423632643493179407535927)
                ·
                  refine ⟨6635448965239769111303891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4423632643493179407535927 6635448965239769111303891)
                  ·
                    refine ⟨9953173447859653666955837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6635448965239769111303891 9953173447859653666955837)
                    ·
                      refine ⟨3732440042947370125108439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9953173447859653666955837 3732440042947370125108439)
                      ·
                        rfl

theorem cell23_7268901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 6, 1, 1, 3].length) (baseStart_7268901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268901 prefixEnd_7268901 := by exact prefixLift 7268901
  have htrace : WordTrace (prefixWord ++ tailWord_7268901) baseStart_7268901 baseEnd_7268901 := by
    simpa [prefixWord, tailWord_7268901, baseEnd_7268901] using wordTrace_append hprefix tailTrace_7268901
  have hstable : (prefixWord ++ tailWord_7268901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268901).length < 2 ^ (prefixWord ++ tailWord_7268901).sum := by decide
  have hdescent : baseEnd_7268901 < baseStart_7268901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268917 : List Nat := [1, 3, 3, 1, 1, 2, 2, 3, 1, 6]
def baseStart_7268917 : Nat := 118140960795 + 7268917 * 2 ^ 59
def prefixEnd_7268917 : Nat := 4983230072969 + 3 ^ 40 * 7268917 * 2
def baseEnd_7268917 : Nat := 1244149419545947354169455

theorem tailTrace_7268917 : CollatzResearch.WordTrace tailWord_7268917 prefixEnd_7268917 1244149419545947354169455 := by
  unfold tailWord_7268917
  simp only [CollatzResearch.WordTrace]
  refine ⟨265119183406962616033245005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176746122271308410688830003 265119183406962616033245005)
  ·
    refine ⟨99419693777610981012466877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265119183406962616033245005 99419693777610981012466877)
    ·
      refine ⟨37282385166604117879675079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99419693777610981012466877 37282385166604117879675079)
      ·
        refine ⟨55923577749906176819512619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37282385166604117879675079 55923577749906176819512619)
        ·
          refine ⟨83885366624859265229268929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55923577749906176819512619 83885366624859265229268929)
          ·
            refine ⟨62914024968644448921951697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83885366624859265229268929 62914024968644448921951697)
            ·
              refine ⟨47185518726483336691463773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62914024968644448921951697 47185518726483336691463773)
              ·
                refine ⟨17694569522431251259298915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47185518726483336691463773 17694569522431251259298915)
                ·
                  refine ⟨26541854283646876888948373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17694569522431251259298915 26541854283646876888948373)
                  ·
                    refine ⟨1244149419545947354169455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26541854283646876888948373 1244149419545947354169455)
                    ·
                      rfl

theorem cell23_7268917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_7268917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268917 prefixEnd_7268917 := by exact prefixLift 7268917
  have htrace : WordTrace (prefixWord ++ tailWord_7268917) baseStart_7268917 baseEnd_7268917 := by
    simpa [prefixWord, tailWord_7268917, baseEnd_7268917] using wordTrace_append hprefix tailTrace_7268917
  have hstable : (prefixWord ++ tailWord_7268917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268917).length < 2 ^ (prefixWord ++ tailWord_7268917).sum := by decide
  have hdescent : baseEnd_7268917 < baseStart_7268917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268924 : List Nat := [2, 2, 2, 2, 3, 2, 1, 1, 3, 1, 4]
def baseStart_7268924 : Nat := 118140960795 + 7268924 * 2 ^ 59
def prefixEnd_7268924 : Nat := 4983230072969 + 3 ^ 40 * 7268924 * 2
def baseEnd_7268924 : Nat := 3732451853002423535120833

theorem tailTrace_7268924 : CollatzResearch.WordTrace tailWord_7268924 prefixEnd_7268924 3732451853002423535120833 := by
  unfold tailWord_7268924
  simp only [CollatzResearch.WordTrace]
  refine ⟨132559719358968628114374913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176746292478624837485833217 132559719358968628114374913)
  ·
    refine ⟨99419789519226471085781185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132559719358968628114374913 99419789519226471085781185)
    ·
      refine ⟨74564842139419853314335889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99419789519226471085781185 74564842139419853314335889)
      ·
        refine ⟨55923631604564889985751917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74564842139419853314335889 55923631604564889985751917)
        ·
          refine ⟨20971361851711833744656969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55923631604564889985751917 20971361851711833744656969)
          ·
            refine ⟨15728521388783875308492727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20971361851711833744656969 15728521388783875308492727)
            ·
              refine ⟨23592782083175812962739091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15728521388783875308492727 23592782083175812962739091)
              ·
                refine ⟨35389173124763719444108637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23592782083175812962739091 35389173124763719444108637)
                ·
                  refine ⟨13270939921786394791540739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35389173124763719444108637 13270939921786394791540739)
                  ·
                    refine ⟨19906409882679592187311109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13270939921786394791540739 19906409882679592187311109)
                    ·
                      refine ⟨3732451853002423535120833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19906409882679592187311109 3732451853002423535120833)
                      ·
                        rfl

theorem cell23_7268924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_7268924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268924 prefixEnd_7268924 := by exact prefixLift 7268924
  have htrace : WordTrace (prefixWord ++ tailWord_7268924) baseStart_7268924 baseEnd_7268924 := by
    simpa [prefixWord, tailWord_7268924, baseEnd_7268924] using wordTrace_append hprefix tailTrace_7268924
  have hstable : (prefixWord ++ tailWord_7268924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268924).length < 2 ^ (prefixWord ++ tailWord_7268924).sum := by decide
  have hdescent : baseEnd_7268924 < baseStart_7268924 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7268981 : List Nat := [1, 3, 4, 2, 2, 1, 3, 7]
def baseStart_7268981 : Nat := 118140960795 + 7268981 * 2 ^ 59
def prefixEnd_7268981 : Nat := 4983230072969 + 3 ^ 40 * 7268981 * 2
def baseEnd_7268981 : Nat := 138240041533323326374373

theorem tailTrace_7268981 : CollatzResearch.WordTrace tailWord_7268981 prefixEnd_7268981 138240041533323326374373 := by
  unfold tailWord_7268981
  simp only [CollatzResearch.WordTrace]
  refine ⟨265121517678730754963574797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176747678452487169975716531 265121517678730754963574797)
  ·
    refine ⟨99420569129524033111340549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265121517678730754963574797 99420569129524033111340549)
    ·
      refine ⟨18641356711785756208376353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99420569129524033111340549 18641356711785756208376353)
      ·
        refine ⟨13981017533839317156282265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18641356711785756208376353 13981017533839317156282265)
        ·
          refine ⟨10485763150379487867211699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13981017533839317156282265 10485763150379487867211699)
          ·
            refine ⟨15728644725569231800817549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10485763150379487867211699 15728644725569231800817549)
            ·
              refine ⟨5898241772088461925306581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15728644725569231800817549 5898241772088461925306581)
              ·
                refine ⟨138240041533323326374373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5898241772088461925306581 138240041533323326374373)
                ·
                  rfl

theorem cell23_7268981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 7].length) (baseStart_7268981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7268981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7268981 prefixEnd_7268981 := by exact prefixLift 7268981
  have htrace : WordTrace (prefixWord ++ tailWord_7268981) baseStart_7268981 baseEnd_7268981 := by
    simpa [prefixWord, tailWord_7268981, baseEnd_7268981] using wordTrace_append hprefix tailTrace_7268981
  have hstable : (prefixWord ++ tailWord_7268981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7268981).length < 2 ^ (prefixWord ++ tailWord_7268981).sum := by decide
  have hdescent : baseEnd_7268981 < baseStart_7268981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7268981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269025 : List Nat := [1, 2, 3, 3, 3, 1, 3, 1, 2, 1, 3]
def baseStart_7269025 : Nat := 118140960795 + 7269025 * 2 ^ 59
def prefixEnd_7269025 : Nat := 4983230072969 + 3 ^ 40 * 7269025 * 2
def baseEnd_7269025 : Nat := 3732503714548527639957869

theorem tailTrace_7269025 : CollatzResearch.WordTrace tailWord_7269025 prefixEnd_7269025 3732503714548527639957869 := by
  unfold tailWord_7269025
  simp only [CollatzResearch.WordTrace]
  refine ⟨265123122490571350478176529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176748748327047566985451019 265123122490571350478176529)
  ·
    refine ⟨198842341867928512858632397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265123122490571350478176529 198842341867928512858632397)
    ·
      refine ⟨74565878200473192321987149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198842341867928512858632397 74565878200473192321987149)
      ·
        refine ⟨27962204325177447120745181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74565878200473192321987149 27962204325177447120745181)
        ·
          refine ⟨10485826621941542670279443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27962204325177447120745181 10485826621941542670279443)
          ·
            refine ⟨15728739932912314005419165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10485826621941542670279443 15728739932912314005419165)
            ·
              refine ⟨5898277474842117752032187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15728739932912314005419165 5898277474842117752032187)
              ·
                refine ⟨8847416212263176628048281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5898277474842117752032187 8847416212263176628048281)
                ·
                  refine ⟨6635562159197382471036211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8847416212263176628048281 6635562159197382471036211)
                  ·
                    refine ⟨9953343238796073706554317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6635562159197382471036211 9953343238796073706554317)
                    ·
                      refine ⟨3732503714548527639957869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9953343238796073706554317 3732503714548527639957869)
                      ·
                        rfl

theorem cell23_7269025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_7269025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269025 prefixEnd_7269025 := by exact prefixLift 7269025
  have htrace : WordTrace (prefixWord ++ tailWord_7269025) baseStart_7269025 baseEnd_7269025 := by
    simpa [prefixWord, tailWord_7269025, baseEnd_7269025] using wordTrace_append hprefix tailTrace_7269025
  have hstable : (prefixWord ++ tailWord_7269025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269025).length < 2 ^ (prefixWord ++ tailWord_7269025).sum := by decide
  have hdescent : baseEnd_7269025 < baseStart_7269025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269027 : List Nat := [1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 4]
def baseStart_7269027 : Nat := 118140960795 + 7269027 * 2 ^ 59
def prefixEnd_7269027 : Nat := 4983230072969 + 3 ^ 40 * 7269027 * 2
def baseEnd_7269027 : Nat := 3732504741509836632132859

theorem tailTrace_7269027 : CollatzResearch.WordTrace tailWord_7269027 prefixEnd_7269027 3732504741509836632132859 := by
  unfold tailWord_7269027
  simp only [CollatzResearch.WordTrace]
  refine ⟨265123195436564104819749335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176748796957709403213166223 265123195436564104819749335)
  ·
    refine ⟨397684793154846157229624003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265123195436564104819749335 397684793154846157229624003)
    ·
      refine ⟨596527189732269235844436005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397684793154846157229624003 596527189732269235844436005)
      ·
        refine ⟨111848848074800481720831751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 596527189732269235844436005 111848848074800481720831751)
        ·
          refine ⟨167773272112200722581247627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111848848074800481720831751 167773272112200722581247627)
          ·
            refine ⟨251659908168301083871871441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167773272112200722581247627 251659908168301083871871441)
            ·
              refine ⟨188744931126225812903903581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251659908168301083871871441 188744931126225812903903581)
              ·
                refine ⟨70779349172334679838963843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188744931126225812903903581 70779349172334679838963843)
                ·
                  refine ⟨106169023758502019758445765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70779349172334679838963843 106169023758502019758445765)
                  ·
                    refine ⟨19906691954719128704708581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106169023758502019758445765 19906691954719128704708581)
                    ·
                      refine ⟨3732504741509836632132859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19906691954719128704708581 3732504741509836632132859)
                      ·
                        rfl

theorem cell23_7269027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_7269027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269027 prefixEnd_7269027 := by exact prefixLift 7269027
  have htrace : WordTrace (prefixWord ++ tailWord_7269027) baseStart_7269027 baseEnd_7269027 := by
    simpa [prefixWord, tailWord_7269027, baseEnd_7269027] using wordTrace_append hprefix tailTrace_7269027
  have hstable : (prefixWord ++ tailWord_7269027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269027).length < 2 ^ (prefixWord ++ tailWord_7269027).sum := by decide
  have hdescent : baseEnd_7269027 < baseStart_7269027 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269097 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 2, 8]
def baseStart_7269097 : Nat := 118140960795 + 7269097 * 2 ^ 59
def prefixEnd_7269097 : Nat := 4983230072969 + 3 ^ 40 * 7269097 * 2
def baseEnd_7269097 : Nat := 1244180228385217119419179

theorem tailTrace_7269097 : CollatzResearch.WordTrace tailWord_7269097 prefixEnd_7269097 1244180228385217119419179 := by
  unfold tailWord_7269097
  simp only [CollatzResearch.WordTrace]
  refine ⟨265125748546310506774797545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176750499030873671183198363 265125748546310506774797545)
  ·
    refine ⟨198844311409732880081098159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265125748546310506774797545 198844311409732880081098159)
    ·
      refine ⟨298266467114599320121647239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198844311409732880081098159 298266467114599320121647239)
      ·
        refine ⟨447399700671898980182470859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298266467114599320121647239 447399700671898980182470859)
        ·
          refine ⟨671099551007848470273706289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447399700671898980182470859 671099551007848470273706289)
          ·
            refine ⟨503324663255886352705279717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 671099551007848470273706289 503324663255886352705279717)
            ·
              refine ⟨94373374360478691132239947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 503324663255886352705279717 94373374360478691132239947)
              ·
                refine ⟨141560061540718036698359921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94373374360478691132239947 141560061540718036698359921)
                ·
                  refine ⟨106170046155538527523769941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141560061540718036698359921 106170046155538527523769941)
                  ·
                    refine ⟨1244180228385217119419179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 106170046155538527523769941 1244180228385217119419179)
                    ·
                      rfl

theorem cell23_7269097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 8].length) (baseStart_7269097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269097 prefixEnd_7269097 := by exact prefixLift 7269097
  have htrace : WordTrace (prefixWord ++ tailWord_7269097) baseStart_7269097 baseEnd_7269097 := by
    simpa [prefixWord, tailWord_7269097, baseEnd_7269097] using wordTrace_append hprefix tailTrace_7269097
  have hstable : (prefixWord ++ tailWord_7269097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269097).length < 2 ^ (prefixWord ++ tailWord_7269097).sum := by decide
  have hdescent : baseEnd_7269097 < baseStart_7269097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269101 : List Nat := [1, 5, 1, 2, 1, 1, 4, 1, 2, 5]
def baseStart_7269101 : Nat := 118140960795 + 7269101 * 2 ^ 59
def prefixEnd_7269101 : Nat := 4983230072969 + 3 ^ 40 * 7269101 * 2
def baseEnd_7269101 : Nat := 1244180913026089780869173

theorem tailTrace_7269101 : CollatzResearch.WordTrace tailWord_7269101 prefixEnd_7269101 1244180913026089780869173 := by
  unfold tailWord_7269101
  simp only [CollatzResearch.WordTrace]
  refine ⟨265125894438296015457943157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176750596292197343638628771 265125894438296015457943157)
  ·
    refine ⟨24855552603590251449182171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 265125894438296015457943157 24855552603590251449182171)
    ·
      refine ⟨37283328905385377173773257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24855552603590251449182171 37283328905385377173773257)
      ·
        refine ⟨27962496679039032880329943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37283328905385377173773257 27962496679039032880329943)
        ·
          refine ⟨41943745018558549320494915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27962496679039032880329943 41943745018558549320494915)
          ·
            refine ⟨62915617527837823980742373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41943745018558549320494915 62915617527837823980742373)
            ·
              refine ⟨11796678286469591996389195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62915617527837823980742373 11796678286469591996389195)
              ·
                refine ⟨17695017429704387994583793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11796678286469591996389195 17695017429704387994583793)
                ·
                  refine ⟨13271263072278290995937845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17695017429704387994583793 13271263072278290995937845)
                  ·
                    refine ⟨1244180913026089780869173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13271263072278290995937845 1244180913026089780869173)
                    ·
                      rfl

theorem cell23_7269101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_7269101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269101 prefixEnd_7269101 := by exact prefixLift 7269101
  have htrace : WordTrace (prefixWord ++ tailWord_7269101) baseStart_7269101 baseEnd_7269101 := by
    simpa [prefixWord, tailWord_7269101, baseEnd_7269101] using wordTrace_append hprefix tailTrace_7269101
  have hstable : (prefixWord ++ tailWord_7269101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269101).length < 2 ^ (prefixWord ++ tailWord_7269101).sum := by decide
  have hdescent : baseEnd_7269101 < baseStart_7269101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269121 : List Nat := [1, 2, 4, 1, 1, 1, 1, 4, 2, 4, 2]
def baseStart_7269121 : Nat := 118140960795 + 7269121 * 2 ^ 59
def prefixEnd_7269121 : Nat := 4983230072969 + 3 ^ 40 * 7269121 * 2
def baseEnd_7269121 : Nat := 3732553008691359264357427

theorem tailTrace_7269121 : CollatzResearch.WordTrace tailWord_7269121 prefixEnd_7269121 3732553008691359264357427 := by
  unfold tailWord_7269121
  simp only [CollatzResearch.WordTrace]
  refine ⟨265126623898223558873671217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176751082598815705915780811 265126623898223558873671217)
  ·
    refine ⟨198844967923667669155253413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265126623898223558873671217 198844967923667669155253413)
    ·
      refine ⟨37283431485687687966610015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198844967923667669155253413 37283431485687687966610015)
      ·
        refine ⟨55925147228531531949915023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37283431485687687966610015 55925147228531531949915023)
        ·
          refine ⟨83887720842797297924872535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55925147228531531949915023 83887720842797297924872535)
          ·
            refine ⟨125831581264195946887308803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83887720842797297924872535 125831581264195946887308803)
            ·
              refine ⟨188747371896293920330963205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125831581264195946887308803 188747371896293920330963205)
              ·
                refine ⟨35390132230555110062055601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188747371896293920330963205 35390132230555110062055601)
                ·
                  refine ⟨26542599172916332546541701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35390132230555110062055601 26542599172916332546541701)
                  ·
                    refine ⟨4976737344921812352476569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26542599172916332546541701 4976737344921812352476569)
                    ·
                      refine ⟨3732553008691359264357427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4976737344921812352476569 3732553008691359264357427)
                      ·
                        rfl

theorem cell23_7269121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_7269121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269121 prefixEnd_7269121 := by exact prefixLift 7269121
  have htrace : WordTrace (prefixWord ++ tailWord_7269121) baseStart_7269121 baseEnd_7269121 := by
    simpa [prefixWord, tailWord_7269121, baseEnd_7269121] using wordTrace_append hprefix tailTrace_7269121
  have hstable : (prefixWord ++ tailWord_7269121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269121).length < 2 ^ (prefixWord ++ tailWord_7269121).sum := by decide
  have hdescent : baseEnd_7269121 < baseStart_7269121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269124 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 2, 3, 5]
def baseStart_7269124 : Nat := 118140960795 + 7269124 * 2 ^ 59
def prefixEnd_7269124 : Nat := 4983230072969 + 3 ^ 40 * 7269124 * 2
def baseEnd_7269124 : Nat := 3732554549133322752619913

theorem tailTrace_7269124 : CollatzResearch.WordTrace tailWord_7269124 prefixEnd_7269124 3732554549133322752619913 := by
  unfold tailWord_7269124
  simp only [CollatzResearch.WordTrace]
  refine ⟨132563366658606345193015213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176751155544808460257353617 132563366658606345193015213)
  ·
    refine ⟨49711262496977379447380705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132563366658606345193015213 49711262496977379447380705)
    ·
      refine ⟨37283446872733034585535529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49711262496977379447380705 37283446872733034585535529)
      ·
        refine ⟨27962585154549775939151647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37283446872733034585535529 27962585154549775939151647)
        ·
          refine ⟨41943877731824663908727471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27962585154549775939151647 41943877731824663908727471)
          ·
            refine ⟨62915816597736995863091207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41943877731824663908727471 62915816597736995863091207)
            ·
              refine ⟨94373724896605493794636811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62915816597736995863091207 94373724896605493794636811)
              ·
                refine ⟨141560587344908240691955217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94373724896605493794636811 141560587344908240691955217)
                ·
                  refine ⟨106170440508681180518966413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141560587344908240691955217 106170440508681180518966413)
                  ·
                    refine ⟨39813915190755442694612405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 106170440508681180518966413 39813915190755442694612405)
                    ·
                      refine ⟨3732554549133322752619913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39813915190755442694612405 3732554549133322752619913)
                      ·
                        rfl

theorem cell23_7269124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_7269124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269124 prefixEnd_7269124 := by exact prefixLift 7269124
  have htrace : WordTrace (prefixWord ++ tailWord_7269124) baseStart_7269124 baseEnd_7269124 := by
    simpa [prefixWord, tailWord_7269124, baseEnd_7269124] using wordTrace_append hprefix tailTrace_7269124
  have hstable : (prefixWord ++ tailWord_7269124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269124).length < 2 ^ (prefixWord ++ tailWord_7269124).sum := by decide
  have hdescent : baseEnd_7269124 < baseStart_7269124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269134 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4]
def baseStart_7269134 : Nat := 118140960795 + 7269134 * 2 ^ 59
def prefixEnd_7269134 : Nat := 4983230072969 + 3 ^ 40 * 7269134 * 2
def baseEnd_7269134 : Nat := 3732559683939867713494867

theorem tailTrace_7269134 : CollatzResearch.WordTrace tailWord_7269134 prefixEnd_7269134 3732559683939867713494867 := by
  unfold tailWord_7269134
  simp only [CollatzResearch.WordTrace]
  refine ⟨33140887255897057761736807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176751398698117641395929637 33140887255897057761736807)
  ·
    refine ⟨49711330883845586642605211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33140887255897057761736807 49711330883845586642605211)
    ·
      refine ⟨74566996325768379963907817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49711330883845586642605211 74566996325768379963907817)
      ·
        refine ⟨55925247244326284972930863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74566996325768379963907817 55925247244326284972930863)
        ·
          refine ⟨83887870866489427459396295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55925247244326284972930863 83887870866489427459396295)
          ·
            refine ⟨125831806299734141189094443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83887870866489427459396295 125831806299734141189094443)
            ·
              refine ⟨188747709449601211783641665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125831806299734141189094443 188747709449601211783641665)
              ·
                refine ⟨141560782087200908837731249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188747709449601211783641665 141560782087200908837731249)
                ·
                  refine ⟨106170586565400681628298437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141560782087200908837731249 106170586565400681628298437)
                  ·
                    refine ⟨19906984981012627805305957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106170586565400681628298437 19906984981012627805305957)
                    ·
                      refine ⟨3732559683939867713494867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19906984981012627805305957 3732559683939867713494867)
                      ·
                        rfl

theorem cell23_7269134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_7269134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269134 prefixEnd_7269134 := by exact prefixLift 7269134
  have htrace : WordTrace (prefixWord ++ tailWord_7269134) baseStart_7269134 baseEnd_7269134 := by
    simpa [prefixWord, tailWord_7269134, baseEnd_7269134] using wordTrace_append hprefix tailTrace_7269134
  have hstable : (prefixWord ++ tailWord_7269134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269134).length < 2 ^ (prefixWord ++ tailWord_7269134).sum := by decide
  have hdescent : baseEnd_7269134 < baseStart_7269134 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269178 : List Nat := [3, 1, 1, 1, 6, 2, 1, 2, 6]
def baseStart_7269178 : Nat := 118140960795 + 7269178 * 2 ^ 59
def prefixEnd_7269178 : Nat := 4983230072969 + 3 ^ 40 * 7269178 * 2
def baseEnd_7269178 : Nat := 414731364120962837927185

theorem tailTrace_7269178 : CollatzResearch.WordTrace tailWord_7269178 prefixEnd_7269178 414731364120962837927185 := by
  unfold tailWord_7269178
  simp only [CollatzResearch.WordTrace]
  refine ⟨66282175714754264402124047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176752468572678038405664125 66282175714754264402124047)
  ·
    refine ⟨99423263572131396603186071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66282175714754264402124047 99423263572131396603186071)
    ·
      refine ⟨149134895358197094904779107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99423263572131396603186071 149134895358197094904779107)
      ·
        refine ⟨223702343037295642357168661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149134895358197094904779107 223702343037295642357168661)
        ·
          refine ⟨10486047329873233235492281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 223702343037295642357168661 10486047329873233235492281)
          ·
            refine ⟨7864535497404924926619211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10486047329873233235492281 7864535497404924926619211)
            ·
              refine ⟨11796803246107387389928817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7864535497404924926619211 11796803246107387389928817)
              ·
                refine ⟨8847602434580540542446613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11796803246107387389928817 8847602434580540542446613)
                ·
                  refine ⟨414731364120962837927185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8847602434580540542446613 414731364120962837927185)
                  ·
                    rfl

theorem cell23_7269178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 6].length) (baseStart_7269178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269178 prefixEnd_7269178 := by exact prefixLift 7269178
  have htrace : WordTrace (prefixWord ++ tailWord_7269178) baseStart_7269178 baseEnd_7269178 := by
    simpa [prefixWord, tailWord_7269178, baseEnd_7269178] using wordTrace_append hprefix tailTrace_7269178
  have hstable : (prefixWord ++ tailWord_7269178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269178).length < 2 ^ (prefixWord ++ tailWord_7269178).sum := by decide
  have hdescent : baseEnd_7269178 < baseStart_7269178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269194 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 2, 5, 4]
def baseStart_7269194 : Nat := 118140960795 + 7269194 * 2 ^ 59
def prefixEnd_7269194 : Nat := 4983230072969 + 3 ^ 40 * 7269194 * 2
def baseEnd_7269194 : Nat := 3732590492779137478744591

theorem tailTrace_7269194 : CollatzResearch.WordTrace tailWord_7269194 prefixEnd_7269194 3732590492779137478744591 := by
  unfold tailWord_7269194
  simp only [CollatzResearch.WordTrace]
  refine ⟨66282321606739773085269659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176752857617972728227385757 66282321606739773085269659)
  ·
    refine ⟨99423482410109659627904489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66282321606739773085269659 99423482410109659627904489)
    ·
      refine ⟨74567611807582244720928367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99423482410109659627904489 74567611807582244720928367)
      ·
        refine ⟨111851417711373367081392551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74567611807582244720928367 111851417711373367081392551)
        ·
          refine ⟨167777126567060050622088827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111851417711373367081392551 167777126567060050622088827)
          ·
            refine ⟨251665689850590075933133241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167777126567060050622088827 251665689850590075933133241)
            ·
              refine ⟨188749267387942556949849931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251665689850590075933133241 188749267387942556949849931)
              ·
                refine ⟨283123901081913835424774897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188749267387942556949849931 283123901081913835424774897)
                ·
                  refine ⟨212342925811435376568581173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283123901081913835424774897 212342925811435376568581173)
                  ·
                    refine ⟨19907149294822066553304485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 212342925811435376568581173 19907149294822066553304485)
                    ·
                      refine ⟨3732590492779137478744591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19907149294822066553304485 3732590492779137478744591)
                      ·
                        rfl

theorem cell23_7269194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_7269194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269194 prefixEnd_7269194 := by exact prefixLift 7269194
  have htrace : WordTrace (prefixWord ++ tailWord_7269194) baseStart_7269194 baseEnd_7269194 := by
    simpa [prefixWord, tailWord_7269194, baseEnd_7269194] using wordTrace_append hprefix tailTrace_7269194
  have hstable : (prefixWord ++ tailWord_7269194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269194).length < 2 ^ (prefixWord ++ tailWord_7269194).sum := by decide
  have hdescent : baseEnd_7269194 < baseStart_7269194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269221 : List Nat := [1, 3, 1, 3, 1, 1, 3, 2, 4, 4]
def baseStart_7269221 : Nat := 118140960795 + 7269221 * 2 ^ 59
def prefixEnd_7269221 : Nat := 4983230072969 + 3 ^ 40 * 7269221 * 2
def baseEnd_7269221 : Nat := 1244201452252269624368989

theorem tailTrace_7269221 : CollatzResearch.WordTrace tailWord_7269221 prefixEnd_7269221 1244201452252269624368989 := by
  unfold tailWord_7269221
  simp only [CollatzResearch.WordTrace]
  refine ⟨265130271197861275952311517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176753514131907517301541011 265130271197861275952311517)
  ·
    refine ⟨99423851699197978482116819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265130271197861275952311517 99423851699197978482116819)
    ·
      refine ⟨149135777548796967723175229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99423851699197978482116819 149135777548796967723175229)
      ·
        refine ⟨55925916580798862896190711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149135777548796967723175229 55925916580798862896190711)
        ·
          refine ⟨83888874871198294344286067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55925916580798862896190711 83888874871198294344286067)
          ·
            refine ⟨125833312306797441516429101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83888874871198294344286067 125833312306797441516429101)
            ·
              refine ⟨47187492115049040568660913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125833312306797441516429101 47187492115049040568660913)
              ·
                refine ⟨35390619086286780426495685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47187492115049040568660913 35390619086286780426495685)
                ·
                  refine ⟨6635741078678771329967941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35390619086286780426495685 6635741078678771329967941)
                  ·
                    refine ⟨1244201452252269624368989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6635741078678771329967941 1244201452252269624368989)
                    ·
                      rfl

theorem cell23_7269221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 4, 4].length) (baseStart_7269221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269221 prefixEnd_7269221 := by exact prefixLift 7269221
  have htrace : WordTrace (prefixWord ++ tailWord_7269221) baseStart_7269221 baseEnd_7269221 := by
    simpa [prefixWord, tailWord_7269221, baseEnd_7269221] using wordTrace_append hprefix tailTrace_7269221
  have hstable : (prefixWord ++ tailWord_7269221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269221).length < 2 ^ (prefixWord ++ tailWord_7269221).sum := by decide
  have hdescent : baseEnd_7269221 < baseStart_7269221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269234 : List Nat := [3, 2, 1, 2, 1, 1, 13]
def baseStart_7269234 : Nat := 118140960795 + 7269234 * 2 ^ 59
def prefixEnd_7269234 : Nat := 4983230072969 + 3 ^ 40 * 7269234 * 2
def baseEnd_7269234 : Nat := 46081617679077991632647

theorem tailTrace_7269234 : CollatzResearch.WordTrace tailWord_7269234 prefixEnd_7269234 46081617679077991632647 := by
  unfold tailWord_7269234
  simp only [CollatzResearch.WordTrace]
  refine ⟨66282686336703544793133689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176753830231209452781689837 66282686336703544793133689)
  ·
    refine ⟨49712014752527658594850267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66282686336703544793133689 49712014752527658594850267)
    ·
      refine ⟨74568022128791487892275401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49712014752527658594850267 74568022128791487892275401)
      ·
        refine ⟨55926016596593615919206551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74568022128791487892275401 55926016596593615919206551)
        ·
          refine ⟨83889024894890423878809827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55926016596593615919206551 83889024894890423878809827)
          ·
            refine ⟨125833537342335635818214741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83889024894890423878809827 125833537342335635818214741)
            ·
              refine ⟨46081617679077991632647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 125833537342335635818214741 46081617679077991632647)
              ·
                rfl

theorem cell23_7269234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 13].length) (baseStart_7269234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269234 prefixEnd_7269234 := by exact prefixLift 7269234
  have htrace : WordTrace (prefixWord ++ tailWord_7269234) baseStart_7269234 baseEnd_7269234 := by
    simpa [prefixWord, tailWord_7269234, baseEnd_7269234] using wordTrace_append hprefix tailTrace_7269234
  have hstable : (prefixWord ++ tailWord_7269234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269234).length < 2 ^ (prefixWord ++ tailWord_7269234).sum := by decide
  have hdescent : baseEnd_7269234 < baseStart_7269234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269245 : List Nat := [1, 4, 1, 1, 2, 1, 5, 1, 3, 2, 2]
def baseStart_7269245 : Nat := 118140960795 + 7269245 * 2 ^ 59
def prefixEnd_7269245 : Nat := 4983230072969 + 3 ^ 40 * 7269245 * 2
def baseEnd_7269245 : Nat := 3732616680292516779206857

theorem tailTrace_7269245 : CollatzResearch.WordTrace tailWord_7269245 prefixEnd_7269245 3732616680292516779206857 := by
  unfold tailWord_7269245
  simp only [CollatzResearch.WordTrace]
  refine ⟨265131146549774328051185189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176754097699849552034123459 265131146549774328051185189)
  ·
    refine ⟨49712089978082686509597223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265131146549774328051185189 49712089978082686509597223)
    ·
      refine ⟨74568134967124029764395835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49712089978082686509597223 74568134967124029764395835)
      ·
        refine ⟨111852202450686044646593753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74568134967124029764395835 111852202450686044646593753)
        ·
          refine ⟨83889151838014533484945315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111852202450686044646593753 83889151838014533484945315)
          ·
            refine ⟨125833727757021800227417973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83889151838014533484945315 125833727757021800227417973)
            ·
              refine ⟨11796911977220793771320435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125833727757021800227417973 11796911977220793771320435)
              ·
                refine ⟨17695367965831190656980653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11796911977220793771320435 17695367965831190656980653)
                ·
                  refine ⟨6635762987186696496367745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17695367965831190656980653 6635762987186696496367745)
                  ·
                    refine ⟨4976822240390022372275809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6635762987186696496367745 4976822240390022372275809)
                    ·
                      refine ⟨3732616680292516779206857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4976822240390022372275809 3732616680292516779206857)
                      ·
                        rfl

theorem cell23_7269245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 3, 2, 2].length) (baseStart_7269245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269245 prefixEnd_7269245 := by exact prefixLift 7269245
  have htrace : WordTrace (prefixWord ++ tailWord_7269245) baseStart_7269245 baseEnd_7269245 := by
    simpa [prefixWord, tailWord_7269245, baseEnd_7269245] using wordTrace_append hprefix tailTrace_7269245
  have hstable : (prefixWord ++ tailWord_7269245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269245).length < 2 ^ (prefixWord ++ tailWord_7269245).sum := by decide
  have hdescent : baseEnd_7269245 < baseStart_7269245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269255 : List Nat := [1, 1, 4, 2, 3, 1, 4, 1, 2, 4]
def baseStart_7269255 : Nat := 118140960795 + 7269255 * 2 ^ 59
def prefixEnd_7269255 : Nat := 4983230072969 + 3 ^ 40 * 7269255 * 2
def baseEnd_7269255 : Nat := 1244207271699687246693937

theorem tailTrace_7269255 : CollatzResearch.WordTrace tailWord_7269255 prefixEnd_7269255 1244207271699687246693937 := by
  unfold tailWord_7269255
  simp only [CollatzResearch.WordTrace]
  refine ⟨265131511279738099759049219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176754340853158733172699479 265131511279738099759049219)
  ·
    refine ⟨397697266919607149638573829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265131511279738099759049219 397697266919607149638573829)
    ·
      refine ⟨74568237547426340557232593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 397697266919607149638573829 74568237547426340557232593)
      ·
        refine ⟨55926178160569755417924445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74568237547426340557232593 55926178160569755417924445)
        ·
          refine ⟨20972316810213658281721667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55926178160569755417924445 20972316810213658281721667)
          ·
            refine ⟨31458475215320487422582501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20972316810213658281721667 31458475215320487422582501)
            ·
              refine ⟨5898464102872591391734219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31458475215320487422582501 5898464102872591391734219)
              ·
                refine ⟨8847696154308887087601329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5898464102872591391734219 8847696154308887087601329)
                ·
                  refine ⟨6635772115731665315700997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8847696154308887087601329 6635772115731665315700997)
                  ·
                    refine ⟨1244207271699687246693937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6635772115731665315700997 1244207271699687246693937)
                    ·
                      rfl

theorem cell23_7269255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 2, 4].length) (baseStart_7269255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269255 prefixEnd_7269255 := by exact prefixLift 7269255
  have htrace : WordTrace (prefixWord ++ tailWord_7269255) baseStart_7269255 baseEnd_7269255 := by
    simpa [prefixWord, tailWord_7269255, baseEnd_7269255] using wordTrace_append hprefix tailTrace_7269255
  have hstable : (prefixWord ++ tailWord_7269255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269255).length < 2 ^ (prefixWord ++ tailWord_7269255).sum := by decide
  have hdescent : baseEnd_7269255 < baseStart_7269255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269282 : List Nat := [3, 3, 1, 2, 2, 2, 3, 1, 1, 2, 3]
def baseStart_7269282 : Nat := 118140960795 + 7269282 * 2 ^ 59
def prefixEnd_7269282 : Nat := 4983230072969 + 3 ^ 40 * 7269282 * 2
def baseEnd_7269282 : Nat := 3732635679076733134444187

theorem tailTrace_7269282 : CollatzResearch.WordTrace tailWord_7269282 prefixEnd_7269282 3732635679076733134444187 := by
  unfold tailWord_7269282
  simp only [CollatzResearch.WordTrace]
  refine ⟨66283124012660070842570525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176754997367093522246854733 66283124012660070842570525)
  ·
    refine ⟨24856171504747526565963947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66283124012660070842570525 24856171504747526565963947)
    ·
      refine ⟨37284257257121289848945921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24856171504747526565963947 37284257257121289848945921)
      ·
        refine ⟨27963192942840967386709441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37284257257121289848945921 27963192942840967386709441)
        ·
          refine ⟨20972394707130725540032081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27963192942840967386709441 20972394707130725540032081)
          ·
            refine ⟨15729296030348044155024061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20972394707130725540032081 15729296030348044155024061)
            ·
              refine ⟨5898486011380516558134023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15729296030348044155024061 5898486011380516558134023)
              ·
                refine ⟨8847729017070774837201035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5898486011380516558134023 8847729017070774837201035)
                ·
                  refine ⟨13271593525606162255801553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8847729017070774837201035 13271593525606162255801553)
                  ·
                    refine ⟨9953695144204621691851165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13271593525606162255801553 9953695144204621691851165)
                    ·
                      refine ⟨3732635679076733134444187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9953695144204621691851165 3732635679076733134444187)
                      ·
                        rfl

theorem cell23_7269282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_7269282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269282 prefixEnd_7269282 := by exact prefixLift 7269282
  have htrace : WordTrace (prefixWord ++ tailWord_7269282) baseStart_7269282 baseEnd_7269282 := by
    simpa [prefixWord, tailWord_7269282, baseEnd_7269282] using wordTrace_append hprefix tailTrace_7269282
  have hstable : (prefixWord ++ tailWord_7269282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269282).length < 2 ^ (prefixWord ++ tailWord_7269282).sum := by decide
  have hdescent : baseEnd_7269282 < baseStart_7269282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269301 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 1, 5, 4]
def baseStart_7269301 : Nat := 118140960795 + 7269301 * 2 ^ 59
def prefixEnd_7269301 : Nat := 4983230072969 + 3 ^ 40 * 7269301 * 2
def baseEnd_7269301 : Nat := 3732645435209168560106599

theorem tailTrace_7269301 : CollatzResearch.WordTrace tailWord_7269301 prefixEnd_7269301 3732645435209168560106599 := by
  unfold tailWord_7269301
  simp only [CollatzResearch.WordTrace]
  refine ⟨265133189037571449615223757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176755459358380966410149171 265133189037571449615223757)
  ·
    refine ⟨99424945889089293605708909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265133189037571449615223757 99424945889089293605708909)
    ·
      refine ⟨37284354708408485102140841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99424945889089293605708909 37284354708408485102140841)
      ·
        refine ⟨27963266031306363826605631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37284354708408485102140841 27963266031306363826605631)
        ·
          refine ⟨41944899046959545739908447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27963266031306363826605631 41944899046959545739908447)
          ·
            refine ⟨62917348570439318609862671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41944899046959545739908447 62917348570439318609862671)
            ·
              refine ⟨94376022855658977914794007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62917348570439318609862671 94376022855658977914794007)
              ·
                refine ⟨141564034283488466872191011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94376022855658977914794007 141564034283488466872191011)
                ·
                  refine ⟨212346051425232700308286517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141564034283488466872191011 212346051425232700308286517)
                  ·
                    refine ⟨19907442321115565653901861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 212346051425232700308286517 19907442321115565653901861)
                    ·
                      refine ⟨3732645435209168560106599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19907442321115565653901861 3732645435209168560106599)
                      ·
                        rfl

theorem cell23_7269301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_7269301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269301 prefixEnd_7269301 := by exact prefixLift 7269301
  have htrace : WordTrace (prefixWord ++ tailWord_7269301) baseStart_7269301 baseEnd_7269301 := by
    simpa [prefixWord, tailWord_7269301, baseEnd_7269301] using wordTrace_append hprefix tailTrace_7269301
  have hstable : (prefixWord ++ tailWord_7269301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269301).length < 2 ^ (prefixWord ++ tailWord_7269301).sum := by decide
  have hdescent : baseEnd_7269301 < baseStart_7269301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269352 : List Nat := [2, 1, 4, 1, 1, 1, 5, 2, 2, 2, 2]
def baseStart_7269352 : Nat := 118140960795 + 7269352 * 2 ^ 59
def prefixEnd_7269352 : Nat := 4983230072969 + 3 ^ 40 * 7269352 * 2
def baseEnd_7269352 : Nat := 3732671622722547860568865

theorem tailTrace_7269352 : CollatzResearch.WordTrace tailWord_7269352 prefixEnd_7269352 3732671622722547860568865 := by
  unfold tailWord_7269352
  simp only [CollatzResearch.WordTrace]
  refine ⟨132567524580193342662665155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176756699440257790216886873 132567524580193342662665155)
  ·
    refine ⟨198851286870290013993997733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132567524580193342662665155 198851286870290013993997733)
    ·
      refine ⟨37284616288179377623874575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198851286870290013993997733 37284616288179377623874575)
      ·
        refine ⟨55926924432269066435811863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37284616288179377623874575 55926924432269066435811863)
        ·
          refine ⟨83890386648403599653717795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55926924432269066435811863 83890386648403599653717795)
          ·
            refine ⟨125835579972605399480576693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83890386648403599653717795 125835579972605399480576693)
            ·
              refine ⟨11797085622431756201304065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125835579972605399480576693 11797085622431756201304065)
              ·
                refine ⟨8847814216823817150978049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11797085622431756201304065 8847814216823817150978049)
                ·
                  refine ⟨6635860662617862863233537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8847814216823817150978049 6635860662617862863233537)
                  ·
                    refine ⟨4976895496963397147425153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6635860662617862863233537 4976895496963397147425153)
                    ·
                      refine ⟨3732671622722547860568865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4976895496963397147425153 3732671622722547860568865)
                      ·
                        rfl

theorem cell23_7269352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_7269352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269352 prefixEnd_7269352 := by exact prefixLift 7269352
  have htrace : WordTrace (prefixWord ++ tailWord_7269352) baseStart_7269352 baseEnd_7269352 := by
    simpa [prefixWord, tailWord_7269352, baseEnd_7269352] using wordTrace_append hprefix tailTrace_7269352
  have hstable : (prefixWord ++ tailWord_7269352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269352).length < 2 ^ (prefixWord ++ tailWord_7269352).sum := by decide
  have hdescent : baseEnd_7269352 < baseStart_7269352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269405 : List Nat := [1, 4, 2, 2, 3, 1, 1, 2, 2, 5]
def baseStart_7269405 : Nat := 118140960795 + 7269405 * 2 ^ 59
def prefixEnd_7269405 : Nat := 4983230072969 + 3 ^ 40 * 7269405 * 2
def baseEnd_7269405 : Nat := 1244232945732412051068707

theorem tailTrace_7269405 : CollatzResearch.WordTrace tailWord_7269405 prefixEnd_7269405 1244232945732412051068707 := by
  unfold tailWord_7269405
  simp only [CollatzResearch.WordTrace]
  refine ⟨265136982229194675377009669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176757988152796450251339779 265136982229194675377009669)
  ·
    refine ⟨49713184167974001633189313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265136982229194675377009669 49713184167974001633189313)
    ·
      refine ⟨37284888125980501224891985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49713184167974001633189313 37284888125980501224891985)
      ·
        refine ⟨27963666094485375918668989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37284888125980501224891985 27963666094485375918668989)
        ·
          refine ⟨10486374785432015969500871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27963666094485375918668989 10486374785432015969500871)
          ·
            refine ⟨15729562178148023954251307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10486374785432015969500871 15729562178148023954251307)
            ·
              refine ⟨23594343267222035931376961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15729562178148023954251307 23594343267222035931376961)
              ·
                refine ⟨17695757450416526948532721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23594343267222035931376961 17695757450416526948532721)
                ·
                  refine ⟨13271818087812395211399541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17695757450416526948532721 13271818087812395211399541)
                  ·
                    refine ⟨1244232945732412051068707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13271818087812395211399541 1244232945732412051068707)
                    ·
                      rfl

theorem cell23_7269405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_7269405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269405 prefixEnd_7269405 := by exact prefixLift 7269405
  have htrace : WordTrace (prefixWord ++ tailWord_7269405) baseStart_7269405 baseEnd_7269405 := by
    simpa [prefixWord, tailWord_7269405, baseEnd_7269405] using wordTrace_append hprefix tailTrace_7269405
  have hstable : (prefixWord ++ tailWord_7269405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269405).length < 2 ^ (prefixWord ++ tailWord_7269405).sum := by decide
  have hdescent : baseEnd_7269405 < baseStart_7269405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269415 : List Nat := [1, 1, 7, 1, 1, 2, 1, 1, 1, 2, 5]
def baseStart_7269415 : Nat := 118140960795 + 7269415 * 2 ^ 59
def prefixEnd_7269415 : Nat := 4983230072969 + 3 ^ 40 * 7269415 * 2
def baseEnd_7269415 : Nat := 3732703972003781114081075

theorem tailTrace_7269415 : CollatzResearch.WordTrace tailWord_7269415 prefixEnd_7269415 3732703972003781114081075 := by
  unfold tailWord_7269415
  simp only [CollatzResearch.WordTrace]
  refine ⟨265137346959158447084873699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176758231306105631389915799 265137346959158447084873699)
  ·
    refine ⟨397706020438737670627310549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265137346959158447084873699 397706020438737670627310549)
    ·
      refine ⟨9321234854032914155327591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 397706020438737670627310549 9321234854032914155327591)
      ·
        refine ⟨13981852281049371232991387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9321234854032914155327591 13981852281049371232991387)
        ·
          refine ⟨20972778421574056849487081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13981852281049371232991387 20972778421574056849487081)
          ·
            refine ⟨15729583816180542637115311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20972778421574056849487081 15729583816180542637115311)
            ·
              refine ⟨23594375724270813955672967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15729583816180542637115311 23594375724270813955672967)
              ·
                refine ⟨35391563586406220933509451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23594375724270813955672967 35391563586406220933509451)
                ·
                  refine ⟨53087345379609331400264177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35391563586406220933509451 53087345379609331400264177)
                  ·
                    refine ⟨39815509034706998550198133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53087345379609331400264177 39815509034706998550198133)
                    ·
                      refine ⟨3732703972003781114081075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39815509034706998550198133 3732703972003781114081075)
                      ·
                        rfl

theorem cell23_7269415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_7269415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269415 prefixEnd_7269415 := by exact prefixLift 7269415
  have htrace : WordTrace (prefixWord ++ tailWord_7269415) baseStart_7269415 baseEnd_7269415 := by
    simpa [prefixWord, tailWord_7269415, baseEnd_7269415] using wordTrace_append hprefix tailTrace_7269415
  have hstable : (prefixWord ++ tailWord_7269415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269415).length < 2 ^ (prefixWord ++ tailWord_7269415).sum := by decide
  have hdescent : baseEnd_7269415 < baseStart_7269415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269468 : List Nat := [2, 2, 4, 1, 1, 1, 2, 1, 1, 2, 6]
def baseStart_7269468 : Nat := 118140960795 + 7269468 * 2 ^ 59
def prefixEnd_7269468 : Nat := 4983230072969 + 3 ^ 40 * 7269468 * 2
def baseEnd_7269468 : Nat := 3732731186478469406718331

theorem tailTrace_7269468 : CollatzResearch.WordTrace tailWord_7269468 prefixEnd_7269468 3732731186478469406718331 := by
  unfold tailWord_7269468
  simp only [CollatzResearch.WordTrace]
  refine ⟨132569640013983218568276529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176759520018644291424368705 132569640013983218568276529)
  ·
    refine ⟨99427230010487413926207397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132569640013983218568276529 99427230010487413926207397)
    ·
      refine ⟨18642605626966390111163887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99427230010487413926207397 18642605626966390111163887)
      ·
        refine ⟨27963908440449585166745831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18642605626966390111163887 27963908440449585166745831)
        ·
          refine ⟨41945862660674377750118747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27963908440449585166745831 41945862660674377750118747)
          ·
            refine ⟨62918793991011566625178121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41945862660674377750118747 62918793991011566625178121)
            ·
              refine ⟨47189095493258674968883591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62918793991011566625178121 47189095493258674968883591)
              ·
                refine ⟨70783643239888012453325387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47189095493258674968883591 70783643239888012453325387)
                ·
                  refine ⟨106175464859832018679988081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70783643239888012453325387 106175464859832018679988081)
                  ·
                    refine ⟨79631598644874014009991061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106175464859832018679988081 79631598644874014009991061)
                    ·
                      refine ⟨3732731186478469406718331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79631598644874014009991061 3732731186478469406718331)
                      ·
                        rfl

theorem cell23_7269468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_7269468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269468 prefixEnd_7269468 := by exact prefixLift 7269468
  have htrace : WordTrace (prefixWord ++ tailWord_7269468) baseStart_7269468 baseEnd_7269468 := by
    simpa [prefixWord, tailWord_7269468, baseEnd_7269468] using wordTrace_append hprefix tailTrace_7269468
  have hstable : (prefixWord ++ tailWord_7269468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269468).length < 2 ^ (prefixWord ++ tailWord_7269468).sum := by decide
  have hdescent : baseEnd_7269468 < baseStart_7269468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269475 : List Nat := [1, 1, 1, 5, 1, 1, 1, 5, 3, 1, 3]
def baseStart_7269475 : Nat := 118140960795 + 7269475 * 2 ^ 59
def prefixEnd_7269475 : Nat := 4983230072969 + 3 ^ 40 * 7269475 * 2
def baseEnd_7269475 : Nat := 3732734780843050879330799

theorem tailTrace_7269475 : CollatzResearch.WordTrace tailWord_7269475 prefixEnd_7269475 3732734780843050879330799 := by
  unfold tailWord_7269475
  simp only [CollatzResearch.WordTrace]
  refine ⟨265139535338941077332057879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176759690225960718221371919 265139535338941077332057879)
  ·
    refine ⟨397709303008411615998086819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265139535338941077332057879 397709303008411615998086819)
    ·
      refine ⟨596563954512617423997130229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397709303008411615998086819 596563954512617423997130229)
      ·
        refine ⟨55927870735557883499730959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 596563954512617423997130229 55927870735557883499730959)
        ·
          refine ⟨83891806103336825249596439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55927870735557883499730959 83891806103336825249596439)
          ·
            refine ⟨125837709155005237874394659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83891806103336825249596439 125837709155005237874394659)
            ·
              refine ⟨188756563732507856811591989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125837709155005237874394659 188756563732507856811591989)
              ·
                refine ⟨17695927849922611576086749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 188756563732507856811591989 17695927849922611576086749)
                ·
                  refine ⟨6635972943720979341032531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17695927849922611576086749 6635972943720979341032531)
                  ·
                    refine ⟨9953959415581469011548797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6635972943720979341032531 9953959415581469011548797)
                    ·
                      refine ⟨3732734780843050879330799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9953959415581469011548797 3732734780843050879330799)
                      ·
                        rfl

theorem cell23_7269475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_7269475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269475 prefixEnd_7269475 := by exact prefixLift 7269475
  have htrace : WordTrace (prefixWord ++ tailWord_7269475) baseStart_7269475 baseEnd_7269475 := by
    simpa [prefixWord, tailWord_7269475, baseEnd_7269475] using wordTrace_append hprefix tailTrace_7269475
  have hstable : (prefixWord ++ tailWord_7269475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269475).length < 2 ^ (prefixWord ++ tailWord_7269475).sum := by decide
  have hdescent : baseEnd_7269475 < baseStart_7269475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269512 : List Nat := [2, 1, 3, 4, 2, 1, 1, 3, 1, 5]
def baseStart_7269512 : Nat := 118140960795 + 7269512 * 2 ^ 59
def prefixEnd_7269512 : Nat := 4983230072969 + 3 ^ 40 * 7269512 * 2
def baseEnd_7269512 : Nat := 1244251259875755744856043

theorem tailTrace_7269512 : CollatzResearch.WordTrace tailWord_7269512 prefixEnd_7269512 1244251259875755744856043 := by
  unfold tailWord_7269512
  simp only [CollatzResearch.WordTrace]
  refine ⟨132570442419903516325577395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176760589893204688434103193 132570442419903516325577395)
  ·
    refine ⟨198855663629855274488366093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132570442419903516325577395 198855663629855274488366093)
    ·
      refine ⟨74570873861195727933137285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198855663629855274488366093 74570873861195727933137285)
      ·
        refine ⟨13982038848974198987463241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74570873861195727933137285 13982038848974198987463241)
        ·
          refine ⟨10486529136730649240597431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13982038848974198987463241 10486529136730649240597431)
          ·
            refine ⟨15729793705095973860896147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10486529136730649240597431 15729793705095973860896147)
            ·
              refine ⟨23594690557643960791344221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15729793705095973860896147 23594690557643960791344221)
              ·
                refine ⟨8848008959116485296754083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23594690557643960791344221 8848008959116485296754083)
                ·
                  refine ⟨13272013438674727945131125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8848008959116485296754083 13272013438674727945131125)
                  ·
                    refine ⟨1244251259875755744856043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13272013438674727945131125 1244251259875755744856043)
                    ·
                      rfl

theorem cell23_7269512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_7269512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269512 prefixEnd_7269512 := by exact prefixLift 7269512
  have htrace : WordTrace (prefixWord ++ tailWord_7269512) baseStart_7269512 baseEnd_7269512 := by
    simpa [prefixWord, tailWord_7269512, baseEnd_7269512] using wordTrace_append hprefix tailTrace_7269512
  have hstable : (prefixWord ++ tailWord_7269512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269512).length < 2 ^ (prefixWord ++ tailWord_7269512).sum := by decide
  have hdescent : baseEnd_7269512 < baseStart_7269512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269525 : List Nat := [1, 3, 2, 1, 1, 1, 2, 6, 2, 4]
def baseStart_7269525 : Nat := 118140960795 + 7269525 * 2 ^ 59
def prefixEnd_7269525 : Nat := 4983230072969 + 3 ^ 40 * 7269525 * 2
def baseEnd_7269525 : Nat := 1244253484958591894568523

theorem tailTrace_7269525 : CollatzResearch.WordTrace tailWord_7269525 prefixEnd_7269525 1244253484958591894568523 := by
  unfold tailWord_7269525
  simp only [CollatzResearch.WordTrace]
  refine ⟨265141358988759935871378029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176760905992506623914252019 265141358988759935871378029)
  ·
    refine ⟨99428009620784975951766761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265141358988759935871378029 99428009620784975951766761)
    ·
      refine ⟨74571007215588731963825071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99428009620784975951766761 74571007215588731963825071)
      ·
        refine ⟨111856510823383097945737607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74571007215588731963825071 111856510823383097945737607)
        ·
          refine ⟨167784766235074646918606411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111856510823383097945737607 167784766235074646918606411)
          ·
            refine ⟨251677149352611970377909617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167784766235074646918606411 251677149352611970377909617)
            ·
              refine ⟨188757862014458977783432213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251677149352611970377909617 188757862014458977783432213)
              ·
                refine ⟨8848024781927764583598385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 188757862014458977783432213 8848024781927764583598385)
                ·
                  refine ⟨6636018586445823437698789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8848024781927764583598385 6636018586445823437698789)
                  ·
                    refine ⟨1244253484958591894568523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6636018586445823437698789 1244253484958591894568523)
                    ·
                      rfl

theorem cell23_7269525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_7269525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269525 prefixEnd_7269525 := by exact prefixLift 7269525
  have htrace : WordTrace (prefixWord ++ tailWord_7269525) baseStart_7269525 baseEnd_7269525 := by
    simpa [prefixWord, tailWord_7269525, baseEnd_7269525] using wordTrace_append hprefix tailTrace_7269525
  have hstable : (prefixWord ++ tailWord_7269525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269525).length < 2 ^ (prefixWord ++ tailWord_7269525).sum := by decide
  have hdescent : baseEnd_7269525 < baseStart_7269525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269549 : List Nat := [1, 5, 2, 1, 3, 1, 2, 2, 1, 1, 4]
def baseStart_7269549 : Nat := 118140960795 + 7269549 * 2 ^ 59
def prefixEnd_7269549 : Nat := 4983230072969 + 3 ^ 40 * 7269549 * 2
def baseEnd_7269549 : Nat := 3732772778411483589805459

theorem tailTrace_7269549 : CollatzResearch.WordTrace tailWord_7269549 prefixEnd_7269549 3732772778411483589805459 := by
  unfold tailWord_7269549
  simp only [CollatzResearch.WordTrace]
  refine ⟨265142234340672987970251701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176761489560448658646834467 265142234340672987970251701)
  ·
    refine ⟨24857084469438092622211097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 265142234340672987970251701 24857084469438092622211097)
    ·
      refine ⟨18642813352078569466658323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24857084469438092622211097 18642813352078569466658323)
      ·
        refine ⟨27964220028117854199987485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18642813352078569466658323 27964220028117854199987485)
        ·
          refine ⟨10486582510544195324995307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27964220028117854199987485 10486582510544195324995307)
          ·
            refine ⟨15729873765816292987492961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10486582510544195324995307 15729873765816292987492961)
            ·
              refine ⟨11797405324362219740619721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15729873765816292987492961 11797405324362219740619721)
              ·
                refine ⟨8848053993271664805464791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11797405324362219740619721 8848053993271664805464791)
                ·
                  refine ⟨13272080989907497208197187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8848053993271664805464791 13272080989907497208197187)
                  ·
                    refine ⟨19908121484861245812295781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13272080989907497208197187 19908121484861245812295781)
                    ·
                      refine ⟨3732772778411483589805459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19908121484861245812295781 3732772778411483589805459)
                      ·
                        rfl

theorem cell23_7269549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_7269549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269549 prefixEnd_7269549 := by exact prefixLift 7269549
  have htrace : WordTrace (prefixWord ++ tailWord_7269549) baseStart_7269549 baseEnd_7269549 := by
    simpa [prefixWord, tailWord_7269549, baseEnd_7269549] using wordTrace_append hprefix tailTrace_7269549
  have hstable : (prefixWord ++ tailWord_7269549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269549).length < 2 ^ (prefixWord ++ tailWord_7269549).sum := by decide
  have hdescent : baseEnd_7269549 < baseStart_7269549 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269565 : List Nat := [1, 4, 1, 2, 1, 1, 2, 4, 1, 3, 3]
def baseStart_7269565 : Nat := 118140960795 + 7269565 * 2 ^ 59
def prefixEnd_7269565 : Nat := 4983230072969 + 3 ^ 40 * 7269565 * 2
def baseEnd_7269565 : Nat := 3732780994101955527205385

theorem tailTrace_7269565 : CollatzResearch.WordTrace tailWord_7269565 prefixEnd_7269565 3732780994101955527205385 := by
  unfold tailWord_7269565
  simp only [CollatzResearch.WordTrace]
  refine ⟨265142817908615022702834149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176761878605743348468556099 265142817908615022702834149)
  ·
    refine ⟨49714278357865316756781403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265142817908615022702834149 49714278357865316756781403)
    ·
      refine ⟨74571417536797975135172105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49714278357865316756781403 74571417536797975135172105)
      ·
        refine ⟨55928563152598481351379079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74571417536797975135172105 55928563152598481351379079)
        ·
          refine ⟨83892844728897722027068619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55928563152598481351379079 83892844728897722027068619)
          ·
            refine ⟨125839267093346583040602929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83892844728897722027068619 125839267093346583040602929)
            ·
              refine ⟨94379450320009937280452197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125839267093346583040602929 94379450320009937280452197)
              ·
                refine ⟨17696146935001863240084787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94379450320009937280452197 17696146935001863240084787)
                ·
                  refine ⟨26544220402502794860127181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17696146935001863240084787 26544220402502794860127181)
                  ·
                    refine ⟨9954082650938548072547693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26544220402502794860127181 9954082650938548072547693)
                    ·
                      refine ⟨3732780994101955527205385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9954082650938548072547693 3732780994101955527205385)
                      ·
                        rfl

theorem cell23_7269565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_7269565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269565 prefixEnd_7269565 := by exact prefixLift 7269565
  have htrace : WordTrace (prefixWord ++ tailWord_7269565) baseStart_7269565 baseEnd_7269565 := by
    simpa [prefixWord, tailWord_7269565, baseEnd_7269565] using wordTrace_append hprefix tailTrace_7269565
  have hstable : (prefixWord ++ tailWord_7269565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269565).length < 2 ^ (prefixWord ++ tailWord_7269565).sum := by decide
  have hdescent : baseEnd_7269565 < baseStart_7269565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269569 : List Nat := [1, 2, 6, 1, 1, 1, 2, 3, 1, 2, 3]
def baseStart_7269569 : Nat := 118140960795 + 7269569 * 2 ^ 59
def prefixEnd_7269569 : Nat := 4983230072969 + 3 ^ 40 * 7269569 * 2
def baseEnd_7269569 : Nat := 3732783048024573511555367

theorem tailTrace_7269569 : CollatzResearch.WordTrace tailWord_7269569 prefixEnd_7269569 3732783048024573511555367 := by
  unfold tailWord_7269569
  simp only [CollatzResearch.WordTrace]
  refine ⟨265142963800600531385979761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176761975867067020923986507 265142963800600531385979761)
  ·
    refine ⟨198857222850450398539484821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265142963800600531385979761 198857222850450398539484821)
    ·
      refine ⟨9321432321114862431538351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 198857222850450398539484821 9321432321114862431538351)
      ·
        refine ⟨13982148481672293647307527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9321432321114862431538351 13982148481672293647307527)
        ·
          refine ⟨20973222722508440470961291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13982148481672293647307527 20973222722508440470961291)
          ·
            refine ⟨31459834083762660706441937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20973222722508440470961291 31459834083762660706441937)
            ·
              refine ⟨23594875562821995529831453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31459834083762660706441937 23594875562821995529831453)
              ·
                refine ⟨8848078336058248323686795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23594875562821995529831453 8848078336058248323686795)
                ·
                  refine ⟨13272117504087372485530193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8848078336058248323686795 13272117504087372485530193)
                  ·
                    refine ⟨9954088128065529364147645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13272117504087372485530193 9954088128065529364147645)
                    ·
                      refine ⟨3732783048024573511555367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9954088128065529364147645 3732783048024573511555367)
                      ·
                        rfl

theorem cell23_7269569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_7269569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269569 prefixEnd_7269569 := by exact prefixLift 7269569
  have htrace : WordTrace (prefixWord ++ tailWord_7269569) baseStart_7269569 baseEnd_7269569 := by
    simpa [prefixWord, tailWord_7269569, baseEnd_7269569] using wordTrace_append hprefix tailTrace_7269569
  have hstable : (prefixWord ++ tailWord_7269569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269569).length < 2 ^ (prefixWord ++ tailWord_7269569).sum := by decide
  have hdescent : baseEnd_7269569 < baseStart_7269569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269572 : List Nat := [2, 3, 3, 1, 4, 1, 9]
def baseStart_7269572 : Nat := 118140960795 + 7269572 * 2 ^ 59
def prefixEnd_7269572 : Nat := 4983230072969 + 3 ^ 40 * 7269572 * 2
def baseEnd_7269572 : Nat := 46083760351438728392813

theorem tailTrace_7269572 : CollatzResearch.WordTrace tailWord_7269572 prefixEnd_7269572 46083760351438728392813 := by
  unfold tailWord_7269572
  simp only [CollatzResearch.WordTrace]
  refine ⟨132571536609794831449169485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176762048813059775265559313 132571536609794831449169485)
  ·
    refine ⟨49714326228673061793438557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132571536609794831449169485 49714326228673061793438557)
    ·
      refine ⟨18642872335752398172539459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49714326228673061793438557 18642872335752398172539459)
      ·
        refine ⟨27964308503628597258809189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18642872335752398172539459 27964308503628597258809189)
        ·
          refine ⟨5243307844430361986026723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27964308503628597258809189 5243307844430361986026723)
          ·
            refine ⟨7864961766645542979040085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5243307844430361986026723 7864961766645542979040085)
            ·
              refine ⟨46083760351438728392813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7864961766645542979040085 46083760351438728392813)
              ·
                rfl

theorem cell23_7269572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 9].length) (baseStart_7269572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269572 prefixEnd_7269572 := by exact prefixLift 7269572
  have htrace : WordTrace (prefixWord ++ tailWord_7269572) baseStart_7269572 baseEnd_7269572 := by
    simpa [prefixWord, tailWord_7269572, baseEnd_7269572] using wordTrace_append hprefix tailTrace_7269572
  have hstable : (prefixWord ++ tailWord_7269572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269572).length < 2 ^ (prefixWord ++ tailWord_7269572).sum := by decide
  have hdescent : baseEnd_7269572 < baseStart_7269572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269599 : List Nat := [1, 1, 2, 3, 2, 1, 6, 1, 2, 1, 3]
def baseStart_7269599 : Nat := 118140960795 + 7269599 * 2 ^ 59
def prefixEnd_7269599 : Nat := 4983230072969 + 3 ^ 40 * 7269599 * 2
def baseEnd_7269599 : Nat := 3732798452444208394180229

theorem tailTrace_7269599 : CollatzResearch.WordTrace tailWord_7269599 prefixEnd_7269599 3732798452444208394180229 := by
  unfold tailWord_7269599
  simp only [CollatzResearch.WordTrace]
  refine ⟨265144057990491846509571851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176762705326994564339714567 265144057990491846509571851)
  ·
    refine ⟨397716086985737769764357777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265144057990491846509571851 397716086985737769764357777)
    ·
      refine ⟨298287065239303327323268333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397716086985737769764357777 298287065239303327323268333)
      ·
        refine ⟨111857649464738747746225625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298287065239303327323268333 111857649464738747746225625)
        ·
          refine ⟨83893237098554060809669219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111857649464738747746225625 83893237098554060809669219)
          ·
            refine ⟨125839855647831091214503829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83893237098554060809669219 125839855647831091214503829)
            ·
              refine ⟨5898743233492082400679867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 125839855647831091214503829 5898743233492082400679867)
              ·
                refine ⟨8848114850238123601019801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5898743233492082400679867 8848114850238123601019801)
                ·
                  refine ⟨6636086137678592700764851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8848114850238123601019801 6636086137678592700764851)
                  ·
                    refine ⟨9954129206517889051147277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6636086137678592700764851 9954129206517889051147277)
                    ·
                      refine ⟨3732798452444208394180229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9954129206517889051147277 3732798452444208394180229)
                      ·
                        rfl

theorem cell23_7269599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 2, 1, 3].length) (baseStart_7269599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269599 prefixEnd_7269599 := by exact prefixLift 7269599
  have htrace : WordTrace (prefixWord ++ tailWord_7269599) baseStart_7269599 baseEnd_7269599 := by
    simpa [prefixWord, tailWord_7269599, baseEnd_7269599] using wordTrace_append hprefix tailTrace_7269599
  have hstable : (prefixWord ++ tailWord_7269599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269599).length < 2 ^ (prefixWord ++ tailWord_7269599).sum := by decide
  have hdescent : baseEnd_7269599 < baseStart_7269599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269620 : List Nat := [2, 6, 1, 2, 1, 1, 3, 1, 1, 2, 3]
def baseStart_7269620 : Nat := 118140960795 + 7269620 * 2 ^ 59
def prefixEnd_7269620 : Nat := 4983230072969 + 3 ^ 40 * 7269620 * 2
def baseEnd_7269620 : Nat := 3732809235537952812017633

theorem tailTrace_7269620 : CollatzResearch.WordTrace tailWord_7269620 prefixEnd_7269620 3732809235537952812017633 := by
  unfold tailWord_7269620
  simp only [CollatzResearch.WordTrace]
  refine ⟨132572411961707883548043157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176763215948943844730724209 132572411961707883548043157)
  ·
    refine ⟨6214331810705057041314523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 132572411961707883548043157 6214331810705057041314523)
    ·
      refine ⟨9321497716057585561971785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6214331810705057041314523 9321497716057585561971785)
      ·
        refine ⟨6991123287043189171478839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9321497716057585561971785 6991123287043189171478839)
        ·
          refine ⟨10486684930564783757218259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6991123287043189171478839 10486684930564783757218259)
          ·
            refine ⟨15730027395847175635827389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10486684930564783757218259 15730027395847175635827389)
            ·
              refine ⟨5898760273442690863435271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15730027395847175635827389 5898760273442690863435271)
              ·
                refine ⟨8848140410164036295152907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5898760273442690863435271 8848140410164036295152907)
                ·
                  refine ⟨13272210615246054442729361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8848140410164036295152907 13272210615246054442729361)
                  ·
                    refine ⟨9954157961434540832047021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13272210615246054442729361 9954157961434540832047021)
                    ·
                      refine ⟨3732809235537952812017633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9954157961434540832047021 3732809235537952812017633)
                      ·
                        rfl

theorem cell23_7269620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_7269620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269620 prefixEnd_7269620 := by exact prefixLift 7269620
  have htrace : WordTrace (prefixWord ++ tailWord_7269620) baseStart_7269620 baseEnd_7269620 := by
    simpa [prefixWord, tailWord_7269620, baseEnd_7269620] using wordTrace_append hprefix tailTrace_7269620
  have hstable : (prefixWord ++ tailWord_7269620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269620).length < 2 ^ (prefixWord ++ tailWord_7269620).sum := by decide
  have hdescent : baseEnd_7269620 < baseStart_7269620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269712 : List Nat := [2, 1, 1, 1, 1, 5, 1, 3, 2, 4, 2]
def baseStart_7269712 : Nat := 118140960795 + 7269712 * 2 ^ 59
def prefixEnd_7269712 : Nat := 4983230072969 + 3 ^ 40 * 7269712 * 2
def baseEnd_7269712 : Nat := 3732856475758166452067209

theorem tailTrace_7269712 : CollatzResearch.WordTrace tailWord_7269712 prefixEnd_7269712 3732856475758166452067209 := by
  unfold tailWord_7269712
  simp only [CollatzResearch.WordTrace]
  refine ⟨132574089719541233404217695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176765452959388311205623593 132574089719541233404217695)
  ·
    refine ⟨198861134579311850106326543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132574089719541233404217695 198861134579311850106326543)
    ·
      refine ⟨298291701868967775159489815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198861134579311850106326543 298291701868967775159489815)
      ·
        refine ⟨447437552803451662739234723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298291701868967775159489815 447437552803451662739234723)
        ·
          refine ⟨671156329205177494108852085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447437552803451662739234723 671156329205177494108852085)
          ·
            refine ⟨62920905862985390072704883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 671156329205177494108852085 62920905862985390072704883)
            ·
              refine ⟨94381358794478085109057325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62920905862985390072704883 94381358794478085109057325)
              ·
                refine ⟨35393009547929281915896497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94381358794478085109057325 35393009547929281915896497)
                ·
                  refine ⟨26544757160946961436922373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35393009547929281915896497 26544757160946961436922373)
                  ·
                    refine ⟨4977141967677555269422945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26544757160946961436922373 4977141967677555269422945)
                    ·
                      refine ⟨3732856475758166452067209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4977141967677555269422945 3732856475758166452067209)
                      ·
                        rfl

theorem cell23_7269712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 2, 4, 2].length) (baseStart_7269712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269712 prefixEnd_7269712 := by exact prefixLift 7269712
  have htrace : WordTrace (prefixWord ++ tailWord_7269712) baseStart_7269712 baseEnd_7269712 := by
    simpa [prefixWord, tailWord_7269712, baseEnd_7269712] using wordTrace_append hprefix tailTrace_7269712
  have hstable : (prefixWord ++ tailWord_7269712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269712).length < 2 ^ (prefixWord ++ tailWord_7269712).sum := by decide
  have hdescent : baseEnd_7269712 < baseStart_7269712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269715 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 3, 4, 3]
def baseStart_7269715 : Nat := 118140960795 + 7269715 * 2 ^ 59
def prefixEnd_7269715 : Nat := 4983230072969 + 3 ^ 40 * 7269715 * 2
def baseEnd_7269715 : Nat := 3732858016200129940329695

theorem tailTrace_7269715 : CollatzResearch.WordTrace tailWord_7269715 prefixEnd_7269715 3732858016200129940329695 := by
  unfold tailWord_7269715
  simp only [CollatzResearch.WordTrace]
  refine ⟨265148288858071598320794599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176765525905381065547196399 265148288858071598320794599)
  ·
    refine ⟨397722433287107397481191899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265148288858071598320794599 397722433287107397481191899)
    ·
      refine ⟨596583649930661096221787849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397722433287107397481191899 596583649930661096221787849)
      ·
        refine ⟨447437737447995822166340887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 596583649930661096221787849 447437737447995822166340887)
        ·
          refine ⟨671156606171993733249511331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447437737447995822166340887 671156606171993733249511331)
          ·
            refine ⟨1006734909257990599874266997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671156606171993733249511331 1006734909257990599874266997)
            ·
              refine ⟨94381397742936618738212531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1006734909257990599874266997 94381397742936618738212531)
              ·
                refine ⟨141572096614404928107318797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94381397742936618738212531 141572096614404928107318797)
                ·
                  refine ⟨53089536230401848040244549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141572096614404928107318797 53089536230401848040244549)
                  ·
                    refine ⟨9954288043200346507545853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53089536230401848040244549 9954288043200346507545853)
                    ·
                      refine ⟨3732858016200129940329695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9954288043200346507545853 3732858016200129940329695)
                      ·
                        rfl

theorem cell23_7269715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 4, 3].length) (baseStart_7269715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269715 prefixEnd_7269715 := by exact prefixLift 7269715
  have htrace : WordTrace (prefixWord ++ tailWord_7269715) baseStart_7269715 baseEnd_7269715 := by
    simpa [prefixWord, tailWord_7269715, baseEnd_7269715] using wordTrace_append hprefix tailTrace_7269715
  have hstable : (prefixWord ++ tailWord_7269715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269715).length < 2 ^ (prefixWord ++ tailWord_7269715).sum := by decide
  have hdescent : baseEnd_7269715 < baseStart_7269715 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269722 : List Nat := [3, 1, 1, 2, 1, 2, 4, 2, 3, 4]
def baseStart_7269722 : Nat := 118140960795 + 7269722 * 2 ^ 59
def prefixEnd_7269722 : Nat := 4983230072969 + 3 ^ 40 * 7269722 * 2
def baseEnd_7269722 : Nat := 1244287203521570470980721

theorem tailTrace_7269722 : CollatzResearch.WordTrace tailWord_7269722 prefixEnd_7269722 1244287203521570470980721 := by
  unfold tailWord_7269722
  simp only [CollatzResearch.WordTrace]
  refine ⟨66287136042261559629074855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176765696112697492344199613 66287136042261559629074855)
  ·
    refine ⟨99430704063392339443612283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66287136042261559629074855 99430704063392339443612283)
    ·
      refine ⟨149146056095088509165418425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99430704063392339443612283 149146056095088509165418425)
      ·
        refine ⟨111859542071316381874063819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149146056095088509165418425 111859542071316381874063819)
        ·
          refine ⟨167789313106974572811095729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111859542071316381874063819 167789313106974572811095729)
          ·
            refine ⟨125841984830230929608321797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167789313106974572811095729 125841984830230929608321797)
            ·
              refine ⟨23595372155668299301560337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125841984830230929608321797 23595372155668299301560337)
              ·
                refine ⟨17696529116751224476170253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23595372155668299301560337 17696529116751224476170253)
                ·
                  refine ⟨6636198418781709178563845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17696529116751224476170253 6636198418781709178563845)
                  ·
                    refine ⟨1244287203521570470980721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6636198418781709178563845 1244287203521570470980721)
                    ·
                      rfl

theorem cell23_7269722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 3, 4].length) (baseStart_7269722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269722 prefixEnd_7269722 := by exact prefixLift 7269722
  have htrace : WordTrace (prefixWord ++ tailWord_7269722) baseStart_7269722 baseEnd_7269722 := by
    simpa [prefixWord, tailWord_7269722, baseEnd_7269722] using wordTrace_append hprefix tailTrace_7269722
  have hstable : (prefixWord ++ tailWord_7269722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269722).length < 2 ^ (prefixWord ++ tailWord_7269722).sum := by decide
  have hdescent : baseEnd_7269722 < baseStart_7269722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269732 : List Nat := [2, 3, 1, 1, 3, 2, 2, 1, 1, 4, 3]
def baseStart_7269732 : Nat := 118140960795 + 7269732 * 2 ^ 59
def prefixEnd_7269732 : Nat := 4983230072969 + 3 ^ 40 * 7269732 * 2
def baseEnd_7269732 : Nat := 3732866745371256373817117

theorem tailTrace_7269732 : CollatzResearch.WordTrace tailWord_7269732 prefixEnd_7269732 3732866745371256373817117 := by
  unfold tailWord_7269732
  simp only [CollatzResearch.WordTrace]
  refine ⟨132574454449505005112081725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176765939266006673482775633 132574454449505005112081725)
  ·
    refine ⟨49715420418564376917030647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132574454449505005112081725 49715420418564376917030647)
    ·
      refine ⟨74573130627846565375545971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49715420418564376917030647 74573130627846565375545971)
      ·
        refine ⟨111859695941769848063318957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74573130627846565375545971 111859695941769848063318957)
        ·
          refine ⟨41947385978163693023744609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111859695941769848063318957 41947385978163693023744609)
          ·
            refine ⟨31460539483622769767808457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41947385978163693023744609 31460539483622769767808457)
            ·
              refine ⟨23595404612717077325856343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31460539483622769767808457 23595404612717077325856343)
              ·
                refine ⟨35393106919075615988784515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23595404612717077325856343 35393106919075615988784515)
                ·
                  refine ⟨53089660378613423983176773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35393106919075615988784515 53089660378613423983176773)
                  ·
                    refine ⟨9954311320990016996845645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53089660378613423983176773 9954311320990016996845645)
                    ·
                      refine ⟨3732866745371256373817117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9954311320990016996845645 3732866745371256373817117)
                      ·
                        rfl

theorem cell23_7269732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_7269732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269732 prefixEnd_7269732 := by exact prefixLift 7269732
  have htrace : WordTrace (prefixWord ++ tailWord_7269732) baseStart_7269732 baseEnd_7269732 := by
    simpa [prefixWord, tailWord_7269732, baseEnd_7269732] using wordTrace_append hprefix tailTrace_7269732
  have hstable : (prefixWord ++ tailWord_7269732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269732).length < 2 ^ (prefixWord ++ tailWord_7269732).sum := by decide
  have hdescent : baseEnd_7269732 < baseStart_7269732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269756 : List Nat := [2, 2, 2, 1, 1, 1, 7, 2, 1, 4]
def baseStart_7269756 : Nat := 118140960795 + 7269756 * 2 ^ 59
def prefixEnd_7269756 : Nat := 4983230072969 + 3 ^ 40 * 7269756 * 2
def baseEnd_7269756 : Nat := 1244293022968988093305669

theorem tailTrace_7269756 : CollatzResearch.WordTrace tailWord_7269756 prefixEnd_7269756 1244293022968988093305669 := by
  unfold tailWord_7269756
  simp only [CollatzResearch.WordTrace]
  refine ⟨132574892125461531161518561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176766522833948708215358081 132574892125461531161518561)
  ·
    refine ⟨99431169094096148371138921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132574892125461531161518561 99431169094096148371138921)
    ·
      refine ⟨74573376820572111278354191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99431169094096148371138921 74573376820572111278354191)
      ·
        refine ⟨111860065230858166917531287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74573376820572111278354191 111860065230858166917531287)
        ·
          refine ⟨167790097846287250376296931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111860065230858166917531287 167790097846287250376296931)
          ·
            refine ⟨251685146769430875564445397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167790097846287250376296931 251685146769430875564445397)
            ·
              refine ⟨5898870627408536146041689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 251685146769430875564445397 5898870627408536146041689)
              ·
                refine ⟨4424152970556402109531267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5898870627408536146041689 4424152970556402109531267)
                ·
                  refine ⟨6636229455834603164296901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4424152970556402109531267 6636229455834603164296901)
                  ·
                    refine ⟨1244293022968988093305669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6636229455834603164296901 1244293022968988093305669)
                    ·
                      rfl

theorem cell23_7269756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 2, 1, 4].length) (baseStart_7269756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269756 prefixEnd_7269756 := by exact prefixLift 7269756
  have htrace : WordTrace (prefixWord ++ tailWord_7269756) baseStart_7269756 baseEnd_7269756 := by
    simpa [prefixWord, tailWord_7269756, baseEnd_7269756] using wordTrace_append hprefix tailTrace_7269756
  have hstable : (prefixWord ++ tailWord_7269756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269756).length < 2 ^ (prefixWord ++ tailWord_7269756).sum := by decide
  have hdescent : baseEnd_7269756 < baseStart_7269756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269796 : List Nat := [2, 3, 1, 2, 1, 1, 1, 7, 1, 1, 3]
def baseStart_7269796 : Nat := 118140960795 + 7269796 * 2 ^ 59
def prefixEnd_7269796 : Nat := 4983230072969 + 3 ^ 40 * 7269796 * 2
def baseEnd_7269796 : Nat := 3732899608133144123416823

theorem tailTrace_7269796 : CollatzResearch.WordTrace tailWord_7269796 prefixEnd_7269796 3732899608133144123416823 := by
  unfold tailWord_7269796
  simp only [CollatzResearch.WordTrace]
  refine ⟨132575621585389074577246621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176767495447185432769662161 132575621585389074577246621)
  ·
    refine ⟨49715858094520902966467483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132575621585389074577246621 49715858094520902966467483)
    ·
      refine ⟨74573787141781354449701225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49715858094520902966467483 74573787141781354449701225)
      ·
        refine ⟨55930340356336015837275919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74573787141781354449701225 55930340356336015837275919)
        ·
          refine ⟨83895510534504023755913879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55930340356336015837275919 83895510534504023755913879)
          ·
            refine ⟨125843265801756035633870819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83895510534504023755913879 125843265801756035633870819)
            ·
              refine ⟨188764898702634053450806229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125843265801756035633870819 188764898702634053450806229)
              ·
                refine ⟨4424177313342985627753271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 188764898702634053450806229 4424177313342985627753271)
                ·
                  refine ⟨6636265970014478441629907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4424177313342985627753271 6636265970014478441629907)
                  ·
                    refine ⟨9954398955021717662444861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6636265970014478441629907 9954398955021717662444861)
                    ·
                      refine ⟨3732899608133144123416823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9954398955021717662444861 3732899608133144123416823)
                      ·
                        rfl

theorem cell23_7269796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 7, 1, 1, 3].length) (baseStart_7269796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269796 prefixEnd_7269796 := by exact prefixLift 7269796
  have htrace : WordTrace (prefixWord ++ tailWord_7269796) baseStart_7269796 baseEnd_7269796 := by
    simpa [prefixWord, tailWord_7269796, baseEnd_7269796] using wordTrace_append hprefix tailTrace_7269796
  have hstable : (prefixWord ++ tailWord_7269796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269796).length < 2 ^ (prefixWord ++ tailWord_7269796).sum := by decide
  have hdescent : baseEnd_7269796 < baseStart_7269796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269813 : List Nat := [1, 3, 3, 2, 2, 2, 1, 4, 1, 1, 3]
def baseStart_7269813 : Nat := 118140960795 + 7269813 * 2 ^ 59
def prefixEnd_7269813 : Nat := 4983230072969 + 3 ^ 40 * 7269813 * 2
def baseEnd_7269813 : Nat := 3732908337304270556904245

theorem tailTrace_7269813 : CollatzResearch.WordTrace tailWord_7269813 prefixEnd_7269813 3732908337304270556904245 := by
  unfold tailWord_7269813
  simp only [CollatzResearch.WordTrace]
  refine ⟨265151863211716561057862093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176767908807811040705241395 265151863211716561057862093)
  ·
    refine ⟨99431948704393710396698285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265151863211716561057862093 99431948704393710396698285)
    ·
      refine ⟨37286980764147641398761857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99431948704393710396698285 37286980764147641398761857)
      ·
        refine ⟨27965235573110731049071393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37286980764147641398761857 27965235573110731049071393)
        ·
          refine ⟨20973926679833048286803545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27965235573110731049071393 20973926679833048286803545)
          ·
            refine ⟨15730445009874786215102659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20973926679833048286803545 15730445009874786215102659)
            ·
              refine ⟨23595667514812179322653989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15730445009874786215102659 23595667514812179322653989)
              ·
                refine ⟨4424187659027283622997623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23595667514812179322653989 4424187659027283622997623)
                ·
                  refine ⟨6636281488540925434496435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4424187659027283622997623 6636281488540925434496435)
                  ·
                    refine ⟨9954422232811388151744653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6636281488540925434496435 9954422232811388151744653)
                    ·
                      refine ⟨3732908337304270556904245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9954422232811388151744653 3732908337304270556904245)
                      ·
                        rfl

theorem cell23_7269813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_7269813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269813 prefixEnd_7269813 := by exact prefixLift 7269813
  have htrace : WordTrace (prefixWord ++ tailWord_7269813) baseStart_7269813 baseEnd_7269813 := by
    simpa [prefixWord, tailWord_7269813, baseEnd_7269813] using wordTrace_append hprefix tailTrace_7269813
  have hstable : (prefixWord ++ tailWord_7269813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269813).length < 2 ^ (prefixWord ++ tailWord_7269813).sum := by decide
  have hdescent : baseEnd_7269813 < baseStart_7269813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269822 : List Nat := [4, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5]
def baseStart_7269822 : Nat := 118140960795 + 7269822 * 2 ^ 59
def prefixEnd_7269822 : Nat := 4983230072969 + 3 ^ 40 * 7269822 * 2
def baseEnd_7269822 : Nat := 3732912958630161021691703

theorem tailTrace_7269822 : CollatzResearch.WordTrace tailWord_7269822 prefixEnd_7269822 3732912958630161021691703 := by
  unfold tailWord_7269822
  simp only [CollatzResearch.WordTrace]
  refine ⟨33144023933585494449367465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176768127645789303729959813 33144023933585494449367465)
  ·
    refine ⟨24858017950189120837025599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33144023933585494449367465 24858017950189120837025599)
    ·
      refine ⟨37287026925283681255538399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24858017950189120837025599 37287026925283681255538399)
      ·
        refine ⟨55930540387925521883307599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37287026925283681255538399 55930540387925521883307599)
        ·
          refine ⟨83895810581888282824961399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55930540387925521883307599 83895810581888282824961399)
          ·
            refine ⟨125843715872832424237442099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83895810581888282824961399 125843715872832424237442099)
            ·
              refine ⟨188765573809248636356163149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125843715872832424237442099 188765573809248636356163149)
              ·
                refine ⟨70787090178468238633561181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188765573809248636356163149 70787090178468238633561181)
                ·
                  refine ⟨26545158816925589487585443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70787090178468238633561181 26545158816925589487585443)
                  ·
                    refine ⟨39817738225388384231378165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26545158816925589487585443 39817738225388384231378165)
                    ·
                      refine ⟨3732912958630161021691703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39817738225388384231378165 3732912958630161021691703)
                      ·
                        rfl

theorem cell23_7269822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_7269822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269822 prefixEnd_7269822 := by exact prefixLift 7269822
  have htrace : WordTrace (prefixWord ++ tailWord_7269822) baseStart_7269822 baseEnd_7269822 := by
    simpa [prefixWord, tailWord_7269822, baseEnd_7269822] using wordTrace_append hprefix tailTrace_7269822
  have hstable : (prefixWord ++ tailWord_7269822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269822).length < 2 ^ (prefixWord ++ tailWord_7269822).sum := by decide
  have hdescent : baseEnd_7269822 < baseStart_7269822 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269836 : List Nat := [2, 2, 1, 4, 2, 1, 1, 1, 5, 2, 2]
def baseStart_7269836 : Nat := 118140960795 + 7269836 * 2 ^ 59
def prefixEnd_7269836 : Nat := 4983230072969 + 3 ^ 40 * 7269836 * 2
def baseEnd_7269836 : Nat := 3732920147359323966916639

theorem tailTrace_7269836 : CollatzResearch.WordTrace tailWord_7269836 prefixEnd_7269836 3732920147359323966916639 := by
  unfold tailWord_7269836
  simp only [CollatzResearch.WordTrace]
  refine ⟨132576351045316617992974681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176768468060422157323966241 132576351045316617992974681)
  ·
    refine ⟨99432263283987463494731011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132576351045316617992974681 99432263283987463494731011)
    ·
      refine ⟨149148394925981195242096517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99432263283987463494731011 149148394925981195242096517)
      ·
        refine ⟨27965324048621474107893097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149148394925981195242096517 27965324048621474107893097)
        ·
          refine ⟨20973993036466105580919823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27965324048621474107893097 20973993036466105580919823)
          ·
            refine ⟨31460989554699158371379735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20973993036466105580919823 31460989554699158371379735)
            ·
              refine ⟨47191484332048737557069603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31460989554699158371379735 47191484332048737557069603)
              ·
                refine ⟨70787226498073106335604405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47191484332048737557069603 70787226498073106335604405)
                ·
                  refine ⟨6636302484194353718962913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70787226498073106335604405 6636302484194353718962913)
                  ·
                    refine ⟨4977226863145765289222185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6636302484194353718962913 4977226863145765289222185)
                    ·
                      refine ⟨3732920147359323966916639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4977226863145765289222185 3732920147359323966916639)
                      ·
                        rfl

theorem cell23_7269836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_7269836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269836 prefixEnd_7269836 := by exact prefixLift 7269836
  have htrace : WordTrace (prefixWord ++ tailWord_7269836) baseStart_7269836 baseEnd_7269836 := by
    simpa [prefixWord, tailWord_7269836, baseEnd_7269836] using wordTrace_append hprefix tailTrace_7269836
  have hstable : (prefixWord ++ tailWord_7269836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269836).length < 2 ^ (prefixWord ++ tailWord_7269836).sum := by decide
  have hdescent : baseEnd_7269836 < baseStart_7269836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269853 : List Nat := [1, 4, 3, 1, 1, 4, 2, 1, 1, 1, 4]
def baseStart_7269853 : Nat := 118140960795 + 7269853 * 2 ^ 59
def prefixEnd_7269853 : Nat := 4983230072969 + 3 ^ 40 * 7269853 * 2
def baseEnd_7269853 : Nat := 3732928876530450400404061

theorem tailTrace_7269853 : CollatzResearch.WordTrace tailWord_7269853 prefixEnd_7269853 3732928876530450400404061 := by
  unfold tailWord_7269853
  simp only [CollatzResearch.WordTrace]
  refine ⟨265153322131571647889318213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176768881421047765259545475 265153322131571647889318213)
  ·
    refine ⟨49716247899669683979247165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265153322131571647889318213 49716247899669683979247165)
    ·
      refine ⟨18643592962376131492217687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49716247899669683979247165 18643592962376131492217687)
      ·
        refine ⟨27965389443564197238326531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18643592962376131492217687 27965389443564197238326531)
        ·
          refine ⟨41948084165346295857489797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27965389443564197238326531 41948084165346295857489797)
          ·
            refine ⟨7865265781002430473279337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41948084165346295857489797 7865265781002430473279337)
            ·
              refine ⟨5898949335751822854959503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7865265781002430473279337 5898949335751822854959503)
              ·
                refine ⟨8848424003627734282439255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5898949335751822854959503 8848424003627734282439255)
                ·
                  refine ⟨13272636005441601423658883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8848424003627734282439255 13272636005441601423658883)
                  ·
                    refine ⟨19908954008162402135488325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13272636005441601423658883 19908954008162402135488325)
                    ·
                      refine ⟨3732928876530450400404061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19908954008162402135488325 3732928876530450400404061)
                      ·
                        rfl

theorem cell23_7269853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_7269853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269853 prefixEnd_7269853 := by exact prefixLift 7269853
  have htrace : WordTrace (prefixWord ++ tailWord_7269853) baseStart_7269853 baseEnd_7269853 := by
    simpa [prefixWord, tailWord_7269853, baseEnd_7269853] using wordTrace_append hprefix tailTrace_7269853
  have hstable : (prefixWord ++ tailWord_7269853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269853).length < 2 ^ (prefixWord ++ tailWord_7269853).sum := by decide
  have hdescent : baseEnd_7269853 < baseStart_7269853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269879 : List Nat := [1, 1, 3, 1, 1, 1, 1, 6, 3, 3, 2]
def baseStart_7269879 : Nat := 118140960795 + 7269879 * 2 ^ 59
def prefixEnd_7269879 : Nat := 4983230072969 + 3 ^ 40 * 7269879 * 2
def baseEnd_7269879 : Nat := 3732942227027467298678941

theorem tailTrace_7269879 : CollatzResearch.WordTrace tailWord_7269879 prefixEnd_7269879 3732942227027467298678941 := by
  unfold tailWord_7269879
  simp only [CollatzResearch.WordTrace]
  refine ⟨265154270429477454329764691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176769513619651636219843127 265154270429477454329764691)
  ·
    refine ⟨397731405644216181494647037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265154270429477454329764691 397731405644216181494647037)
    ·
      refine ⟨149149277116581068060492639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 397731405644216181494647037 149149277116581068060492639)
      ·
        refine ⟨223723915674871602090738959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149149277116581068060492639 223723915674871602090738959)
        ·
          refine ⟨335585873512307403136108439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223723915674871602090738959 335585873512307403136108439)
          ·
            refine ⟨503378810268461104704162659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335585873512307403136108439 503378810268461104704162659)
            ·
              refine ⟨755068215402691657056243989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503378810268461104704162659 755068215402691657056243989)
              ·
                refine ⟨35393822597001171424511437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 755068215402691657056243989 35393822597001171424511437)
                ·
                  refine ⟨13272683473875439284191789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35393822597001171424511437 13272683473875439284191789)
                  ·
                    refine ⟨4977256302703289731571921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13272683473875439284191789 4977256302703289731571921)
                    ·
                      refine ⟨3732942227027467298678941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4977256302703289731571921 3732942227027467298678941)
                      ·
                        rfl

theorem cell23_7269879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 3, 2].length) (baseStart_7269879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269879 prefixEnd_7269879 := by exact prefixLift 7269879
  have htrace : WordTrace (prefixWord ++ tailWord_7269879) baseStart_7269879 baseEnd_7269879 := by
    simpa [prefixWord, tailWord_7269879, baseEnd_7269879] using wordTrace_append hprefix tailTrace_7269879
  have hstable : (prefixWord ++ tailWord_7269879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269879).length < 2 ^ (prefixWord ++ tailWord_7269879).sum := by decide
  have hdescent : baseEnd_7269879 < baseStart_7269879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269896 : List Nat := [2, 1, 3, 2, 1, 1, 3, 4, 1, 3, 2]
def baseStart_7269896 : Nat := 118140960795 + 7269896 * 2 ^ 59
def prefixEnd_7269896 : Nat := 4983230072969 + 3 ^ 40 * 7269896 * 2
def baseEnd_7269896 : Nat := 3732950956198593732166363

theorem tailTrace_7269896 : CollatzResearch.WordTrace tailWord_7269896 prefixEnd_7269896 3732950956198593732166363 := by
  unfold tailWord_7269896
  simp only [CollatzResearch.WordTrace]
  refine ⟨132577445235207933116566771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176769926980277244155422361 132577445235207933116566771)
  ·
    refine ⟨198866167852811899674850157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132577445235207933116566771 198866167852811899674850157)
    ·
      refine ⟨74574812944804462378068809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198866167852811899674850157 74574812944804462378068809)
      ·
        refine ⟨55931109708603346783551607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74574812944804462378068809 55931109708603346783551607)
        ·
          refine ⟨83896664562905020175327411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55931109708603346783551607 83896664562905020175327411)
          ·
            refine ⟨125844996844357530262991117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83896664562905020175327411 125844996844357530262991117)
            ·
              refine ⟨47191873816634073848621669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125844996844357530262991117 47191873816634073848621669)
              ·
                refine ⟨8848476340618888846616563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47191873816634073848621669 8848476340618888846616563)
                ·
                  refine ⟨13272714510928333269924845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8848476340618888846616563 13272714510928333269924845)
                  ·
                    refine ⟨4977267941598124976221817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13272714510928333269924845 4977267941598124976221817)
                    ·
                      refine ⟨3732950956198593732166363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4977267941598124976221817 3732950956198593732166363)
                      ·
                        rfl

theorem cell23_7269896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_7269896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269896 prefixEnd_7269896 := by exact prefixLift 7269896
  have htrace : WordTrace (prefixWord ++ tailWord_7269896) baseStart_7269896 baseEnd_7269896 := by
    simpa [prefixWord, tailWord_7269896, baseEnd_7269896] using wordTrace_append hprefix tailTrace_7269896
  have hstable : (prefixWord ++ tailWord_7269896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269896).length < 2 ^ (prefixWord ++ tailWord_7269896).sum := by decide
  have hdescent : baseEnd_7269896 < baseStart_7269896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269943 : List Nat := [1, 1, 3, 1, 2, 5, 1, 3, 2, 2, 2]
def baseStart_7269943 : Nat := 118140960795 + 7269943 * 2 ^ 59
def prefixEnd_7269943 : Nat := 4983230072969 + 3 ^ 40 * 7269943 * 2
def baseEnd_7269943 : Nat := 3732975089789355048278647

theorem tailTrace_7269943 : CollatzResearch.WordTrace tailWord_7269943 prefixEnd_7269943 3732975089789355048278647 := by
  unfold tailWord_7269943
  simp only [CollatzResearch.WordTrace]
  refine ⟨265156604701245593260094483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176771069800830395506729655 265156604701245593260094483)
  ·
    refine ⟨397734907051868389890141725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265156604701245593260094483 397734907051868389890141725)
    ·
      refine ⟨149150590144450646208803147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 397734907051868389890141725 149150590144450646208803147)
      ·
        refine ⟨223725885216675969313204721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149150590144450646208803147 223725885216675969313204721)
        ·
          refine ⟨167794413912506976984903541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223725885216675969313204721 167794413912506976984903541)
          ·
            refine ⟨15730726304297529092334707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 167794413912506976984903541 15730726304297529092334707)
            ·
              refine ⟨23596089456446293638502061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15730726304297529092334707 23596089456446293638502061)
              ·
                refine ⟨8848533546167360114438273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23596089456446293638502061 8848533546167360114438273)
                ·
                  refine ⟨6636400159625520085828705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8848533546167360114438273 6636400159625520085828705)
                  ·
                    refine ⟨4977300119719140064371529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6636400159625520085828705 4977300119719140064371529)
                    ·
                      refine ⟨3732975089789355048278647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4977300119719140064371529 3732975089789355048278647)
                      ·
                        rfl

theorem cell23_7269943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 2, 2, 2].length) (baseStart_7269943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269943 prefixEnd_7269943 := by exact prefixLift 7269943
  have htrace : WordTrace (prefixWord ++ tailWord_7269943) baseStart_7269943 baseEnd_7269943 := by
    simpa [prefixWord, tailWord_7269943, baseEnd_7269943] using wordTrace_append hprefix tailTrace_7269943
  have hstable : (prefixWord ++ tailWord_7269943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269943).length < 2 ^ (prefixWord ++ tailWord_7269943).sum := by decide
  have hdescent : baseEnd_7269943 < baseStart_7269943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7269989 : List Nat := [1, 3, 1, 3, 3, 1, 2, 1, 1, 2, 5]
def baseStart_7269989 : Nat := 118140960795 + 7269989 * 2 ^ 59
def prefixEnd_7269989 : Nat := 4983230072969 + 3 ^ 40 * 7269989 * 2
def baseEnd_7269989 : Nat := 3732998709899461868303435

theorem tailTrace_7269989 : CollatzResearch.WordTrace tailWord_7269989 prefixEnd_7269989 3732998709899461868303435 := by
  unfold tailWord_7269989
  simp only [CollatzResearch.WordTrace]
  refine ⟨265158282459078943116269021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176772188306052628744179347 265158282459078943116269021)
  ·
    refine ⟨99434355922154603668600883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265158282459078943116269021 99434355922154603668600883)
    ·
      refine ⟨149151533883231905502901325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99434355922154603668600883 149151533883231905502901325)
      ·
        refine ⟨55931825206211964563587997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149151533883231905502901325 55931825206211964563587997)
        ·
          refine ⟨20974434452329486711345499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55931825206211964563587997 20974434452329486711345499)
          ·
            refine ⟨31461651678494230067018249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20974434452329486711345499 31461651678494230067018249)
            ·
              refine ⟨23596238758870672550263687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31461651678494230067018249 23596238758870672550263687)
              ·
                refine ⟨35394358138306008825395531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23596238758870672550263687 35394358138306008825395531)
                ·
                  refine ⟨53091537207459013238093297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35394358138306008825395531 53091537207459013238093297)
                  ·
                    refine ⟨39818652905594259928569973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53091537207459013238093297 39818652905594259928569973)
                    ·
                      refine ⟨3732998709899461868303435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39818652905594259928569973 3732998709899461868303435)
                      ·
                        rfl

theorem cell23_7269989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_7269989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7269989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7269989 prefixEnd_7269989 := by exact prefixLift 7269989
  have htrace : WordTrace (prefixWord ++ tailWord_7269989) baseStart_7269989 baseEnd_7269989 := by
    simpa [prefixWord, tailWord_7269989, baseEnd_7269989] using wordTrace_append hprefix tailTrace_7269989
  have hstable : (prefixWord ++ tailWord_7269989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7269989).length < 2 ^ (prefixWord ++ tailWord_7269989).sum := by decide
  have hdescent : baseEnd_7269989 < baseStart_7269989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7269989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270039 : List Nat := [1, 1, 3, 3, 2, 3, 1, 1, 8]
def baseStart_7270039 : Nat := 118140960795 + 7270039 * 2 ^ 59
def prefixEnd_7270039 : Nat := 4983230072969 + 3 ^ 40 * 7270039 * 2
def baseEnd_7270039 : Nat := 414780487103576296964245

theorem tailTrace_7270039 : CollatzResearch.WordTrace tailWord_7270039 prefixEnd_7270039 414780487103576296964245 := by
  unfold tailWord_7270039
  simp only [CollatzResearch.WordTrace]
  refine ⟨265160106108897801655589171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176773404072598534437059447 265160106108897801655589171)
  ·
    refine ⟨397740159163346702483383757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265160106108897801655589171 397740159163346702483383757)
    ·
      refine ⟨149152559686255013431268909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 397740159163346702483383757 149152559686255013431268909)
      ·
        refine ⟨55932209882345630036725841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149152559686255013431268909 55932209882345630036725841)
        ·
          refine ⟨41949157411759222527544381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55932209882345630036725841 41949157411759222527544381)
          ·
            refine ⟨15730934029409708447829143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41949157411759222527544381 15730934029409708447829143)
            ·
              refine ⟨23596401044114562671743715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15730934029409708447829143 23596401044114562671743715)
              ·
                refine ⟨35394601566171844007615573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23596401044114562671743715 35394601566171844007615573)
                ·
                  refine ⟨414780487103576296964245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35394601566171844007615573 414780487103576296964245)
                  ·
                    rfl

theorem cell23_7270039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 8].length) (baseStart_7270039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270039 prefixEnd_7270039 := by exact prefixLift 7270039
  have htrace : WordTrace (prefixWord ++ tailWord_7270039) baseStart_7270039 baseEnd_7270039 := by
    simpa [prefixWord, tailWord_7270039, baseEnd_7270039] using wordTrace_append hprefix tailTrace_7270039
  have hstable : (prefixWord ++ tailWord_7270039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270039).length < 2 ^ (prefixWord ++ tailWord_7270039).sum := by decide
  have hdescent : baseEnd_7270039 < baseStart_7270039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270100 : List Nat := [2, 4, 1, 3, 1, 1, 3, 1, 3, 1, 3]
def baseStart_7270100 : Nat := 118140960795 + 7270100 * 2 ^ 59
def prefixEnd_7270100 : Nat := 4983230072969 + 3 ^ 40 * 7270100 * 2
def baseEnd_7270100 : Nat := 3733055706252110934015425

theorem tailTrace_7270100 : CollatzResearch.WordTrace tailWord_7270100 prefixEnd_7270100 3733055706252110934015425 := by
  unfold tailWord_7270100
  simp only [CollatzResearch.WordTrace]
  refine ⟨132581165480838404536779877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176774887307784539382373169 132581165480838404536779877)
  ·
    refine ⟨24858968527657200850646227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132581165480838404536779877 24858968527657200850646227)
    ·
      refine ⟨37288452791485801275969341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24858968527657200850646227 37288452791485801275969341)
      ·
        refine ⟨13983169796807175478488503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37288452791485801275969341 13983169796807175478488503)
        ·
          refine ⟨20974754695210763217732755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13983169796807175478488503 20974754695210763217732755)
          ·
            refine ⟨31462132042816144826599133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20974754695210763217732755 31462132042816144826599133)
            ·
              refine ⟨11798299516056054309974675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31462132042816144826599133 11798299516056054309974675)
              ·
                refine ⟨17697449274084081464962013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11798299516056054309974675 17697449274084081464962013)
                ·
                  refine ⟨6636543477781530549360755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17697449274084081464962013 6636543477781530549360755)
                  ·
                    refine ⟨9954815216672295824041133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6636543477781530549360755 9954815216672295824041133)
                    ·
                      refine ⟨3733055706252110934015425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9954815216672295824041133 3733055706252110934015425)
                      ·
                        rfl

theorem cell23_7270100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_7270100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270100 prefixEnd_7270100 := by exact prefixLift 7270100
  have htrace : WordTrace (prefixWord ++ tailWord_7270100) baseStart_7270100 baseEnd_7270100 := by
    simpa [prefixWord, tailWord_7270100, baseEnd_7270100] using wordTrace_append hprefix tailTrace_7270100
  have hstable : (prefixWord ++ tailWord_7270100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270100).length < 2 ^ (prefixWord ++ tailWord_7270100).sum := by decide
  have hdescent : baseEnd_7270100 < baseStart_7270100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270123 : List Nat := [1, 1, 1, 1, 2, 4, 2, 4, 3, 2, 2]
def baseStart_7270123 : Nat := 118140960795 + 7270123 * 2 ^ 59
def prefixEnd_7270123 : Nat := 4983230072969 + 3 ^ 40 * 7270123 * 2
def baseEnd_7270123 : Nat := 3733067516307164344027819

theorem tailTrace_7270123 : CollatzResearch.WordTrace tailWord_7270123 prefixEnd_7270123 3733067516307164344027819 := by
  unfold tailWord_7270123
  simp only [CollatzResearch.WordTrace]
  refine ⟨265163169840593484001647023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176775446560395656001098015 265163169840593484001647023)
  ·
    refine ⟨397744754760890226002470535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265163169840593484001647023 397744754760890226002470535)
    ·
      refine ⟨596617132141335339003705803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397744754760890226002470535 596617132141335339003705803)
      ·
        refine ⟨894925698212003008505558705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596617132141335339003705803 894925698212003008505558705)
        ·
          refine ⟨671194273659002256379169029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 894925698212003008505558705 671194273659002256379169029)
          ·
            refine ⟨125848926311062923071094193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 671194273659002256379169029 125848926311062923071094193)
            ·
              refine ⟨94386694733297192303320645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125848926311062923071094193 94386694733297192303320645)
              ·
                refine ⟨17697505262493223556872621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94386694733297192303320645 17697505262493223556872621)
                ·
                  refine ⟨6636564473434958833827233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17697505262493223556872621 6636564473434958833827233)
                  ·
                    refine ⟨4977423355076219125370425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6636564473434958833827233 4977423355076219125370425)
                    ·
                      refine ⟨3733067516307164344027819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4977423355076219125370425 3733067516307164344027819)
                      ·
                        rfl

theorem cell23_7270123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 3, 2, 2].length) (baseStart_7270123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270123 prefixEnd_7270123 := by exact prefixLift 7270123
  have htrace : WordTrace (prefixWord ++ tailWord_7270123) baseStart_7270123 baseEnd_7270123 := by
    simpa [prefixWord, tailWord_7270123, baseEnd_7270123] using wordTrace_append hprefix tailTrace_7270123
  have hstable : (prefixWord ++ tailWord_7270123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270123).length < 2 ^ (prefixWord ++ tailWord_7270123).sum := by decide
  have hdescent : baseEnd_7270123 < baseStart_7270123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270129 : List Nat := [1, 2, 2, 2, 2, 3, 2, 9]
def baseStart_7270129 : Nat := 118140960795 + 7270129 * 2 ^ 59
def prefixEnd_7270129 : Nat := 4983230072969 + 3 ^ 40 * 7270129 * 2
def baseEnd_7270129 : Nat := 138261873970040419279733

theorem tailTrace_7270129 : CollatzResearch.WordTrace tailWord_7270129 prefixEnd_7270129 138261873970040419279733 := by
  unfold tailWord_7270129
  simp only [CollatzResearch.WordTrace]
  refine ⟨265163388678571747026365441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176775592452381164684243627 265163388678571747026365441)
  ·
    refine ⟨198872541508928810269774081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265163388678571747026365441 198872541508928810269774081)
    ·
      refine ⟨149154406131696607702330561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198872541508928810269774081 149154406131696607702330561)
      ·
        refine ⟨111865804598772455776747921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149154406131696607702330561 111865804598772455776747921)
        ·
          refine ⟨83899353449079341832560941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111865804598772455776747921 83899353449079341832560941)
          ·
            refine ⟨31462257543404753187210353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83899353449079341832560941 31462257543404753187210353)
            ·
              refine ⟨23596693157553564890407765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31462257543404753187210353 23596693157553564890407765)
              ·
                refine ⟨138261873970040419279733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23596693157553564890407765 138261873970040419279733)
                ·
                  rfl

theorem cell23_7270129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 9].length) (baseStart_7270129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270129 prefixEnd_7270129 := by exact prefixLift 7270129
  have htrace : WordTrace (prefixWord ++ tailWord_7270129) baseStart_7270129 baseEnd_7270129 := by
    simpa [prefixWord, tailWord_7270129, baseEnd_7270129] using wordTrace_append hprefix tailTrace_7270129
  have hstable : (prefixWord ++ tailWord_7270129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270129).length < 2 ^ (prefixWord ++ tailWord_7270129).sum := by decide
  have hdescent : baseEnd_7270129 < baseStart_7270129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270151 : List Nat := [1, 1, 4, 4, 3, 1, 2, 2, 1, 1, 3]
def baseStart_7270151 : Nat := 118140960795 + 7270151 * 2 ^ 59
def prefixEnd_7270151 : Nat := 4983230072969 + 3 ^ 40 * 7270151 * 2
def baseEnd_7270151 : Nat := 3733081893765490234477691

theorem tailTrace_7270151 : CollatzResearch.WordTrace tailWord_7270151 prefixEnd_7270151 3733081893765490234477691 := by
  unfold tailWord_7270151
  simp only [CollatzResearch.WordTrace]
  refine ⟨265164191084492044783666307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176776127389661363189110871 265164191084492044783666307)
  ·
    refine ⟨397746286626738067175499461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265164191084492044783666307 397746286626738067175499461)
    ·
      refine ⟨74577428742513387595406149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 397746286626738067175499461 74577428742513387595406149)
      ·
        refine ⟨13983267889221260174138653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74577428742513387595406149 13983267889221260174138653)
        ·
          refine ⟨5243725458457972565301995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13983267889221260174138653 5243725458457972565301995)
          ·
            refine ⟨7865588187686958847952993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5243725458457972565301995 7865588187686958847952993)
            ·
              refine ⟨5899191140765219135964745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7865588187686958847952993 5899191140765219135964745)
              ·
                refine ⟨4424393355573914351973559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5899191140765219135964745 4424393355573914351973559)
                ·
                  refine ⟨6636590033360871527960339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4424393355573914351973559 6636590033360871527960339)
                  ·
                    refine ⟨9954885050041307291940509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6636590033360871527960339 9954885050041307291940509)
                    ·
                      refine ⟨3733081893765490234477691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9954885050041307291940509 3733081893765490234477691)
                      ·
                        rfl

theorem cell23_7270151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_7270151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270151 prefixEnd_7270151 := by exact prefixLift 7270151
  have htrace : WordTrace (prefixWord ++ tailWord_7270151) baseStart_7270151 baseEnd_7270151 := by
    simpa [prefixWord, tailWord_7270151, baseEnd_7270151] using wordTrace_append hprefix tailTrace_7270151
  have hstable : (prefixWord ++ tailWord_7270151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270151).length < 2 ^ (prefixWord ++ tailWord_7270151).sum := by decide
  have hdescent : baseEnd_7270151 < baseStart_7270151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270200 : List Nat := [2, 1, 2, 1, 3, 4, 1, 3, 1, 3, 2]
def baseStart_7270200 : Nat := 118140960795 + 7270200 * 2 ^ 59
def prefixEnd_7270200 : Nat := 4983230072969 + 3 ^ 40 * 7270200 * 2
def baseEnd_7270200 : Nat := 3733107054317560542764965

theorem tailTrace_7270200 : CollatzResearch.WordTrace tailWord_7270200 prefixEnd_7270200 3733107054317560542764965 := by
  unfold tailWord_7270200
  simp only [CollatzResearch.WordTrace]
  refine ⟨132582989130657263076100027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176777318840876350768133369 132582989130657263076100027)
  ·
    refine ⟨198874483695985894614150041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132582989130657263076100027 198874483695985894614150041)
    ·
      refine ⟨149155862771989420960612531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198874483695985894614150041 149155862771989420960612531)
      ·
        refine ⟨223733794157984131440918797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149155862771989420960612531 223733794157984131440918797)
        ·
          refine ⟨83900172809244049290344549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223733794157984131440918797 83900172809244049290344549)
          ·
            refine ⟨15731282401733259241939603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83900172809244049290344549 15731282401733259241939603)
            ·
              refine ⟨23596923602599888862909405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15731282401733259241939603 23596923602599888862909405)
              ·
                refine ⟨8848846350974958323591027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23596923602599888862909405 8848846350974958323591027)
                ·
                  refine ⟨13273269526462437485386541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8848846350974958323591027 13273269526462437485386541)
                  ·
                    refine ⟨4977476072423414057019953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13273269526462437485386541 4977476072423414057019953)
                    ·
                      refine ⟨3733107054317560542764965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4977476072423414057019953 3733107054317560542764965)
                      ·
                        rfl

theorem cell23_7270200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 1, 3, 2].length) (baseStart_7270200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270200 prefixEnd_7270200 := by exact prefixLift 7270200
  have htrace : WordTrace (prefixWord ++ tailWord_7270200) baseStart_7270200 baseEnd_7270200 := by
    simpa [prefixWord, tailWord_7270200, baseEnd_7270200] using wordTrace_append hprefix tailTrace_7270200
  have hstable : (prefixWord ++ tailWord_7270200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270200).length < 2 ^ (prefixWord ++ tailWord_7270200).sum := by decide
  have hdescent : baseEnd_7270200 < baseStart_7270200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270207 : List Nat := [1, 1, 2, 2, 6, 2, 1, 2, 2, 1, 3]
def baseStart_7270207 : Nat := 118140960795 + 7270207 * 2 ^ 59
def prefixEnd_7270207 : Nat := 4983230072969 + 3 ^ 40 * 7270207 * 2
def baseEnd_7270207 : Nat := 3733110648682142015377433

theorem tailTrace_7270207 : CollatzResearch.WordTrace tailWord_7270207 prefixEnd_7270207 3733110648682142015377433 := by
  unfold tailWord_7270207
  simp only [CollatzResearch.WordTrace]
  refine ⟨265166233572289166347704875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176777489048192777565136583 265166233572289166347704875)
  ·
    refine ⟨397749350358433749521557313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265166233572289166347704875 397749350358433749521557313)
    ·
      refine ⟨298312012768825312141167985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397749350358433749521557313 298312012768825312141167985)
      ·
        refine ⟨223734009576618984105875989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298312012768825312141167985 223734009576618984105875989)
        ·
          refine ⟨10487531698904014879962937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 223734009576618984105875989 10487531698904014879962937)
          ·
            refine ⟨7865648774178011159972203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10487531698904014879962937 7865648774178011159972203)
            ·
              refine ⟨11798473161267016739958305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7865648774178011159972203 11798473161267016739958305)
              ·
                refine ⟨8848854870950262554968729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11798473161267016739958305 8848854870950262554968729)
                ·
                  refine ⟨6636641153212696916226547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8848854870950262554968729 6636641153212696916226547)
                  ·
                    refine ⟨9954961729819045374339821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6636641153212696916226547 9954961729819045374339821)
                    ·
                      refine ⟨3733110648682142015377433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9954961729819045374339821 3733110648682142015377433)
                      ·
                        rfl

theorem cell23_7270207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 2, 1, 3].length) (baseStart_7270207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270207 prefixEnd_7270207 := by exact prefixLift 7270207
  have htrace : WordTrace (prefixWord ++ tailWord_7270207) baseStart_7270207 baseEnd_7270207 := by
    simpa [prefixWord, tailWord_7270207, baseEnd_7270207] using wordTrace_append hprefix tailTrace_7270207
  have hstable : (prefixWord ++ tailWord_7270207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270207).length < 2 ^ (prefixWord ++ tailWord_7270207).sum := by decide
  have hdescent : baseEnd_7270207 < baseStart_7270207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270250 : List Nat := [3, 1, 3, 4, 1, 1, 1, 1, 2, 1, 5]
def baseStart_7270250 : Nat := 118140960795 + 7270250 * 2 ^ 59
def prefixEnd_7270250 : Nat := 4983230072969 + 3 ^ 40 * 7270250 * 2
def baseEnd_7270250 : Nat := 3733132728350285347139735

theorem tailTrace_7270250 : CollatzResearch.WordTrace tailWord_7270250 prefixEnd_7270250 3733132728350285347139735 := by
  unfold tailWord_7270250
  simp only [CollatzResearch.WordTrace]
  refine ⟨66291950477783346172880051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176778534607422256461013469 66291950477783346172880051)
  ·
    refine ⟨99437925716675019259320077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66291950477783346172880051 99437925716675019259320077)
    ·
      refine ⟨37289222143753132222245029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99437925716675019259320077 37289222143753132222245029)
      ·
        refine ⟨6991729151953712291670943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37289222143753132222245029 6991729151953712291670943)
        ·
          refine ⟨10487593727930568437506415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6991729151953712291670943 10487593727930568437506415)
          ·
            refine ⟨15731390591895852656259623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10487593727930568437506415 15731390591895852656259623)
            ·
              refine ⟨23597085887843778984389435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15731390591895852656259623 23597085887843778984389435)
              ·
                refine ⟨35395628831765668476584153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23597085887843778984389435 35395628831765668476584153)
                ·
                  refine ⟨26546721623824251357438115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35395628831765668476584153 26546721623824251357438115)
                  ·
                    refine ⟨39820082435736377036157173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26546721623824251357438115 39820082435736377036157173)
                    ·
                      refine ⟨3733132728350285347139735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39820082435736377036157173 3733132728350285347139735)
                      ·
                        rfl

theorem cell23_7270250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_7270250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270250 prefixEnd_7270250 := by exact prefixLift 7270250
  have htrace : WordTrace (prefixWord ++ tailWord_7270250) baseStart_7270250 baseEnd_7270250 := by
    simpa [prefixWord, tailWord_7270250, baseEnd_7270250] using wordTrace_append hprefix tailTrace_7270250
  have hstable : (prefixWord ++ tailWord_7270250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270250).length < 2 ^ (prefixWord ++ tailWord_7270250).sum := by decide
  have hdescent : baseEnd_7270250 < baseStart_7270250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270266 : List Nat := [3, 1, 1, 1, 1, 1, 5, 1, 4, 5]
def baseStart_7270266 : Nat := 118140960795 + 7270266 * 2 ^ 59
def prefixEnd_7270266 : Nat := 4983230072969 + 3 ^ 40 * 7270266 * 2
def baseEnd_7270266 : Nat := 1244380314680252428179887

theorem tailTrace_7270266 : CollatzResearch.WordTrace tailWord_7270266 prefixEnd_7270266 1244380314680252428179887 := by
  unfold tailWord_7270266
  simp only [CollatzResearch.WordTrace]
  refine ⟨66292096369768854856025663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176778923652716946282735101 66292096369768854856025663)
  ·
    refine ⟨99438144554653282284038495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66292096369768854856025663 99438144554653282284038495)
    ·
      refine ⟨149157216831979923426057743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99438144554653282284038495 149157216831979923426057743)
      ·
        refine ⟨223735825247969885139086615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149157216831979923426057743 223735825247969885139086615)
        ·
          refine ⟨335603737871954827708629923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223735825247969885139086615 335603737871954827708629923)
          ·
            refine ⟨503405606807932241562944885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335603737871954827708629923 503405606807932241562944885)
            ·
              refine ⟨47194275638243647646526083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 503405606807932241562944885 47194275638243647646526083)
              ·
                refine ⟨70791413457365471469789125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47194275638243647646526083 70791413457365471469789125)
                ·
                  refine ⟨13273390023256025900585461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70791413457365471469789125 13273390023256025900585461)
                  ·
                    refine ⟨1244380314680252428179887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13273390023256025900585461 1244380314680252428179887)
                    ·
                      rfl

theorem cell23_7270266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 4, 5].length) (baseStart_7270266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270266 prefixEnd_7270266 := by exact prefixLift 7270266
  have htrace : WordTrace (prefixWord ++ tailWord_7270266) baseStart_7270266 baseEnd_7270266 := by
    simpa [prefixWord, tailWord_7270266, baseEnd_7270266] using wordTrace_append hprefix tailTrace_7270266
  have hstable : (prefixWord ++ tailWord_7270266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270266).length < 2 ^ (prefixWord ++ tailWord_7270266).sum := by decide
  have hdescent : baseEnd_7270266 < baseStart_7270266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270270 : List Nat := [4, 2, 3, 1, 1, 1, 3, 1, 7]
def baseStart_7270270 : Nat := 118140960795 + 7270270 * 2 ^ 59
def prefixEnd_7270270 : Nat := 4983230072969 + 3 ^ 40 * 7270270 * 2
def baseEnd_7270270 : Nat := 414793666440375029876627

theorem tailTrace_7270270 : CollatzResearch.WordTrace tailWord_7270270 prefixEnd_7270270 414793666440375029876627 := by
  unfold tailWord_7270270
  simp only [CollatzResearch.WordTrace]
  refine ⟨33146066421382616013406033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176779020914040618738165509 33146066421382616013406033)
  ·
    refine ⟨24859549816036962010054525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33146066421382616013406033 24859549816036962010054525)
    ·
      refine ⟨9322331181013860753770447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24859549816036962010054525 9322331181013860753770447)
      ·
        refine ⟨13983496771520791130655671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9322331181013860753770447 13983496771520791130655671)
        ·
          refine ⟨20975245157281186695983507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13983496771520791130655671 20975245157281186695983507)
          ·
            refine ⟨31462867735921780043975261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20975245157281186695983507 31462867735921780043975261)
            ·
              refine ⟨11798575400970667516490723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31462867735921780043975261 11798575400970667516490723)
              ·
                refine ⟨17697863101456001274736085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11798575400970667516490723 17697863101456001274736085)
                ·
                  refine ⟨414793666440375029876627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17697863101456001274736085 414793666440375029876627)
                  ·
                    rfl

theorem cell23_7270270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_7270270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270270 prefixEnd_7270270 := by exact prefixLift 7270270
  have htrace : WordTrace (prefixWord ++ tailWord_7270270) baseStart_7270270 baseEnd_7270270 := by
    simpa [prefixWord, tailWord_7270270, baseEnd_7270270] using wordTrace_append hprefix tailTrace_7270270
  have hstable : (prefixWord ++ tailWord_7270270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270270).length < 2 ^ (prefixWord ++ tailWord_7270270).sum := by decide
  have hdescent : baseEnd_7270270 < baseStart_7270270 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270276 : List Nat := [2, 3, 2, 1, 1, 1, 3, 1, 1, 1, 7]
def baseStart_7270276 : Nat := 118140960795 + 7270276 * 2 ^ 59
def prefixEnd_7270276 : Nat := 4983230072969 + 3 ^ 40 * 7270276 * 2
def baseEnd_7270276 : Nat := 3733146078847302245414615

theorem tailTrace_7270276 : CollatzResearch.WordTrace tailWord_7270276 prefixEnd_7270276 3733146078847302245414615 := by
  unfold tailWord_7270276
  simp only [CollatzResearch.WordTrace]
  refine ⟨132584375104519595565983341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176779166806026127421311121 132584375104519595565983341)
  ·
    refine ⟨49719140664194848337243753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132584375104519595565983341 49719140664194848337243753)
    ·
      refine ⟨37289355498146136252932815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49719140664194848337243753 37289355498146136252932815)
      ·
        refine ⟨55934033247219204379399223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37289355498146136252932815 55934033247219204379399223)
        ·
          refine ⟨83901049870828806569098835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55934033247219204379399223 83901049870828806569098835)
          ·
            refine ⟨125851574806243209853648253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83901049870828806569098835 125851574806243209853648253)
            ·
              refine ⟨47194340552341203695118095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125851574806243209853648253 47194340552341203695118095)
              ·
                refine ⟨70791510828511805542677143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47194340552341203695118095 70791510828511805542677143)
                ·
                  refine ⟨106187266242767708314015715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70791510828511805542677143 106187266242767708314015715)
                  ·
                    refine ⟨159280899364151562471023573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106187266242767708314015715 159280899364151562471023573)
                    ·
                      refine ⟨3733146078847302245414615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 159280899364151562471023573 3733146078847302245414615)
                      ·
                        rfl

theorem cell23_7270276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_7270276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270276 prefixEnd_7270276 := by exact prefixLift 7270276
  have htrace : WordTrace (prefixWord ++ tailWord_7270276) baseStart_7270276 baseEnd_7270276 := by
    simpa [prefixWord, tailWord_7270276, baseEnd_7270276] using wordTrace_append hprefix tailTrace_7270276
  have hstable : (prefixWord ++ tailWord_7270276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270276).length < 2 ^ (prefixWord ++ tailWord_7270276).sum := by decide
  have hdescent : baseEnd_7270276 < baseStart_7270276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270300 : List Nat := [2, 2, 3, 3, 1, 2, 2, 1, 2, 5]
def baseStart_7270300 : Nat := 118140960795 + 7270300 * 2 ^ 59
def prefixEnd_7270300 : Nat := 4983230072969 + 3 ^ 40 * 7270300 * 2
def baseEnd_7270300 : Nat := 1244386134127670050504835

theorem tailTrace_7270300 : CollatzResearch.WordTrace tailWord_7270300 prefixEnd_7270300 1244386134127670050504835 := by
  unfold tailWord_7270300
  simp only [CollatzResearch.WordTrace]
  refine ⟨132584812780476121615420177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176779750373968162153893569 132584812780476121615420177)
  ·
    refine ⟨99438609585357091211565133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132584812780476121615420177 99438609585357091211565133)
    ·
      refine ⟨37289478594508909204336925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99438609585357091211565133 37289478594508909204336925)
      ·
        refine ⟨13983554472940840951626347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37289478594508909204336925 13983554472940840951626347)
        ·
          refine ⟨20975331709411261427439521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13983554472940840951626347 20975331709411261427439521)
          ·
            refine ⟨15731498782058446070579641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20975331709411261427439521 15731498782058446070579641)
            ·
              refine ⟨11798624086543834552934731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15731498782058446070579641 11798624086543834552934731)
              ·
                refine ⟨17697936129815751829402097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11798624086543834552934731 17697936129815751829402097)
                ·
                  refine ⟨13273452097361813872051573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17697936129815751829402097 13273452097361813872051573)
                  ·
                    refine ⟨1244386134127670050504835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13273452097361813872051573 1244386134127670050504835)
                    ·
                      rfl

theorem cell23_7270300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_7270300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270300 prefixEnd_7270300 := by exact prefixLift 7270300
  have htrace : WordTrace (prefixWord ++ tailWord_7270300) baseStart_7270300 baseEnd_7270300 := by
    simpa [prefixWord, tailWord_7270300, baseEnd_7270300] using wordTrace_append hprefix tailTrace_7270300
  have hstable : (prefixWord ++ tailWord_7270300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270300).length < 2 ^ (prefixWord ++ tailWord_7270300).sum := by decide
  have hdescent : baseEnd_7270300 < baseStart_7270300 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270323 : List Nat := [1, 1, 1, 2, 3, 1, 3, 4, 2, 2, 3]
def baseStart_7270323 : Nat := 118140960795 + 7270323 * 2 ^ 59
def prefixEnd_7270323 : Nat := 4983230072969 + 3 ^ 40 * 7270323 * 2
def baseEnd_7270323 : Nat := 3733170212438063561526899

theorem tailTrace_7270323 : CollatzResearch.WordTrace tailWord_7270323 prefixEnd_7270323 3733170212438063561526899 := by
  unfold tailWord_7270323
  simp only [CollatzResearch.WordTrace]
  refine ⟨265170464439868918158927623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176780309626579278772618415 265170464439868918158927623)
  ·
    refine ⟨397755696659803377238391435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265170464439868918158927623 397755696659803377238391435)
    ·
      refine ⟨596633544989705065857587153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397755696659803377238391435 596633544989705065857587153)
      ·
        refine ⟨447475158742278799393190365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 596633544989705065857587153 447475158742278799393190365)
        ·
          refine ⟨167803184528354549772446387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 447475158742278799393190365 167803184528354549772446387)
          ·
            refine ⟨251704776792531824658669581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167803184528354549772446387 251704776792531824658669581)
            ·
              refine ⟨94389291297199434247001093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 251704776792531824658669581 94389291297199434247001093)
              ·
                refine ⟨17697992118224893921312705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94389291297199434247001093 17697992118224893921312705)
                ·
                  refine ⟨13273494088668670440984529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17697992118224893921312705 13273494088668670440984529)
                  ·
                    refine ⟨9955120566501502830738397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13273494088668670440984529 9955120566501502830738397)
                    ·
                      refine ⟨3733170212438063561526899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9955120566501502830738397 3733170212438063561526899)
                      ·
                        rfl

theorem cell23_7270323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 2, 3].length) (baseStart_7270323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270323 prefixEnd_7270323 := by exact prefixLift 7270323
  have htrace : WordTrace (prefixWord ++ tailWord_7270323) baseStart_7270323 baseEnd_7270323 := by
    simpa [prefixWord, tailWord_7270323, baseEnd_7270323] using wordTrace_append hprefix tailTrace_7270323
  have hstable : (prefixWord ++ tailWord_7270323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270323).length < 2 ^ (prefixWord ++ tailWord_7270323).sum := by decide
  have hdescent : baseEnd_7270323 < baseStart_7270323 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270354 : List Nat := [3, 2, 2, 3, 3, 1, 1, 1, 2, 1, 4]
def baseStart_7270354 : Nat := 118140960795 + 7270354 * 2 ^ 59
def prefixEnd_7270354 : Nat := 4983230072969 + 3 ^ 40 * 7270354 * 2
def baseEnd_7270354 : Nat := 3733186130338352940239257

theorem tailTrace_7270354 : CollatzResearch.WordTrace tailWord_7270354 prefixEnd_7270354 3733186130338352940239257 := by
  unfold tailWord_7270354
  simp only [CollatzResearch.WordTrace]
  refine ⟨66292898775689152613326529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176781063401837740302204077 66292898775689152613326529)
  ·
    refine ⟨49719674081766864459994897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66292898775689152613326529 49719674081766864459994897)
    ·
      refine ⟨37289755561325148344996173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49719674081766864459994897 37289755561325148344996173)
      ·
        refine ⟨13983658335496930629373565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37289755561325148344996173 13983658335496930629373565)
        ·
          refine ⟨5243871875811348986015087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13983658335496930629373565 5243871875811348986015087)
          ·
            refine ⟨7865807813717023479022631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5243871875811348986015087 7865807813717023479022631)
            ·
              refine ⟨11798711720575535218533947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7865807813717023479022631 11798711720575535218533947)
              ·
                refine ⟨17698067580863302827800921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11798711720575535218533947 17698067580863302827800921)
                ·
                  refine ⟨13273550685647477120850691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17698067580863302827800921 13273550685647477120850691)
                  ·
                    refine ⟨19910326028471215681276037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13273550685647477120850691 19910326028471215681276037)
                    ·
                      refine ⟨3733186130338352940239257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19910326028471215681276037 3733186130338352940239257)
                      ·
                        rfl

theorem cell23_7270354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_7270354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270354 prefixEnd_7270354 := by exact prefixLift 7270354
  have htrace : WordTrace (prefixWord ++ tailWord_7270354) baseStart_7270354 baseEnd_7270354 := by
    simpa [prefixWord, tailWord_7270354, baseEnd_7270354] using wordTrace_append hprefix tailTrace_7270354
  have hstable : (prefixWord ++ tailWord_7270354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270354).length < 2 ^ (prefixWord ++ tailWord_7270354).sum := by decide
  have hdescent : baseEnd_7270354 < baseStart_7270354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270357 : List Nat := [1, 3, 2, 3, 2, 3, 1, 1, 2, 2, 3]
def baseStart_7270357 : Nat := 118140960795 + 7270357 * 2 ^ 59
def prefixEnd_7270357 : Nat := 4983230072969 + 3 ^ 40 * 7270357 * 2
def baseEnd_7270357 : Nat := 3733187670780316428501743

theorem tailTrace_7270357 : CollatzResearch.WordTrace tailWord_7270357 prefixEnd_7270357 3733187670780316428501743 := by
  unfold tailWord_7270357
  simp only [CollatzResearch.WordTrace]
  refine ⟨265171704521745741965665325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176781136347830494643776883 265171704521745741965665325)
  ·
    refine ⟨99439389195654653237124497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265171704521745741965665325 99439389195654653237124497)
    ·
      refine ⟨74579541896740989927843373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99439389195654653237124497 74579541896740989927843373)
      ·
        refine ⟨27967328211277871222941265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74579541896740989927843373 27967328211277871222941265)
        ·
          refine ⟨20975496158458403417205949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27967328211277871222941265 20975496158458403417205949)
          ·
            refine ⟨7865811059421901281452231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20975496158458403417205949 7865811059421901281452231)
            ·
              refine ⟨11798716589132851922178347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7865811059421901281452231 11798716589132851922178347)
              ·
                refine ⟨17698074883699277883267521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11798716589132851922178347 17698074883699277883267521)
                ·
                  refine ⟨13273556162774458412450641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17698074883699277883267521 13273556162774458412450641)
                  ·
                    refine ⟨9955167122080843809337981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13273556162774458412450641 9955167122080843809337981)
                    ·
                      refine ⟨3733187670780316428501743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9955167122080843809337981 3733187670780316428501743)
                      ·
                        rfl

theorem cell23_7270357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_7270357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270357 prefixEnd_7270357 := by exact prefixLift 7270357
  have htrace : WordTrace (prefixWord ++ tailWord_7270357) baseStart_7270357 baseEnd_7270357 := by
    simpa [prefixWord, tailWord_7270357, baseEnd_7270357] using wordTrace_append hprefix tailTrace_7270357
  have hstable : (prefixWord ++ tailWord_7270357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270357).length < 2 ^ (prefixWord ++ tailWord_7270357).sum := by decide
  have hdescent : baseEnd_7270357 < baseStart_7270357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270380 : List Nat := [2, 2, 1, 1, 2, 1, 1, 6, 2, 3, 2]
def baseStart_7270380 : Nat := 118140960795 + 7270380 * 2 ^ 59
def prefixEnd_7270380 : Nat := 4983230072969 + 3 ^ 40 * 7270380 * 2
def baseEnd_7270380 : Nat := 3733199480835369838514137

theorem tailTrace_7270380 : CollatzResearch.WordTrace tailWord_7270380 prefixEnd_7270380 3733199480835369838514137 := by
  unfold tailWord_7270380
  simp only [CollatzResearch.WordTrace]
  refine ⟨132586271700331208446876297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176781695600441611262501729 132586271700331208446876297)
  ·
    refine ⟨99439703775248406335157223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132586271700331208446876297 99439703775248406335157223)
    ·
      refine ⟨149159555662872609502735835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99439703775248406335157223 149159555662872609502735835)
      ·
        refine ⟨223739333494308914254103753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149159555662872609502735835 223739333494308914254103753)
        ·
          refine ⟨167804500120731685690577815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223739333494308914254103753 167804500120731685690577815)
          ·
            refine ⟨251706750181097528535866723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167804500120731685690577815 251706750181097528535866723)
            ·
              refine ⟨377560125271646292803800085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251706750181097528535866723 377560125271646292803800085)
              ·
                refine ⟨17698130872108419975178129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 377560125271646292803800085 17698130872108419975178129)
                ·
                  refine ⟨13273598154081314981383597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17698130872108419975178129 13273598154081314981383597)
                  ·
                    refine ⟨4977599307780493118018849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13273598154081314981383597 4977599307780493118018849)
                    ·
                      refine ⟨3733199480835369838514137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4977599307780493118018849 3733199480835369838514137)
                      ·
                        rfl

theorem cell23_7270380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 3, 2].length) (baseStart_7270380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270380 prefixEnd_7270380 := by exact prefixLift 7270380
  have htrace : WordTrace (prefixWord ++ tailWord_7270380) baseStart_7270380 baseEnd_7270380 := by
    simpa [prefixWord, tailWord_7270380, baseEnd_7270380] using wordTrace_append hprefix tailTrace_7270380
  have hstable : (prefixWord ++ tailWord_7270380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270380).length < 2 ^ (prefixWord ++ tailWord_7270380).sum := by decide
  have hdescent : baseEnd_7270380 < baseStart_7270380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270416 : List Nat := [2, 1, 1, 1, 1, 1, 1, 15]
def baseStart_7270416 : Nat := 118140960795 + 7270416 * 2 ^ 59
def prefixEnd_7270416 : Nat := 4983230072969 + 3 ^ 40 * 7270416 * 2
def baseEnd_7270416 : Nat := 138267332079219692506073

theorem tailTrace_7270416 : CollatzResearch.WordTrace tailWord_7270416 prefixEnd_7270416 138267332079219692506073 := by
  unfold tailWord_7270416
  simp only [CollatzResearch.WordTrace]
  refine ⟨132586928214265997521031551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176782570952354663361375401 132586928214265997521031551)
  ·
    refine ⟨198880392321398996281547327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132586928214265997521031551 198880392321398996281547327)
    ·
      refine ⟨298320588482098494422320991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198880392321398996281547327 298320588482098494422320991)
      ·
        refine ⟨447480882723147741633481487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298320588482098494422320991 447480882723147741633481487)
        ·
          refine ⟨671221324084721612450222231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447480882723147741633481487 671221324084721612450222231)
          ·
            refine ⟨1006831986127082418675333347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671221324084721612450222231 1006831986127082418675333347)
            ·
              refine ⟨1510247979190623628013000021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1006831986127082418675333347 1510247979190623628013000021)
              ·
                refine ⟨138267332079219692506073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 15 1510247979190623628013000021 138267332079219692506073)
                ·
                  rfl

theorem cell23_7270416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 15].length) (baseStart_7270416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270416 prefixEnd_7270416 := by exact prefixLift 7270416
  have htrace : WordTrace (prefixWord ++ tailWord_7270416) baseStart_7270416 baseEnd_7270416 := by
    simpa [prefixWord, tailWord_7270416, baseEnd_7270416] using wordTrace_append hprefix tailTrace_7270416
  have hstable : (prefixWord ++ tailWord_7270416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270416).length < 2 ^ (prefixWord ++ tailWord_7270416).sum := by decide
  have hdescent : baseEnd_7270416 < baseStart_7270416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270421 : List Nat := [1, 3, 2, 1, 5, 2, 1, 3, 1, 1, 3]
def baseStart_7270421 : Nat := 118140960795 + 7270421 * 2 ^ 59
def prefixEnd_7270421 : Nat := 4983230072969 + 3 ^ 40 * 7270421 * 2
def baseEnd_7270421 : Nat := 3733220533542204178101449

theorem tailTrace_7270421 : CollatzResearch.WordTrace tailWord_7270421 prefixEnd_7270421 3733220533542204178101449 := by
  unfold tailWord_7270421
  simp only [CollatzResearch.WordTrace]
  refine ⟨265174038793513880895995117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176782692529009253930663411 265174038793513880895995117)
  ·
    refine ⟨99440264547567705335998169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265174038793513880895995117 99440264547567705335998169)
    ·
      refine ⟨74580198410675779001998627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99440264547567705335998169 74580198410675779001998627)
      ·
        refine ⟨111870297616013668502997941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74580198410675779001998627 111870297616013668502997941)
        ·
          refine ⟨10487840401501281422156057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111870297616013668502997941 10487840401501281422156057)
          ·
            refine ⟨7865880301125961066617043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10487840401501281422156057 7865880301125961066617043)
            ·
              refine ⟨11798820451688941599925565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7865880301125961066617043 11798820451688941599925565)
              ·
                refine ⟨4424557669383353099972087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11798820451688941599925565 4424557669383353099972087)
                ·
                  refine ⟨6636836504075029649958131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4424557669383353099972087 6636836504075029649958131)
                  ·
                    refine ⟨9955254756112544474937197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6636836504075029649958131 9955254756112544474937197)
                    ·
                      refine ⟨3733220533542204178101449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9955254756112544474937197 3733220533542204178101449)
                      ·
                        rfl

theorem cell23_7270421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 3, 1, 1, 3].length) (baseStart_7270421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270421 prefixEnd_7270421 := by exact prefixLift 7270421
  have htrace : WordTrace (prefixWord ++ tailWord_7270421) baseStart_7270421 baseEnd_7270421 := by
    simpa [prefixWord, tailWord_7270421, baseEnd_7270421] using wordTrace_append hprefix tailTrace_7270421
  have hstable : (prefixWord ++ tailWord_7270421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270421).length < 2 ^ (prefixWord ++ tailWord_7270421).sum := by decide
  have hdescent : baseEnd_7270421 < baseStart_7270421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270443 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 5, 3, 3]
def baseStart_7270443 : Nat := 118140960795 + 7270443 * 2 ^ 59
def prefixEnd_7270443 : Nat := 4983230072969 + 3 ^ 40 * 7270443 * 2
def baseEnd_7270443 : Nat := 3733231830116603092026347

theorem tailTrace_7270443 : CollatzResearch.WordTrace tailWord_7270443 prefixEnd_7270443 3733231830116603092026347 := by
  unfold tailWord_7270443
  simp only [CollatzResearch.WordTrace]
  refine ⟨265174841199434178653295983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176783227466289452435530655 265174841199434178653295983)
  ·
    refine ⟨397762261799151267979943975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265174841199434178653295983 397762261799151267979943975)
    ·
      refine ⟨596643392698726901969915963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397762261799151267979943975 596643392698726901969915963)
      ·
        refine ⟨894965089048090352954873945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596643392698726901969915963 894965089048090352954873945)
        ·
          refine ⟨671223816786067764716155459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 894965089048090352954873945 671223816786067764716155459)
          ·
            refine ⟨1006835725179101647074233189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671223816786067764716155459 1006835725179101647074233189)
            ·
              refine ⟨188781698471081558826418723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1006835725179101647074233189 188781698471081558826418723)
              ·
                refine ⟨283172547706622338239628085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188781698471081558826418723 283172547706622338239628085)
                ·
                  refine ⟨26547426347495844209965133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 283172547706622338239628085 26547426347495844209965133)
                  ·
                    refine ⟨9955284880310941578736925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26547426347495844209965133 9955284880310941578736925)
                    ·
                      refine ⟨3733231830116603092026347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9955284880310941578736925 3733231830116603092026347)
                      ·
                        rfl

theorem cell23_7270443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 3, 3].length) (baseStart_7270443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270443 prefixEnd_7270443 := by exact prefixLift 7270443
  have htrace : WordTrace (prefixWord ++ tailWord_7270443) baseStart_7270443 baseEnd_7270443 := by
    simpa [prefixWord, tailWord_7270443, baseEnd_7270443] using wordTrace_append hprefix tailTrace_7270443
  have hstable : (prefixWord ++ tailWord_7270443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270443).length < 2 ^ (prefixWord ++ tailWord_7270443).sum := by decide
  have hdescent : baseEnd_7270443 < baseStart_7270443 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270460 : List Nat := [2, 2, 2, 2, 2, 1, 2, 3, 1, 3, 3]
def baseStart_7270460 : Nat := 118140960795 + 7270460 * 2 ^ 59
def prefixEnd_7270460 : Nat := 4983230072969 + 3 ^ 40 * 7270460 * 2
def baseEnd_7270460 : Nat := 3733240559287729525513769

theorem tailTrace_7270460 : CollatzResearch.WordTrace tailWord_7270460 prefixEnd_7270460 3733240559287729525513769 := by
  unfold tailWord_7270460
  simp only [CollatzResearch.WordTrace]
  refine ⟨132587730620186295278332417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176783640826915060371109889 132587730620186295278332417)
  ·
    refine ⟨99440797965139721458749313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132587730620186295278332417 99440797965139721458749313)
    ·
      refine ⟨74580598473854791094061985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99440797965139721458749313 74580598473854791094061985)
      ·
        refine ⟨55935448855391093320546489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74580598473854791094061985 55935448855391093320546489)
        ·
          refine ⟨41951586641543319990409867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55935448855391093320546489 41951586641543319990409867)
          ·
            refine ⟨62927379962314979985614801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41951586641543319990409867 62927379962314979985614801)
            ·
              refine ⟨47195534971736234989211101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62927379962314979985614801 47195534971736234989211101)
              ·
                refine ⟨17698325614401088120954163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47195534971736234989211101 17698325614401088120954163)
                ·
                  refine ⟨26547488421601632181431245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17698325614401088120954163 26547488421601632181431245)
                  ·
                    refine ⟨9955308158100612068036717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26547488421601632181431245 9955308158100612068036717)
                    ·
                      refine ⟨3733240559287729525513769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9955308158100612068036717 3733240559287729525513769)
                      ·
                        rfl

theorem cell23_7270460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_7270460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270460 prefixEnd_7270460 := by exact prefixLift 7270460
  have htrace : WordTrace (prefixWord ++ tailWord_7270460) baseStart_7270460 baseEnd_7270460 := by
    simpa [prefixWord, tailWord_7270460, baseEnd_7270460] using wordTrace_append hprefix tailTrace_7270460
  have hstable : (prefixWord ++ tailWord_7270460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270460).length < 2 ^ (prefixWord ++ tailWord_7270460).sum := by decide
  have hdescent : baseEnd_7270460 < baseStart_7270460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270477 : List Nat := [1, 6, 1, 1, 1, 1, 3, 2, 1, 3, 3]
def baseStart_7270477 : Nat := 118140960795 + 7270477 * 2 ^ 59
def prefixEnd_7270477 : Nat := 4983230072969 + 3 ^ 40 * 7270477 * 2
def baseEnd_7270477 : Nat := 3733249288458855959001191

theorem tailTrace_7270477 : CollatzResearch.WordTrace tailWord_7270477 prefixEnd_7270477 3733249288458855959001191 := by
  unfold tailWord_7270477
  simp only [CollatzResearch.WordTrace]
  refine ⟨265176081281311002460033685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176784054187540668306689123 265176081281311002460033685)
  ·
    refine ⟨12430128810061453240314079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 265176081281311002460033685 12430128810061453240314079)
    ·
      refine ⟨18645193215092179860471119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12430128810061453240314079 18645193215092179860471119)
      ·
        refine ⟨27967789822638269790706679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18645193215092179860471119 27967789822638269790706679)
        ·
          refine ⟨41951684733957404686060019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27967789822638269790706679 41951684733957404686060019)
          ·
            refine ⟨62927527100936107029090029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41951684733957404686060019 62927527100936107029090029)
            ·
              refine ⟨23597822662851040135908761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62927527100936107029090029 23597822662851040135908761)
              ·
                refine ⟨17698366997138280101931571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23597822662851040135908761 17698366997138280101931571)
                ·
                  refine ⟨26547550495707420152897357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17698366997138280101931571 26547550495707420152897357)
                  ·
                    refine ⟨9955331435890282557336509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26547550495707420152897357 9955331435890282557336509)
                    ·
                      refine ⟨3733249288458855959001191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9955331435890282557336509 3733249288458855959001191)
                      ·
                        rfl

theorem cell23_7270477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_7270477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270477 prefixEnd_7270477 := by exact prefixLift 7270477
  have htrace : WordTrace (prefixWord ++ tailWord_7270477) baseStart_7270477 baseEnd_7270477 := by
    simpa [prefixWord, tailWord_7270477, baseEnd_7270477] using wordTrace_append hprefix tailTrace_7270477
  have hstable : (prefixWord ++ tailWord_7270477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270477).length < 2 ^ (prefixWord ++ tailWord_7270477).sum := by decide
  have hdescent : baseEnd_7270477 < baseStart_7270477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270487 : List Nat := [1, 1, 3, 2, 2, 1, 2, 5, 1, 3, 2]
def baseStart_7270487 : Nat := 118140960795 + 7270487 * 2 ^ 59
def prefixEnd_7270487 : Nat := 4983230072969 + 3 ^ 40 * 7270487 * 2
def baseEnd_7270487 : Nat := 3733254423265400919876145

theorem tailTrace_7270487 : CollatzResearch.WordTrace tailWord_7270487 prefixEnd_7270487 3733254423265400919876145 := by
  unfold tailWord_7270487
  simp only [CollatzResearch.WordTrace]
  refine ⟨265176446011274774167897715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176784297340849849445265143 265176446011274774167897715)
  ·
    refine ⟨397764669016912161251846573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265176446011274774167897715 397764669016912161251846573)
    ·
      refine ⟨149161750881342060469442465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 397764669016912161251846573 149161750881342060469442465)
      ·
        refine ⟨111871313161006545352081849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149161750881342060469442465 111871313161006545352081849)
        ·
          refine ⟨83903484870754909014061387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111871313161006545352081849 83903484870754909014061387)
          ·
            refine ⟨125855227306132363521092081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83903484870754909014061387 125855227306132363521092081)
            ·
              refine ⟨94391420479599272640819061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125855227306132363521092081 94391420479599272640819061)
              ·
                refine ⟨8849195669962431810076787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94391420479599272640819061 8849195669962431810076787)
                ·
                  refine ⟨13273793504943647715115181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8849195669962431810076787 13273793504943647715115181)
                  ·
                    refine ⟨4977672564353867893168193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13273793504943647715115181 4977672564353867893168193)
                    ·
                      refine ⟨3733254423265400919876145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4977672564353867893168193 3733254423265400919876145)
                      ·
                        rfl

theorem cell23_7270487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 3, 2].length) (baseStart_7270487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270487 prefixEnd_7270487 := by exact prefixLift 7270487
  have htrace : WordTrace (prefixWord ++ tailWord_7270487) baseStart_7270487 baseEnd_7270487 := by
    simpa [prefixWord, tailWord_7270487, baseEnd_7270487] using wordTrace_append hprefix tailTrace_7270487
  have hstable : (prefixWord ++ tailWord_7270487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270487).length < 2 ^ (prefixWord ++ tailWord_7270487).sum := by decide
  have hdescent : baseEnd_7270487 < baseStart_7270487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270510 : List Nat := [4, 1, 2, 2, 1, 1, 3, 1, 2, 6]
def baseStart_7270510 : Nat := 118140960795 + 7270510 * 2 ^ 59
def prefixEnd_7270510 : Nat := 4983230072969 + 3 ^ 40 * 7270510 * 2
def baseEnd_7270510 : Nat := 1244422077773484776629513

theorem tailTrace_7270510 : CollatzResearch.WordTrace tailWord_7270510 prefixEnd_7270510 1244422077773484776629513 := by
  unfold tailWord_7270510
  simp only [CollatzResearch.WordTrace]
  refine ⟨33147160611273931136998123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176784856593460966063989989 33147160611273931136998123)
  ·
    refine ⟨49720740916910896705497185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33147160611273931136998123 49720740916910896705497185)
    ·
      refine ⟨37290555687683172529122889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49720740916910896705497185 37290555687683172529122889)
      ·
        refine ⟨27967916765762379396842167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37290555687683172529122889 27967916765762379396842167)
        ·
          refine ⟨41951875148643569095263251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27967916765762379396842167 41951875148643569095263251)
          ·
            refine ⟨62927812722965353642894877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41951875148643569095263251 62927812722965353642894877)
            ·
              refine ⟨23597929771112007616085579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62927812722965353642894877 23597929771112007616085579)
              ·
                refine ⟨35396894656668011424128369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23597929771112007616085579 35396894656668011424128369)
                ·
                  refine ⟨26547670992501008568096277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35396894656668011424128369 26547670992501008568096277)
                  ·
                    refine ⟨1244422077773484776629513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26547670992501008568096277 1244422077773484776629513)
                    ·
                      rfl

theorem cell23_7270510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_7270510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270510 prefixEnd_7270510 := by exact prefixLift 7270510
  have htrace : WordTrace (prefixWord ++ tailWord_7270510) baseStart_7270510 baseEnd_7270510 := by
    simpa [prefixWord, tailWord_7270510, baseEnd_7270510] using wordTrace_append hprefix tailTrace_7270510
  have hstable : (prefixWord ++ tailWord_7270510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270510).length < 2 ^ (prefixWord ++ tailWord_7270510).sum := by decide
  have hdescent : baseEnd_7270510 < baseStart_7270510 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270557 : List Nat := [1, 4, 2, 1, 1, 3, 2, 4, 5]
def baseStart_7270557 : Nat := 118140960795 + 7270557 * 2 ^ 59
def prefixEnd_7270557 : Nat := 4983230072969 + 3 ^ 40 * 7270557 * 2
def baseEnd_7270557 : Nat := 414810040767912849555647

theorem tailTrace_7270557 : CollatzResearch.WordTrace tailWord_7270557 prefixEnd_7270557 414810040767912849555647 := by
  unfold tailWord_7270557
  simp only [CollatzResearch.WordTrace]
  refine ⟨265178999121021176122945925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176785999414014117415297283 265178999121021176122945925)
  ·
    refine ⟨49721062335191470523052361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265178999121021176122945925 49721062335191470523052361)
    ·
      refine ⟨37290796751393602892289271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49721062335191470523052361 37290796751393602892289271)
      ·
        refine ⟨55936195127090404338433907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37290796751393602892289271 55936195127090404338433907)
        ·
          refine ⟨83904292690635606507650861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55936195127090404338433907 83904292690635606507650861)
          ·
            refine ⟨31464109758988352440369073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83904292690635606507650861 31464109758988352440369073)
            ·
              refine ⟨23598082319241264330276805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31464109758988352440369073 23598082319241264330276805)
              ·
                refine ⟨4424640434857737061926901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23598082319241264330276805 4424640434857737061926901)
                ·
                  refine ⟨414810040767912849555647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4424640434857737061926901 414810040767912849555647)
                  ·
                    rfl

theorem cell23_7270557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 4, 5].length) (baseStart_7270557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270557 prefixEnd_7270557 := by exact prefixLift 7270557
  have htrace : WordTrace (prefixWord ++ tailWord_7270557) baseStart_7270557 baseEnd_7270557 := by
    simpa [prefixWord, tailWord_7270557, baseEnd_7270557] using wordTrace_append hprefix tailTrace_7270557
  have hstable : (prefixWord ++ tailWord_7270557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270557).length < 2 ^ (prefixWord ++ tailWord_7270557).sum := by decide
  have hdescent : baseEnd_7270557 < baseStart_7270557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
