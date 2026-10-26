import V185TrunkScan22Chunk240

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2148994 : List Nat := [3, 4, 3, 1, 2, 1, 2, 2, 4]
def baseStart_2148994 : Nat := 118140960795 + 2148994 * 2 ^ 59
def prefixEnd_2148994 : Nat := 4983230072969 + 3 ^ 40 * 2148994 * 2
def baseEnd_2148994 : Nat := 245214854584060063287103

theorem tailTrace_2148994 : CollatzResearch.WordTrace tailWord_2148994 prefixEnd_2148994 245214854584060063287103 := by
  unfold tailWord_2148994
  simp only [CollatzResearch.WordTrace]
  refine ⟨19595062594142307950109509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52253500251046154533625357 19595062594142307950109509)
  ·
    refine ⟨3674074236401682740645533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19595062594142307950109509 3674074236401682740645533)
    ·
      refine ⟨1377777838650631027742075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3674074236401682740645533 1377777838650631027742075)
      ·
        refine ⟨2066666757975946541613113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1377777838650631027742075 2066666757975946541613113)
        ·
          refine ⟨1550000068481959906209835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2066666757975946541613113 1550000068481959906209835)
          ·
            refine ⟨2325000102722939859314753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1550000068481959906209835 2325000102722939859314753)
            ·
              refine ⟨1743750077042204894486065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2325000102722939859314753 1743750077042204894486065)
              ·
                refine ⟨1307812557781653670864549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1743750077042204894486065 1307812557781653670864549)
                ·
                  refine ⟨245214854584060063287103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1307812557781653670864549 245214854584060063287103)
                  ·
                    rfl

theorem cell22_2148994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_2148994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2148994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2148994 prefixEnd_2148994 := by exact prefixLift 2148994
  have htrace : WordTrace (prefixWord ++ tailWord_2148994) baseStart_2148994 baseEnd_2148994 := by
    simpa [prefixWord, tailWord_2148994, baseEnd_2148994] using wordTrace_append hprefix tailTrace_2148994
  have hstable : (prefixWord ++ tailWord_2148994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148994).length < 2 ^ (prefixWord ++ tailWord_2148994).sum := by decide
  have hdescent : baseEnd_2148994 < baseStart_2148994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149089 : List Nat := [1, 2, 3, 1, 4, 1, 4, 6]
def baseStart_2149089 : Nat := 118140960795 + 2149089 * 2 ^ 59
def prefixEnd_2149089 : Nat := 4983230072969 + 3 ^ 40 * 2149089 * 2
def baseEnd_2149089 : Nat := 81741898243736845415113

theorem tailTrace_2149089 : CollatzResearch.WordTrace tailWord_2149089 prefixEnd_2149089 81741898243736845415113 := by
  unfold tailWord_2149089
  simp only [CollatzResearch.WordTrace]
  refine ⟨78383715311225063025146321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52255810207483375350097547 78383715311225063025146321)
  ·
    refine ⟨58787786483418797268859741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78383715311225063025146321 58787786483418797268859741)
    ·
      refine ⟨22045419931282048975822403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58787786483418797268859741 22045419931282048975822403)
      ·
        refine ⟨33068129896923073463733605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22045419931282048975822403 33068129896923073463733605)
        ·
          refine ⟨6200274355673076274450051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33068129896923073463733605 6200274355673076274450051)
          ·
            refine ⟨9300411533509614411675077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6200274355673076274450051 9300411533509614411675077)
            ·
              refine ⟨1743827162533052702189077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9300411533509614411675077 1743827162533052702189077)
              ·
                refine ⟨81741898243736845415113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1743827162533052702189077 81741898243736845415113)
                ·
                  rfl

theorem cell22_2149089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 6].length) (baseStart_2149089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2149089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2149089 prefixEnd_2149089 := by exact prefixLift 2149089
  have htrace : WordTrace (prefixWord ++ tailWord_2149089) baseStart_2149089 baseEnd_2149089 := by
    simpa [prefixWord, tailWord_2149089, baseEnd_2149089] using wordTrace_append hprefix tailTrace_2149089
  have hstable : (prefixWord ++ tailWord_2149089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149089).length < 2 ^ (prefixWord ++ tailWord_2149089).sum := by decide
  have hdescent : baseEnd_2149089 < baseStart_2149089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149117 : List Nat := [1, 4, 1, 1, 1, 1, 3, 3, 7]
def baseStart_2149117 : Nat := 118140960795 + 2149117 * 2 ^ 59
def prefixEnd_2149117 : Nat := 4983230072969 + 3 ^ 40 * 2149117 * 2
def baseEnd_2149117 : Nat := 245228889721949623011977

theorem tailTrace_2149117 : CollatzResearch.WordTrace tailWord_2149117 prefixEnd_2149117 245228889721949623011977 := by
  unfold tailWord_2149117
  simp only [CollatzResearch.WordTrace]
  refine ⟨78384736555123623807165605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52256491036749082538110403 78384736555123623807165605)
  ·
    refine ⟨14697138104085679463843551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78384736555123623807165605 14697138104085679463843551)
    ·
      refine ⟨22045707156128519195765327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14697138104085679463843551 22045707156128519195765327)
      ·
        refine ⟨33068560734192778793647991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22045707156128519195765327 33068560734192778793647991)
        ·
          refine ⟨49602841101289168190471987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33068560734192778793647991 49602841101289168190471987)
          ·
            refine ⟨74404261651933752285707981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49602841101289168190471987 74404261651933752285707981)
            ·
              refine ⟨27901598119475157107140493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74404261651933752285707981 27901598119475157107140493)
              ·
                refine ⟨10463099294803183915177685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27901598119475157107140493 10463099294803183915177685)
                ·
                  refine ⟨245228889721949623011977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10463099294803183915177685 245228889721949623011977)
                  ·
                    rfl

theorem cell22_2149117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_2149117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2149117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2149117 prefixEnd_2149117 := by exact prefixLift 2149117
  have htrace : WordTrace (prefixWord ++ tailWord_2149117) baseStart_2149117 baseEnd_2149117 := by
    simpa [prefixWord, tailWord_2149117, baseEnd_2149117] using wordTrace_append hprefix tailTrace_2149117
  have hstable : (prefixWord ++ tailWord_2149117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149117).length < 2 ^ (prefixWord ++ tailWord_2149117).sum := by decide
  have hdescent : baseEnd_2149117 < baseStart_2149117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149132 : List Nat := [2, 2, 1, 2, 2, 1, 1, 3, 1, 7]
def baseStart_2149132 : Nat := 118140960795 + 2149132 * 2 ^ 59
def prefixEnd_2149132 : Nat := 4983230072969 + 3 ^ 40 * 2149132 * 2
def baseEnd_2149132 : Nat := 735691803972393829910885

theorem tailTrace_2149132 : CollatzResearch.WordTrace tailWord_2149132 prefixEnd_2149132 735691803972393829910885 := by
  unfold tailWord_2149132
  simp only [CollatzResearch.WordTrace]
  refine ⟨39192641825034640684480825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52256855766712854245974433 39192641825034640684480825)
  ·
    refine ⟨29394481368775980513360619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39192641825034640684480825 29394481368775980513360619)
    ·
      refine ⟨44091722053163970770040929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29394481368775980513360619 44091722053163970770040929)
      ·
        refine ⟨33068791539872978077530697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44091722053163970770040929 33068791539872978077530697)
        ·
          refine ⟨24801593654904733558148023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33068791539872978077530697 24801593654904733558148023)
          ·
            refine ⟨37202390482357100337222035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24801593654904733558148023 37202390482357100337222035)
            ·
              refine ⟨55803585723535650505833053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37202390482357100337222035 55803585723535650505833053)
              ·
                refine ⟨20926344646325868939687395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55803585723535650505833053 20926344646325868939687395)
                ·
                  refine ⟨31389516969488803409531093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20926344646325868939687395 31389516969488803409531093)
                  ·
                    refine ⟨735691803972393829910885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31389516969488803409531093 735691803972393829910885)
                    ·
                      rfl

theorem cell22_2149132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_2149132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2149132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2149132 prefixEnd_2149132 := by exact prefixLift 2149132
  have htrace : WordTrace (prefixWord ++ tailWord_2149132) baseStart_2149132 baseEnd_2149132 := by
    simpa [prefixWord, tailWord_2149132, baseEnd_2149132] using wordTrace_append hprefix tailTrace_2149132
  have hstable : (prefixWord ++ tailWord_2149132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149132).length < 2 ^ (prefixWord ++ tailWord_2149132).sum := by decide
  have hdescent : baseEnd_2149132 < baseStart_2149132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149209 : List Nat := [1, 2, 1, 2, 2, 5, 1, 1, 1, 6]
def baseStart_2149209 : Nat := 118140960795 + 2149209 * 2 ^ 59
def prefixEnd_2149209 : Nat := 4983230072969 + 3 ^ 40 * 2149209 * 2
def baseEnd_2149209 : Nat := 735718162645991295735649

theorem tailTrace_2149209 : CollatzResearch.WordTrace tailWord_2149209 prefixEnd_2149209 735718162645991295735649 := by
  unfold tailWord_2149209
  simp only [CollatzResearch.WordTrace]
  refine ⟨78388092070790323519514681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52258728047193549013009787 78388092070790323519514681)
  ·
    refine ⟨58791069053092742639636011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78388092070790323519514681 58791069053092742639636011)
    ·
      refine ⟨88186603579639113959454017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58791069053092742639636011 88186603579639113959454017)
      ·
        refine ⟨66139952684729335469590513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88186603579639113959454017 66139952684729335469590513)
        ·
          refine ⟨49604964513547001602192885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66139952684729335469590513 49604964513547001602192885)
          ·
            refine ⟨4650465423145031400205583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49604964513547001602192885 4650465423145031400205583)
            ·
              refine ⟨6975698134717547100308375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4650465423145031400205583 6975698134717547100308375)
              ·
                refine ⟨10463547202076320650462563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6975698134717547100308375 10463547202076320650462563)
                ·
                  refine ⟨15695320803114480975693845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10463547202076320650462563 15695320803114480975693845)
                  ·
                    refine ⟨735718162645991295735649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15695320803114480975693845 735718162645991295735649)
                    ·
                      rfl

theorem cell22_2149209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 6].length) (baseStart_2149209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2149209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2149209 prefixEnd_2149209 := by exact prefixLift 2149209
  have htrace : WordTrace (prefixWord ++ tailWord_2149209) baseStart_2149209 baseEnd_2149209 := by
    simpa [prefixWord, tailWord_2149209, baseEnd_2149209] using wordTrace_append hprefix tailTrace_2149209
  have hstable : (prefixWord ++ tailWord_2149209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149209).length < 2 ^ (prefixWord ++ tailWord_2149209).sum := by decide
  have hdescent : baseEnd_2149209 < baseStart_2149209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149224 : List Nat := [2, 1, 4, 2, 1, 3, 9]
def baseStart_2149224 : Nat := 118140960795 + 2149224 * 2 ^ 59
def prefixEnd_2149224 : Nat := 4983230072969 + 3 ^ 40 * 2149224 * 2
def baseEnd_2149224 : Nat := 27249011016760602096689

theorem tailTrace_2149224 : CollatzResearch.WordTrace tailWord_2149224 prefixEnd_2149224 27249011016760602096689 := by
  unfold tailWord_2149224
  simp only [CollatzResearch.WordTrace]
  refine ⟨39194319582867990540655363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52259092777157320720873817 39194319582867990540655363)
  ·
    refine ⟨58791479374301985810983045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39194319582867990540655363 58791479374301985810983045)
    ·
      refine ⟨11023402382681622339559321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58791479374301985810983045 11023402382681622339559321)
      ·
        refine ⟨8267551787011216754669491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11023402382681622339559321 8267551787011216754669491)
        ·
          refine ⟨12401327680516825132004237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8267551787011216754669491 12401327680516825132004237)
          ·
            refine ⟨4650497880193809424501589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12401327680516825132004237 4650497880193809424501589)
            ·
              refine ⟨27249011016760602096689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4650497880193809424501589 27249011016760602096689)
              ·
                rfl

theorem cell22_2149224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 9].length) (baseStart_2149224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2149224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2149224 prefixEnd_2149224 := by exact prefixLift 2149224
  have htrace : WordTrace (prefixWord ++ tailWord_2149224) baseStart_2149224 baseEnd_2149224 := by
    simpa [prefixWord, tailWord_2149224, baseEnd_2149224] using wordTrace_append hprefix tailTrace_2149224
  have hstable : (prefixWord ++ tailWord_2149224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149224).length < 2 ^ (prefixWord ++ tailWord_2149224).sum := by decide
  have hdescent : baseEnd_2149224 < baseStart_2149224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149258 : List Nat := [3, 1, 2, 4, 1, 3, 2, 6]
def baseStart_2149258 : Nat := 118140960795 + 2149258 * 2 ^ 59
def prefixEnd_2149258 : Nat := 4983230072969 + 3 ^ 40 * 2149258 * 2
def baseEnd_2149258 : Nat := 81748326260819055695611

theorem tailTrace_2149258 : CollatzResearch.WordTrace tailWord_2149258 prefixEnd_2149258 81748326260819055695611 := by
  unfold tailWord_2149258
  simp only [CollatzResearch.WordTrace]
  refine ⟨19597469811903201222012107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52259919498408536592032285 19597469811903201222012107)
  ·
    refine ⟨29396204717854801833018161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19597469811903201222012107 29396204717854801833018161)
    ·
      refine ⟨22047153538391101374763621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29396204717854801833018161 22047153538391101374763621)
      ·
        refine ⟨4133841288448331507768179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22047153538391101374763621 4133841288448331507768179)
        ·
          refine ⟨6200761932672497261652269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4133841288448331507768179 6200761932672497261652269)
          ·
            refine ⟨2325285724752186473119601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6200761932672497261652269 2325285724752186473119601)
            ·
              refine ⟨1743964293564139854839701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2325285724752186473119601 1743964293564139854839701)
              ·
                refine ⟨81748326260819055695611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1743964293564139854839701 81748326260819055695611)
                ·
                  rfl

theorem cell22_2149258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 6].length) (baseStart_2149258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2149258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2149258 prefixEnd_2149258 := by exact prefixLift 2149258
  have htrace : WordTrace (prefixWord ++ tailWord_2149258) baseStart_2149258 baseEnd_2149258 := by
    simpa [prefixWord, tailWord_2149258, baseEnd_2149258] using wordTrace_append hprefix tailTrace_2149258
  have hstable : (prefixWord ++ tailWord_2149258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149258).length < 2 ^ (prefixWord ++ tailWord_2149258).sum := by decide
  have hdescent : baseEnd_2149258 < baseStart_2149258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149269 : List Nat := [1, 3, 2, 1, 1, 4, 1, 2, 7]
def baseStart_2149269 : Nat := 118140960795 + 2149269 * 2 ^ 59
def prefixEnd_2149269 : Nat := 4983230072969 + 3 ^ 40 * 2149269 * 2
def baseEnd_2149269 : Nat := 245246233957390379745155

theorem tailTrace_2149269 : CollatzResearch.WordTrace tailWord_2149269 prefixEnd_2149269 245246233957390379745155 := by
  unfold tailWord_2149269
  simp only [CollatzResearch.WordTrace]
  refine ⟨78390280450572953766698861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52260186967048635844465907 78390280450572953766698861)
  ·
    refine ⟨29396355168964857662512073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78390280450572953766698861 29396355168964857662512073)
    ·
      refine ⟨22047266376723643246884055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29396355168964857662512073 22047266376723643246884055)
      ·
        refine ⟨33070899565085464870326083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22047266376723643246884055 33070899565085464870326083)
        ·
          refine ⟨49606349347628197305489125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33070899565085464870326083 49606349347628197305489125)
          ·
            refine ⟨9301190502680286994779211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49606349347628197305489125 9301190502680286994779211)
            ·
              refine ⟨13951785754020430492168817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9301190502680286994779211 13951785754020430492168817)
              ·
                refine ⟨10463839315515322869126613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13951785754020430492168817 10463839315515322869126613)
                ·
                  refine ⟨245246233957390379745155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10463839315515322869126613 245246233957390379745155)
                  ·
                    rfl

theorem cell22_2149269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 7].length) (baseStart_2149269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2149269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2149269 prefixEnd_2149269 := by exact prefixLift 2149269
  have htrace : WordTrace (prefixWord ++ tailWord_2149269) baseStart_2149269 baseEnd_2149269 := by
    simpa [prefixWord, tailWord_2149269, baseEnd_2149269] using wordTrace_append hprefix tailTrace_2149269
  have hstable : (prefixWord ++ tailWord_2149269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149269).length < 2 ^ (prefixWord ++ tailWord_2149269).sum := by decide
  have hdescent : baseEnd_2149269 < baseStart_2149269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149344 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 5, 6]
def baseStart_2149344 : Nat := 118140960795 + 2149344 * 2 ^ 59
def prefixEnd_2149344 : Nat := 4983230072969 + 3 ^ 40 * 2149344 * 2
def baseEnd_2149344 : Nat := 735764375904895943610235

theorem tailTrace_2149344 : CollatzResearch.WordTrace tailWord_2149344 prefixEnd_2149344 735764375904895943610235 := by
  unfold tailWord_2149344
  simp only [CollatzResearch.WordTrace]
  refine ⟨39196507962650620787839543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52262010616867494383786057 39196507962650620787839543)
  ·
    refine ⟨58794761943975931181759315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39196507962650620787839543 58794761943975931181759315)
    ·
      refine ⟨88192142915963896772638973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58794761943975931181759315 88192142915963896772638973)
      ·
        refine ⟨33072053593486461289739615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88192142915963896772638973 33072053593486461289739615)
        ·
          refine ⟨49608080390229691934609423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33072053593486461289739615 49608080390229691934609423)
          ·
            refine ⟨74412120585344537901914135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49608080390229691934609423 74412120585344537901914135)
            ·
              refine ⟨111618180878016806852871203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74412120585344537901914135 111618180878016806852871203)
              ·
                refine ⟨167427271317025210279306805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111618180878016806852871203 167427271317025210279306805)
                ·
                  refine ⟨15696306685971113463685013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 167427271317025210279306805 15696306685971113463685013)
                  ·
                    refine ⟨735764375904895943610235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15696306685971113463685013 735764375904895943610235)
                    ·
                      rfl

theorem cell22_2149344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 5, 6].length) (baseStart_2149344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2149344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2149344 prefixEnd_2149344 := by exact prefixLift 2149344
  have htrace : WordTrace (prefixWord ++ tailWord_2149344) baseStart_2149344 baseEnd_2149344 := by
    simpa [prefixWord, tailWord_2149344, baseEnd_2149344] using wordTrace_append hprefix tailTrace_2149344
  have hstable : (prefixWord ++ tailWord_2149344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149344).length < 2 ^ (prefixWord ++ tailWord_2149344).sum := by decide
  have hdescent : baseEnd_2149344 < baseStart_2149344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149365 : List Nat := [1, 3, 5, 2, 1, 1, 1, 2, 6]
def baseStart_2149365 : Nat := 118140960795 + 2149365 * 2 ^ 59
def prefixEnd_2149365 : Nat := 4983230072969 + 3 ^ 40 * 2149365 * 2
def baseEnd_2149365 : Nat := 245257188211352962945057

theorem tailTrace_2149365 : CollatzResearch.WordTrace tailWord_2149365 prefixEnd_2149365 245257188211352962945057 := by
  unfold tailWord_2149365
  simp only [CollatzResearch.WordTrace]
  refine ⟨78393781858225162162193549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52262521238816774774795699 78393781858225162162193549)
  ·
    refine ⟨29397668196834435810822581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78393781858225162162193549 29397668196834435810822581)
    ·
      refine ⟨2756031393453228357264617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29397668196834435810822581 2756031393453228357264617)
      ·
        refine ⟨2067023545089921267948463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2756031393453228357264617 2067023545089921267948463)
        ·
          refine ⟨3100535317634881901922695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2067023545089921267948463 3100535317634881901922695)
          ·
            refine ⟨4650802976452322852884043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3100535317634881901922695 4650802976452322852884043)
            ·
              refine ⟨6976204464678484279326065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4650802976452322852884043 6976204464678484279326065)
              ·
                refine ⟨5232153348508863209494549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6976204464678484279326065 5232153348508863209494549)
                ·
                  refine ⟨245257188211352962945057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5232153348508863209494549 245257188211352962945057)
                  ·
                    rfl

theorem cell22_2149365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 6].length) (baseStart_2149365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2149365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2149365 prefixEnd_2149365 := by exact prefixLift 2149365
  have htrace : WordTrace (prefixWord ++ tailWord_2149365) baseStart_2149365 baseEnd_2149365 := by
    simpa [prefixWord, tailWord_2149365, baseEnd_2149365] using wordTrace_append hprefix tailTrace_2149365
  have hstable : (prefixWord ++ tailWord_2149365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149365).length < 2 ^ (prefixWord ++ tailWord_2149365).sum := by decide
  have hdescent : baseEnd_2149365 < baseStart_2149365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149438 : List Nat := [4, 2, 1, 3, 1, 1, 1, 2, 7]
def baseStart_2149438 : Nat := 118140960795 + 2149438 * 2 ^ 59
def prefixEnd_2149438 : Nat := 4983230072969 + 3 ^ 40 * 2149438 * 2
def baseEnd_2149438 : Nat := 245265518008637010586649

theorem tailTrace_2149438 : CollatzResearch.WordTrace tailWord_2149438 prefixEnd_2149438 245265518008637010586649 := by
  unfold tailWord_2149438
  simp only [CollatzResearch.WordTrace]
  refine ⟨9799555548370086953700121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52264296257973797086400645 9799555548370086953700121)
  ·
    refine ⟨7349666661277565215275091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9799555548370086953700121 7349666661277565215275091)
    ·
      refine ⟨11024499991916347822912637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7349666661277565215275091 11024499991916347822912637)
      ·
        refine ⟨4134187496968630433592239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11024499991916347822912637 4134187496968630433592239)
        ·
          refine ⟨6201281245452945650388359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4134187496968630433592239 6201281245452945650388359)
          ·
            refine ⟨9301921868179418475582539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6201281245452945650388359 9301921868179418475582539)
            ·
              refine ⟨13952882802269127713373809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9301921868179418475582539 13952882802269127713373809)
              ·
                refine ⟨10464662101701845785030357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13952882802269127713373809 10464662101701845785030357)
                ·
                  refine ⟨245265518008637010586649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10464662101701845785030357 245265518008637010586649)
                  ·
                    rfl

theorem cell22_2149438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_2149438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2149438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2149438 prefixEnd_2149438 := by exact prefixLift 2149438
  have htrace : WordTrace (prefixWord ++ tailWord_2149438) baseStart_2149438 baseEnd_2149438 := by
    simpa [prefixWord, tailWord_2149438, baseEnd_2149438] using wordTrace_append hprefix tailTrace_2149438
  have hstable : (prefixWord ++ tailWord_2149438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149438).length < 2 ^ (prefixWord ++ tailWord_2149438).sum := by decide
  have hdescent : baseEnd_2149438 < baseStart_2149438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149466 : List Nat := [3, 1, 1, 2, 1, 1, 2, 5, 6]
def baseStart_2149466 : Nat := 118140960795 + 2149466 * 2 ^ 59
def prefixEnd_2149466 : Nat := 4983230072969 + 3 ^ 40 * 2149466 * 2
def baseEnd_2149466 : Nat := 245268712999376097353287

theorem tailTrace_2149466 : CollatzResearch.WordTrace tailWord_2149466 prefixEnd_2149466 245268712999376097353287 := by
  unfold tailWord_2149466
  simp only [CollatzResearch.WordTrace]
  refine ⟨19599366407714814102905063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52264977087239504274413501 19599366407714814102905063)
  ·
    refine ⟨29399049611572221154357595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19599366407714814102905063 29399049611572221154357595)
    ·
      refine ⟨44098574417358331731536393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29399049611572221154357595 44098574417358331731536393)
      ·
        refine ⟨33073930813018748798652295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44098574417358331731536393 33073930813018748798652295)
        ·
          refine ⟨49610896219528123197978443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33073930813018748798652295 49610896219528123197978443)
          ·
            refine ⟨74416344329292184796967665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49610896219528123197978443 74416344329292184796967665)
            ·
              refine ⟨55812258246969138597725749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74416344329292184796967665 55812258246969138597725749)
              ·
                refine ⟨5232399210653356743536789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55812258246969138597725749 5232399210653356743536789)
                ·
                  refine ⟨245268712999376097353287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5232399210653356743536789 245268712999376097353287)
                  ·
                    rfl

theorem cell22_2149466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 6].length) (baseStart_2149466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2149466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2149466 prefixEnd_2149466 := by exact prefixLift 2149466
  have htrace : WordTrace (prefixWord ++ tailWord_2149466) baseStart_2149466 baseEnd_2149466 := by
    simpa [prefixWord, tailWord_2149466, baseEnd_2149466] using wordTrace_append hprefix tailTrace_2149466
  have hstable : (prefixWord ++ tailWord_2149466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149466).length < 2 ^ (prefixWord ++ tailWord_2149466).sum := by decide
  have hdescent : baseEnd_2149466 < baseStart_2149466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149468 : List Nat := [2, 2, 4, 1, 1, 1, 2, 2, 3, 4]
def baseStart_2149468 : Nat := 118140960795 + 2149468 * 2 ^ 59
def prefixEnd_2149468 : Nat := 4983230072969 + 3 ^ 40 * 2149468 * 2
def baseEnd_2149468 : Nat := 735806823639000953509855

theorem tailTrace_2149468 : CollatzResearch.WordTrace tailWord_2149468 prefixEnd_2149468 735806823639000953509855 := by
  unfold tailWord_2149468
  simp only [CollatzResearch.WordTrace]
  refine ⟨39198769288426005376596529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52265025717901340502128705 39198769288426005376596529)
  ·
    refine ⟨29399076966319504032447397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39198769288426005376596529 29399076966319504032447397)
    ·
      refine ⟨5512326931184907006083887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29399076966319504032447397 5512326931184907006083887)
      ·
        refine ⟨8268490396777360509125831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5512326931184907006083887 8268490396777360509125831)
        ·
          refine ⟨12402735595166040763688747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8268490396777360509125831 12402735595166040763688747)
          ·
            refine ⟨18604103392749061145533121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12402735595166040763688747 18604103392749061145533121)
            ·
              refine ⟨13953077544561795859149841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18604103392749061145533121 13953077544561795859149841)
              ·
                refine ⟨10464808158421346894362381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13953077544561795859149841 10464808158421346894362381)
                ·
                  refine ⟨3924303059408005085385893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10464808158421346894362381 3924303059408005085385893)
                  ·
                    refine ⟨735806823639000953509855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3924303059408005085385893 735806823639000953509855)
                    ·
                      rfl

theorem cell22_2149468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_2149468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2149468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2149468 prefixEnd_2149468 := by exact prefixLift 2149468
  have htrace : WordTrace (prefixWord ++ tailWord_2149468) baseStart_2149468 baseEnd_2149468 := by
    simpa [prefixWord, tailWord_2149468, baseEnd_2149468] using wordTrace_append hprefix tailTrace_2149468
  have hstable : (prefixWord ++ tailWord_2149468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149468).length < 2 ^ (prefixWord ++ tailWord_2149468).sum := by decide
  have hdescent : baseEnd_2149468 < baseStart_2149468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149485 : List Nat := [1, 5, 1, 1, 2, 2, 3, 2, 1, 4]
def baseStart_2149485 : Nat := 118140960795 + 2149485 * 2 ^ 59
def prefixEnd_2149485 : Nat := 4983230072969 + 3 ^ 40 * 2149485 * 2
def baseEnd_2149485 : Nat := 735812643086418575834803

theorem tailTrace_2149485 : CollatzResearch.WordTrace tailWord_2149485 prefixEnd_2149485 735812643086418575834803 := by
  unfold tailWord_2149485
  simp only [CollatzResearch.WordTrace]
  refine ⟨78398158617790422656561909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52265439078526948437707939 78398158617790422656561909)
  ·
    refine ⟨7349827370417852124052679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78398158617790422656561909 7349827370417852124052679)
    ·
      refine ⟨11024741055626778186079019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7349827370417852124052679 11024741055626778186079019)
      ·
        refine ⟨16537111583440167279118529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11024741055626778186079019 16537111583440167279118529)
        ·
          refine ⟨12402833687580125459338897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16537111583440167279118529 12402833687580125459338897)
          ·
            refine ⟨9302125265685094094504173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12402833687580125459338897 9302125265685094094504173)
            ·
              refine ⟨3488296974631910285439065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9302125265685094094504173 3488296974631910285439065)
              ·
                refine ⟨2616222730973932714079299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3488296974631910285439065 2616222730973932714079299)
                ·
                  refine ⟨3924334096460899071118949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2616222730973932714079299 3924334096460899071118949)
                  ·
                    refine ⟨735812643086418575834803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3924334096460899071118949 735812643086418575834803)
                    ·
                      rfl

theorem cell22_2149485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_2149485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2149485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2149485 prefixEnd_2149485 := by exact prefixLift 2149485
  have htrace : WordTrace (prefixWord ++ tailWord_2149485) baseStart_2149485 baseEnd_2149485 := by
    simpa [prefixWord, tailWord_2149485, baseEnd_2149485] using wordTrace_append hprefix tailTrace_2149485
  have hstable : (prefixWord ++ tailWord_2149485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149485).length < 2 ^ (prefixWord ++ tailWord_2149485).sum := by decide
  have hdescent : baseEnd_2149485 < baseStart_2149485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149496 : List Nat := [2, 1, 2, 1, 1, 1, 4, 3, 1, 6]
def baseStart_2149496 : Nat := 118140960795 + 2149496 * 2 ^ 59
def prefixEnd_2149496 : Nat := 4983230072969 + 3 ^ 40 * 2149496 * 2
def baseEnd_2149496 : Nat := 735816408611218213809769

theorem tailTrace_2149496 : CollatzResearch.WordTrace tailWord_2149496 prefixEnd_2149496 735816408611218213809769 := by
  unfold tailWord_2149496
  simp only [CollatzResearch.WordTrace]
  refine ⟨39199279910375285767606171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52265706547167047690141561 39199279910375285767606171)
  ·
    refine ⟨58798919865562928651409257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39199279910375285767606171 58798919865562928651409257)
    ·
      refine ⟨44099189899172196488556943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58798919865562928651409257 44099189899172196488556943)
      ·
        refine ⟨66148784848758294732835415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44099189899172196488556943 66148784848758294732835415)
        ·
          refine ⟨99223177273137442099253123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66148784848758294732835415 99223177273137442099253123)
          ·
            refine ⟨148834765909706163148879685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99223177273137442099253123 148834765909706163148879685)
            ·
              refine ⟨27906518608069905590414941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 148834765909706163148879685 27906518608069905590414941)
              ·
                refine ⟨10464944478026214596405603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27906518608069905590414941 10464944478026214596405603)
                ·
                  refine ⟨15697416717039321894608405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10464944478026214596405603 15697416717039321894608405)
                  ·
                    refine ⟨735816408611218213809769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15697416717039321894608405 735816408611218213809769)
                    ·
                      rfl

theorem cell22_2149496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_2149496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2149496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2149496 prefixEnd_2149496 := by exact prefixLift 2149496
  have htrace : WordTrace (prefixWord ++ tailWord_2149496) baseStart_2149496 baseEnd_2149496 := by
    simpa [prefixWord, tailWord_2149496, baseEnd_2149496] using wordTrace_append hprefix tailTrace_2149496
  have hstable : (prefixWord ++ tailWord_2149496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149496).length < 2 ^ (prefixWord ++ tailWord_2149496).sum := by decide
  have hdescent : baseEnd_2149496 < baseStart_2149496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149513 : List Nat := [1, 2, 1, 1, 4, 3, 2, 2, 2, 4]
def baseStart_2149513 : Nat := 118140960795 + 2149513 * 2 ^ 59
def prefixEnd_2149513 : Nat := 4983230072969 + 3 ^ 40 * 2149513 * 2
def baseEnd_2149513 : Nat := 735822228058635836134717

theorem tailTrace_2149513 : CollatzResearch.WordTrace tailWord_2149513 prefixEnd_2149513 735822228058635836134717 := by
  unfold tailWord_2149513
  simp only [CollatzResearch.WordTrace]
  refine ⟨78399179861688983438581193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52266119907792655625720795 78399179861688983438581193)
  ·
    refine ⟨58799384896266737578935895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78399179861688983438581193 58799384896266737578935895)
    ·
      refine ⟨88199077344400106368403843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58799384896266737578935895 88199077344400106368403843)
      ·
        refine ⟨132298616016600159552605765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88199077344400106368403843 132298616016600159552605765)
        ·
          refine ⟨24805990503112529916113581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132298616016600159552605765 24805990503112529916113581)
          ·
            refine ⟨9302246438667198718542593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24805990503112529916113581 9302246438667198718542593)
            ·
              refine ⟨6976684829000399038906945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9302246438667198718542593 6976684829000399038906945)
              ·
                refine ⟨5232513621750299279180209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6976684829000399038906945 5232513621750299279180209)
                ·
                  refine ⟨3924385216312724459385157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5232513621750299279180209 3924385216312724459385157)
                  ·
                    refine ⟨735822228058635836134717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3924385216312724459385157 735822228058635836134717)
                    ·
                      rfl

theorem cell22_2149513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 4].length) (baseStart_2149513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2149513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2149513 prefixEnd_2149513 := by exact prefixLift 2149513
  have htrace : WordTrace (prefixWord ++ tailWord_2149513) baseStart_2149513 baseEnd_2149513 := by
    simpa [prefixWord, tailWord_2149513, baseEnd_2149513] using wordTrace_append hprefix tailTrace_2149513
  have hstable : (prefixWord ++ tailWord_2149513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149513).length < 2 ^ (prefixWord ++ tailWord_2149513).sum := by decide
  have hdescent : baseEnd_2149513 < baseStart_2149513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149528 : List Nat := [2, 1, 2, 4, 2, 1, 3, 7]
def baseStart_2149528 : Nat := 118140960795 + 2149528 * 2 ^ 59
def prefixEnd_2149528 : Nat := 4983230072969 + 3 ^ 40 * 2149528 * 2
def baseEnd_2149528 : Nat := 81758595873908977445519

theorem tailTrace_2149528 : CollatzResearch.WordTrace tailWord_2149528 prefixEnd_2149528 81758595873908977445519 := by
  unfold tailWord_2149528
  simp only [CollatzResearch.WordTrace]
  refine ⟨39199863478317320500188619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52266484637756427333584825 39199863478317320500188619)
  ·
    refine ⟨58799795217475980750282929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39199863478317320500188619 58799795217475980750282929)
    ·
      refine ⟨44099846413106985562712197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58799795217475980750282929 44099846413106985562712197)
      ·
        refine ⟨8268721202457559793008537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44099846413106985562712197 8268721202457559793008537)
        ·
          refine ⟨6201540901843169844756403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8268721202457559793008537 6201540901843169844756403)
          ·
            refine ⟨9302311352764754767134605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6201540901843169844756403 9302311352764754767134605)
            ·
              refine ⟨3488366757286783037675477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9302311352764754767134605 3488366757286783037675477)
              ·
                refine ⟨81758595873908977445519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3488366757286783037675477 81758595873908977445519)
                ·
                  rfl

theorem cell22_2149528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 7].length) (baseStart_2149528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2149528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2149528 prefixEnd_2149528 := by exact prefixLift 2149528
  have htrace : WordTrace (prefixWord ++ tailWord_2149528) baseStart_2149528 baseEnd_2149528 := by
    simpa [prefixWord, tailWord_2149528, baseEnd_2149528] using wordTrace_append hprefix tailTrace_2149528
  have hstable : (prefixWord ++ tailWord_2149528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149528).length < 2 ^ (prefixWord ++ tailWord_2149528).sum := by decide
  have hdescent : baseEnd_2149528 < baseStart_2149528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149635 : List Nat := [1, 1, 1, 3, 2, 6, 1, 1, 6]
def baseStart_2149635 : Nat := 118140960795 + 2149635 * 2 ^ 59
def prefixEnd_2149635 : Nat := 4983230072969 + 3 ^ 40 * 2149635 * 2
def baseEnd_2149635 : Nat := 245287997050622728194781

theorem tailTrace_2149635 : CollatzResearch.WordTrace tailWord_2149635 prefixEnd_2149635 245287997050622728194781 := by
  unfold tailWord_2149635
  simp only [CollatzResearch.WordTrace]
  refine ⟨78403629567246998274522359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52269086378164665516348239 78403629567246998274522359)
  ·
    refine ⟨117605444350870497411783539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78403629567246998274522359 117605444350870497411783539)
    ·
      refine ⟨176408166526305746117675309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117605444350870497411783539 176408166526305746117675309)
      ·
        refine ⟨66153062447364654794128241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176408166526305746117675309 66153062447364654794128241)
        ·
          refine ⟨49614796835523491095596181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66153062447364654794128241 49614796835523491095596181)
          ·
            refine ⟨2325693601665163645106071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 49614796835523491095596181 2325693601665163645106071)
            ·
              refine ⟨3488540402497745467659107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2325693601665163645106071 3488540402497745467659107)
              ·
                refine ⟨5232810603746618201488661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3488540402497745467659107 5232810603746618201488661)
                ·
                  refine ⟨245287997050622728194781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5232810603746618201488661 245287997050622728194781)
                  ·
                    rfl

theorem cell22_2149635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 6].length) (baseStart_2149635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2149635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2149635 prefixEnd_2149635 := by exact prefixLift 2149635
  have htrace : WordTrace (prefixWord ++ tailWord_2149635) baseStart_2149635 baseEnd_2149635 := by
    simpa [prefixWord, tailWord_2149635, baseEnd_2149635] using wordTrace_append hprefix tailTrace_2149635
  have hstable : (prefixWord ++ tailWord_2149635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149635).length < 2 ^ (prefixWord ++ tailWord_2149635).sum := by decide
  have hdescent : baseEnd_2149635 < baseStart_2149635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149684 : List Nat := [2, 5, 1, 1, 1, 1, 4, 2, 2, 3]
def baseStart_2149684 : Nat := 118140960795 + 2149684 * 2 ^ 59
def prefixEnd_2149684 : Nat := 4983230072969 + 3 ^ 40 * 2149684 * 2
def baseEnd_2149684 : Nat := 735880764853248390109193

theorem tailTrace_2149684 : CollatzResearch.WordTrace tailWord_2149684 prefixEnd_2149684 735880764853248390109193 := by
  unfold tailWord_2149684
  simp only [CollatzResearch.WordTrace]
  refine ⟨39202708372034739821528053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52270277829379653095370737 39202708372034739821528053)
  ·
    refine ⟨3675253909878256858268255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39202708372034739821528053 3675253909878256858268255)
    ·
      refine ⟨5512880864817385287402383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3675253909878256858268255 5512880864817385287402383)
      ·
        refine ⟨8269321297226077931103575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5512880864817385287402383 8269321297226077931103575)
        ·
          refine ⟨12403981945839116896655363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8269321297226077931103575 12403981945839116896655363)
          ·
            refine ⟨18605972918758675344983045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12403981945839116896655363 18605972918758675344983045)
            ·
              refine ⟨3488619922267251627184321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18605972918758675344983045 3488619922267251627184321)
              ·
                refine ⟨2616464941700438720388241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3488619922267251627184321 2616464941700438720388241)
                ·
                  refine ⟨1962348706275329040291181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2616464941700438720388241 1962348706275329040291181)
                  ·
                    refine ⟨735880764853248390109193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1962348706275329040291181 735880764853248390109193)
                    ·
                      rfl

theorem cell22_2149684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_2149684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2149684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2149684 prefixEnd_2149684 := by exact prefixLift 2149684
  have htrace : WordTrace (prefixWord ++ tailWord_2149684) baseStart_2149684 baseEnd_2149684 := by
    simpa [prefixWord, tailWord_2149684, baseEnd_2149684] using wordTrace_append hprefix tailTrace_2149684
  have hstable : (prefixWord ++ tailWord_2149684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149684).length < 2 ^ (prefixWord ++ tailWord_2149684).sum := by decide
  have hdescent : baseEnd_2149684 < baseStart_2149684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149686 : List Nat := [5, 1, 2, 3, 1, 1, 1, 4, 4]
def baseStart_2149686 : Nat := 118140960795 + 2149686 * 2 ^ 59
def prefixEnd_2149686 : Nat := 4983230072969 + 3 ^ 40 * 2149686 * 2
def baseEnd_2149686 : Nat := 245293816498040350519729

theorem tailTrace_2149686 : CollatzResearch.WordTrace tailWord_2149686 prefixEnd_2149686 245293816498040350519729 := by
  unfold tailWord_2149686
  simp only [CollatzResearch.WordTrace]
  refine ⟨4900343105628889624039307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52270326460041489323085941 4900343105628889624039307)
  ·
    refine ⟨7350514658443334436058961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4900343105628889624039307 7350514658443334436058961)
    ·
      refine ⟨5512885993832500827044221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7350514658443334436058961 5512885993832500827044221)
      ·
        refine ⟨2067332247687187810141583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5512885993832500827044221 2067332247687187810141583)
        ·
          refine ⟨3100998371530781715212375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2067332247687187810141583 3100998371530781715212375)
          ·
            refine ⟨4651497557296172572818563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3100998371530781715212375 4651497557296172572818563)
            ·
              refine ⟨6977246335944258859227845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4651497557296172572818563 6977246335944258859227845)
              ·
                refine ⟨1308233687989548536105221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6977246335944258859227845 1308233687989548536105221)
                ·
                  refine ⟨245293816498040350519729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1308233687989548536105221 245293816498040350519729)
                  ·
                    rfl

theorem cell22_2149686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_2149686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2149686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2149686 prefixEnd_2149686 := by exact prefixLift 2149686
  have htrace : WordTrace (prefixWord ++ tailWord_2149686) baseStart_2149686 baseEnd_2149686 := by
    simpa [prefixWord, tailWord_2149686, baseEnd_2149686] using wordTrace_append hprefix tailTrace_2149686
  have hstable : (prefixWord ++ tailWord_2149686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149686).length < 2 ^ (prefixWord ++ tailWord_2149686).sum := by decide
  have hdescent : baseEnd_2149686 < baseStart_2149686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149697 : List Nat := [1, 2, 5, 2, 1, 3, 1, 7]
def baseStart_2149697 : Nat := 118140960795 + 2149697 * 2 ^ 59
def prefixEnd_2149697 : Nat := 4983230072969 + 3 ^ 40 * 2149697 * 2
def baseEnd_2149697 : Nat := 81765023890991187726017

theorem tailTrace_2149697 : CollatzResearch.WordTrace tailWord_2149697 prefixEnd_2149697 81765023890991187726017 := by
  unfold tailWord_2149697
  simp only [CollatzResearch.WordTrace]
  refine ⟨78405890893022382863279345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52270593928681588575519563 78405890893022382863279345)
  ·
    refine ⟨58804418169766787147459509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78405890893022382863279345 58804418169766787147459509)
    ·
      refine ⟨5512914203415636295074329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58804418169766787147459509 5512914203415636295074329)
      ·
        refine ⟨4134685652561727221305747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5512914203415636295074329 4134685652561727221305747)
        ·
          refine ⟨6202028478842590831958621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4134685652561727221305747 6202028478842590831958621)
          ·
            refine ⟨2325760679565971561984483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6202028478842590831958621 2325760679565971561984483)
            ·
              refine ⟨3488641019348957342976725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2325760679565971561984483 3488641019348957342976725)
              ·
                refine ⟨81765023890991187726017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3488641019348957342976725 81765023890991187726017)
                ·
                  rfl

theorem cell22_2149697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 7].length) (baseStart_2149697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2149697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2149697 prefixEnd_2149697 := by exact prefixLift 2149697
  have htrace : WordTrace (prefixWord ++ tailWord_2149697) baseStart_2149697 baseEnd_2149697 := by
    simpa [prefixWord, tailWord_2149697, baseEnd_2149697] using wordTrace_append hprefix tailTrace_2149697
  have hstable : (prefixWord ++ tailWord_2149697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149697).length < 2 ^ (prefixWord ++ tailWord_2149697).sum := by decide
  have hdescent : baseEnd_2149697 < baseStart_2149697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149740 : List Nat := [2, 2, 1, 1, 5, 1, 1, 2, 2, 5]
def baseStart_2149740 : Nat := 118140960795 + 2149740 * 2 ^ 59
def prefixEnd_2149740 : Nat := 4983230072969 + 3 ^ 40 * 2149740 * 2
def baseEnd_2149740 : Nat := 735899934797682910709021

theorem tailTrace_2149740 : CollatzResearch.WordTrace tailWord_2149740 prefixEnd_2149740 735899934797682910709021 := by
  unfold tailWord_2149740
  simp only [CollatzResearch.WordTrace]
  refine ⟨39203729615933300603547337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52271639487911067471396449 39203729615933300603547337)
  ·
    refine ⟨29402797211949975452660503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39203729615933300603547337 29402797211949975452660503)
    ·
      refine ⟨44104195817924963178990755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29402797211949975452660503 44104195817924963178990755)
      ·
        refine ⟨66156293726887444768486133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44104195817924963178990755 66156293726887444768486133)
        ·
          refine ⟨6202152536895697947045575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66156293726887444768486133 6202152536895697947045575)
          ·
            refine ⟨9303228805343546920568363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6202152536895697947045575 9303228805343546920568363)
            ·
              refine ⟨13954843208015320380852545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9303228805343546920568363 13954843208015320380852545)
              ·
                refine ⟨10466132406011490285639409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13954843208015320380852545 10466132406011490285639409)
                ·
                  refine ⟨7849599304508617714229557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10466132406011490285639409 7849599304508617714229557)
                  ·
                    refine ⟨735899934797682910709021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7849599304508617714229557 735899934797682910709021)
                    ·
                      rfl

theorem cell22_2149740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_2149740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2149740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2149740 prefixEnd_2149740 := by exact prefixLift 2149740
  have htrace : WordTrace (prefixWord ++ tailWord_2149740) baseStart_2149740 baseEnd_2149740 := by
    simpa [prefixWord, tailWord_2149740, baseEnd_2149740] using wordTrace_append hprefix tailTrace_2149740
  have hstable : (prefixWord ++ tailWord_2149740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149740).length < 2 ^ (prefixWord ++ tailWord_2149740).sum := by decide
  have hdescent : baseEnd_2149740 < baseStart_2149740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149772 : List Nat := [2, 2, 1, 2, 1, 3, 4, 2, 1, 4]
def baseStart_2149772 : Nat := 118140960795 + 2149772 * 2 ^ 59
def prefixEnd_2149772 : Nat := 4983230072969 + 3 ^ 40 * 2149772 * 2
def baseEnd_2149772 : Nat := 735910889051645493908923

theorem tailTrace_2149772 : CollatzResearch.WordTrace tailWord_2149772 prefixEnd_2149772 735910889051645493908923 := by
  unfold tailWord_2149772
  simp only [CollatzResearch.WordTrace]
  refine ⟨39204313183875335336129785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52272417578500447114839713 39204313183875335336129785)
  ·
    refine ⟨29403234887906501502097339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39204313183875335336129785 29403234887906501502097339)
    ·
      refine ⟨44104852331859752253146009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29403234887906501502097339 44104852331859752253146009)
      ·
        refine ⟨33078639248894814189859507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44104852331859752253146009 33078639248894814189859507)
        ·
          refine ⟨49617958873342221284789261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33078639248894814189859507 49617958873342221284789261)
          ·
            refine ⟨18606734577503332981795973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49617958873342221284789261 18606734577503332981795973)
            ·
              refine ⟨3488762733281874934086745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18606734577503332981795973 3488762733281874934086745)
              ·
                refine ⟨2616572049961406200565059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3488762733281874934086745 2616572049961406200565059)
                ·
                  refine ⟨3924858074942109300847589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2616572049961406200565059 3924858074942109300847589)
                  ·
                    refine ⟨735910889051645493908923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3924858074942109300847589 735910889051645493908923)
                    ·
                      rfl

theorem cell22_2149772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 1, 4].length) (baseStart_2149772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2149772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2149772 prefixEnd_2149772 := by exact prefixLift 2149772
  have htrace : WordTrace (prefixWord ++ tailWord_2149772) baseStart_2149772 baseEnd_2149772 := by
    simpa [prefixWord, tailWord_2149772, baseEnd_2149772] using wordTrace_append hprefix tailTrace_2149772
  have hstable : (prefixWord ++ tailWord_2149772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149772).length < 2 ^ (prefixWord ++ tailWord_2149772).sum := by decide
  have hdescent : baseEnd_2149772 < baseStart_2149772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149815 : List Nat := [1, 1, 3, 1, 3, 2, 4, 7]
def baseStart_2149815 : Nat := 118140960795 + 2149815 * 2 ^ 59
def prefixEnd_2149815 : Nat := 4983230072969 + 3 ^ 40 * 2149815 * 2
def baseEnd_2149815 : Nat := 81769512092267523898199

theorem tailTrace_2149815 : CollatzResearch.WordTrace tailWord_2149815 prefixEnd_2149815 81769512092267523898199 := by
  unfold tailWord_2149815
  simp only [CollatzResearch.WordTrace]
  refine ⟨78410194706594889016074899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52273463137729926010716599 78410194706594889016074899)
  ·
    refine ⟨117615292059892333524112349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78410194706594889016074899 117615292059892333524112349)
    ·
      refine ⟨44105734522459625071542131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117615292059892333524112349 44105734522459625071542131)
      ·
        refine ⟨66158601783689437607313197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44105734522459625071542131 66158601783689437607313197)
        ·
          refine ⟨24809475668883539102742449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66158601783689437607313197 24809475668883539102742449)
          ·
            refine ⟨18607106751662654327056837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24809475668883539102742449 18607106751662654327056837)
            ·
              refine ⟨3488832515936747686323157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18607106751662654327056837 3488832515936747686323157)
              ·
                refine ⟨81769512092267523898199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3488832515936747686323157 81769512092267523898199)
                ·
                  rfl

theorem cell22_2149815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 7].length) (baseStart_2149815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2149815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2149815 prefixEnd_2149815 := by exact prefixLift 2149815
  have htrace : WordTrace (prefixWord ++ tailWord_2149815) baseStart_2149815 baseEnd_2149815 := by
    simpa [prefixWord, tailWord_2149815, baseEnd_2149815] using wordTrace_append hprefix tailTrace_2149815
  have hstable : (prefixWord ++ tailWord_2149815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149815).length < 2 ^ (prefixWord ++ tailWord_2149815).sum := by decide
  have hdescent : baseEnd_2149815 < baseStart_2149815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149860 : List Nat := [2, 3, 1, 1, 1, 1, 1, 5, 7]
def baseStart_2149860 : Nat := 118140960795 + 2149860 * 2 ^ 59
def prefixEnd_2149860 : Nat := 4983230072969 + 3 ^ 40 * 2149860 * 2
def baseEnd_2149860 : Nat := 245313671083347532569551

theorem tailTrace_2149860 : CollatzResearch.WordTrace tailWord_2149860 prefixEnd_2149860 245313671083347532569551 := by
  unfold tailWord_2149860
  simp only [CollatzResearch.WordTrace]
  refine ⟨39205917995715930850731517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52274557327621241134308689 39205917995715930850731517)
  ·
    refine ⟨14702219248393474069024319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39205917995715930850731517 14702219248393474069024319)
    ·
      refine ⟨22053328872590211103536479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14702219248393474069024319 22053328872590211103536479)
      ·
        refine ⟨33079993308885316655304719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22053328872590211103536479 33079993308885316655304719)
        ·
          refine ⟨49619989963327974982957079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33079993308885316655304719 49619989963327974982957079)
          ·
            refine ⟨74429984944991962474435619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49619989963327974982957079 74429984944991962474435619)
            ·
              refine ⟨111644977417487943711653429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74429984944991962474435619 111644977417487943711653429)
              ·
                refine ⟨10466716632889494722967509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 111644977417487943711653429 10466716632889494722967509)
                ·
                  refine ⟨245313671083347532569551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10466716632889494722967509 245313671083347532569551)
                  ·
                    rfl

theorem cell22_2149860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_2149860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2149860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2149860 prefixEnd_2149860 := by exact prefixLift 2149860
  have htrace : WordTrace (prefixWord ++ tailWord_2149860) baseStart_2149860 baseEnd_2149860 := by
    simpa [prefixWord, tailWord_2149860, baseEnd_2149860] using wordTrace_append hprefix tailTrace_2149860
  have hstable : (prefixWord ++ tailWord_2149860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149860).length < 2 ^ (prefixWord ++ tailWord_2149860).sum := by decide
  have hdescent : baseEnd_2149860 < baseStart_2149860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149905 : List Nat := [1, 2, 2, 1, 1, 2, 3, 2, 8]
def baseStart_2149905 : Nat := 118140960795 + 2149905 * 2 ^ 59
def prefixEnd_2149905 : Nat := 4983230072969 + 3 ^ 40 * 2149905 * 2
def baseEnd_2149905 : Nat := 245318805889892493444505

theorem tailTrace_2149905 : CollatzResearch.WordTrace tailWord_2149905 prefixEnd_2149905 245318805889892493444505 := by
  unfold tailWord_2149905
  simp only [CollatzResearch.WordTrace]
  refine ⟨78413477276268834386851169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52275651517512556257900779 78413477276268834386851169)
  ·
    refine ⟨58810107957201625790138377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78413477276268834386851169 58810107957201625790138377)
    ·
      refine ⟨44107580967901219342603783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58810107957201625790138377 44107580967901219342603783)
      ·
        refine ⟨66161371451851829013905675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44107580967901219342603783 66161371451851829013905675)
        ·
          refine ⟨99242057177777743520858513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66161371451851829013905675 99242057177777743520858513)
          ·
            refine ⟨74431542883333307640643885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99242057177777743520858513 74431542883333307640643885)
            ·
              refine ⟨27911828581249990365241457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74431542883333307640643885 27911828581249990365241457)
              ·
                refine ⟨20933871435937492773931093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27911828581249990365241457 20933871435937492773931093)
                ·
                  refine ⟨245318805889892493444505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20933871435937492773931093 245318805889892493444505)
                  ·
                    rfl

theorem cell22_2149905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 8].length) (baseStart_2149905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2149905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2149905 prefixEnd_2149905 := by exact prefixLift 2149905
  have htrace : WordTrace (prefixWord ++ tailWord_2149905) baseStart_2149905 baseEnd_2149905 := by
    simpa [prefixWord, tailWord_2149905, baseEnd_2149905] using wordTrace_append hprefix tailTrace_2149905
  have hstable : (prefixWord ++ tailWord_2149905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149905).length < 2 ^ (prefixWord ++ tailWord_2149905).sum := by decide
  have hdescent : baseEnd_2149905 < baseStart_2149905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149922 : List Nat := [3, 3, 1, 1, 1, 1, 3, 3, 6]
def baseStart_2149922 : Nat := 118140960795 + 2149922 * 2 ^ 59
def prefixEnd_2149922 : Nat := 4983230072969 + 3 ^ 40 * 2149922 * 2
def baseEnd_2149922 : Nat := 245320745705698367552821

theorem tailTrace_2149922 : CollatzResearch.WordTrace tailWord_2149922 prefixEnd_2149922 245320745705698367552821 := by
  unfold tailWord_2149922
  simp only [CollatzResearch.WordTrace]
  refine ⟨19603524329301811572555005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52276064878138164193480013 19603524329301811572555005)
  ·
    refine ⟨7351321623488179339708127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19603524329301811572555005 7351321623488179339708127)
    ·
      refine ⟨11026982435232269009562191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7351321623488179339708127 11026982435232269009562191)
      ·
        refine ⟨16540473652848403514343287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11026982435232269009562191 16540473652848403514343287)
        ·
          refine ⟨24810710479272605271514931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16540473652848403514343287 24810710479272605271514931)
          ·
            refine ⟨37216065718908907907272397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24810710479272605271514931 37216065718908907907272397)
            ·
              refine ⟨13956024644590840465227149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37216065718908907907272397 13956024644590840465227149)
              ·
                refine ⟨5233509241721565174460181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13956024644590840465227149 5233509241721565174460181)
                ·
                  refine ⟨245320745705698367552821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5233509241721565174460181 245320745705698367552821)
                  ·
                    rfl

theorem cell22_2149922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_2149922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2149922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2149922 prefixEnd_2149922 := by exact prefixLift 2149922
  have htrace : WordTrace (prefixWord ++ tailWord_2149922) baseStart_2149922 baseEnd_2149922 := by
    simpa [prefixWord, tailWord_2149922, baseEnd_2149922] using wordTrace_append hprefix tailTrace_2149922
  have hstable : (prefixWord ++ tailWord_2149922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149922).length < 2 ^ (prefixWord ++ tailWord_2149922).sum := by decide
  have hdescent : baseEnd_2149922 < baseStart_2149922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149952 : List Nat := [2, 1, 1, 2, 2, 2, 1, 5, 2, 4]
def baseStart_2149952 : Nat := 118140960795 + 2149952 * 2 ^ 59
def prefixEnd_2149952 : Nat := 4983230072969 + 3 ^ 40 * 2149952 * 2
def baseEnd_2149952 : Nat := 735972506730185024408371

theorem tailTrace_2149952 : CollatzResearch.WordTrace tailWord_2149952 prefixEnd_2149952 735972506730185024408371 := by
  unfold tailWord_2149952
  simp only [CollatzResearch.WordTrace]
  refine ⟨39207595753549280706906055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52276794338065707609208073 39207595753549280706906055)
  ·
    refine ⟨58811393630323921060359083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39207595753549280706906055 58811393630323921060359083)
    ·
      refine ⟨88217090445485881590538625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58811393630323921060359083 88217090445485881590538625)
      ·
        refine ⟨66162817834114411192903969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88217090445485881590538625 66162817834114411192903969)
        ·
          refine ⟨49622113375585808394677977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66162817834114411192903969 49622113375585808394677977)
          ·
            refine ⟨37216585031689356296008483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49622113375585808394677977 37216585031689356296008483)
            ·
              refine ⟨55824877547534034444012725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37216585031689356296008483 55824877547534034444012725)
              ·
                refine ⟨5233582270081315729126193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55824877547534034444012725 5233582270081315729126193)
                ·
                  refine ⟨3925186702560986796844645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5233582270081315729126193 3925186702560986796844645)
                  ·
                    refine ⟨735972506730185024408371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3925186702560986796844645 735972506730185024408371)
                    ·
                      rfl

theorem cell22_2149952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 2, 4].length) (baseStart_2149952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2149952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2149952 prefixEnd_2149952 := by exact prefixLift 2149952
  have htrace : WordTrace (prefixWord ++ tailWord_2149952) baseStart_2149952 baseEnd_2149952 := by
    simpa [prefixWord, tailWord_2149952, baseEnd_2149952] using wordTrace_append hprefix tailTrace_2149952
  have hstable : (prefixWord ++ tailWord_2149952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149952).length < 2 ^ (prefixWord ++ tailWord_2149952).sum := by decide
  have hdescent : baseEnd_2149952 < baseStart_2149952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149988 : List Nat := [2, 3, 1, 1, 2, 5, 2, 1, 2, 3]
def baseStart_2149988 : Nat := 118140960795 + 2149988 * 2 ^ 59
def prefixEnd_2149988 : Nat := 4983230072969 + 3 ^ 40 * 2149988 * 2
def baseEnd_2149988 : Nat := 735984830265892930508261

theorem tailTrace_2149988 : CollatzResearch.WordTrace tailWord_2149988 prefixEnd_2149988 735984830265892930508261 := by
  unfold tailWord_2149988
  simp only [CollatzResearch.WordTrace]
  refine ⟨39208252267484069781061309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52277669689978759708081745 39208252267484069781061309)
  ·
    refine ⟨14703094600306526167897991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39208252267484069781061309 14703094600306526167897991)
    ·
      refine ⟨22054641900459789251846987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14703094600306526167897991 22054641900459789251846987)
      ·
        refine ⟨33081962850689683877770481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22054641900459789251846987 33081962850689683877770481)
        ·
          refine ⟨24811472138017262908327861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33081962850689683877770481 24811472138017262908327861)
          ·
            refine ⟨2326075512939118397655737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24811472138017262908327861 2326075512939118397655737)
            ·
              refine ⟨1744556634704338798241803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2326075512939118397655737 1744556634704338798241803)
              ·
                refine ⟨2616834952056508197362705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1744556634704338798241803 2616834952056508197362705)
                ·
                  refine ⟨1962626214042381148022029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2616834952056508197362705 1962626214042381148022029)
                  ·
                    refine ⟨735984830265892930508261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1962626214042381148022029 735984830265892930508261)
                    ·
                      rfl

theorem cell22_2149988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 2, 3].length) (baseStart_2149988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2149988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2149988 prefixEnd_2149988 := by exact prefixLift 2149988
  have htrace : WordTrace (prefixWord ++ tailWord_2149988) baseStart_2149988 baseEnd_2149988 := by
    simpa [prefixWord, tailWord_2149988, baseEnd_2149988] using wordTrace_append hprefix tailTrace_2149988
  have hstable : (prefixWord ++ tailWord_2149988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149988).length < 2 ^ (prefixWord ++ tailWord_2149988).sum := by decide
  have hdescent : baseEnd_2149988 < baseStart_2149988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150016 : List Nat := [2, 1, 1, 2, 1, 4, 2, 5, 1, 3]
def baseStart_2150016 : Nat := 118140960795 + 2150016 * 2 ^ 59
def prefixEnd_2150016 : Nat := 4983230072969 + 3 ^ 40 * 2150016 * 2
def baseEnd_2150016 : Nat := 735994415238110190808175

theorem tailTrace_2150016 : CollatzResearch.WordTrace tailWord_2150016 prefixEnd_2150016 735994415238110190808175 := by
  unfold tailWord_2150016
  simp only [CollatzResearch.WordTrace]
  refine ⟨39208762889433350172070951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52278350519244466896094601 39208762889433350172070951)
  ·
    refine ⟨58813144334150025258106427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39208762889433350172070951 58813144334150025258106427)
    ·
      refine ⟨88219716501225037887159641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58813144334150025258106427 88219716501225037887159641)
      ·
        refine ⟨66164787375918778415369731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88219716501225037887159641 66164787375918778415369731)
        ·
          refine ⟨99247181063878167623054597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66164787375918778415369731 99247181063878167623054597)
          ·
            refine ⟨18608846449477156429322737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99247181063878167623054597 18608846449477156429322737)
            ·
              refine ⟨13956634837107867321992053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18608846449477156429322737 13956634837107867321992053)
              ·
                refine ⟨1308434515978862561436755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13956634837107867321992053 1308434515978862561436755)
                ·
                  refine ⟨1962651773968293842155133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1308434515978862561436755 1962651773968293842155133)
                  ·
                    refine ⟨735994415238110190808175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1962651773968293842155133 735994415238110190808175)
                    ·
                      rfl

theorem cell22_2150016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 5, 1, 3].length) (baseStart_2150016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2150016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2150016 prefixEnd_2150016 := by exact prefixLift 2150016
  have htrace : WordTrace (prefixWord ++ tailWord_2150016) baseStart_2150016 baseEnd_2150016 := by
    simpa [prefixWord, tailWord_2150016, baseEnd_2150016] using wordTrace_append hprefix tailTrace_2150016
  have hstable : (prefixWord ++ tailWord_2150016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150016).length < 2 ^ (prefixWord ++ tailWord_2150016).sum := by decide
  have hdescent : baseEnd_2150016 < baseStart_2150016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150027 : List Nat := [1, 1, 1, 1, 4, 1, 4, 2, 2, 5]
def baseStart_2150027 : Nat := 118140960795 + 2150027 * 2 ^ 59
def prefixEnd_2150027 : Nat := 4983230072969 + 3 ^ 40 * 2150027 * 2
def baseEnd_2150027 : Nat := 735998180762909828783141

theorem tailTrace_2150027 : CollatzResearch.WordTrace tailWord_2150027 prefixEnd_2150027 735998180762909828783141 := by
  unfold tailWord_2150027
  simp only [CollatzResearch.WordTrace]
  refine ⟨78417926981826849222792335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52278617987884566148528223 78417926981826849222792335)
  ·
    refine ⟨117626890472740273834188503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78417926981826849222792335 117626890472740273834188503)
    ·
      refine ⟨176440335709110410751282755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117626890472740273834188503 176440335709110410751282755)
      ·
        refine ⟨264660503563665616126924133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176440335709110410751282755 264660503563665616126924133)
        ·
          refine ⟨49623844418187303023798275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 264660503563665616126924133 49623844418187303023798275)
          ·
            refine ⟨74435766627280954535697413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49623844418187303023798275 74435766627280954535697413)
            ·
              refine ⟨13956706242615178975443265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74435766627280954535697413 13956706242615178975443265)
              ·
                refine ⟨10467529681961384231582449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13956706242615178975443265 10467529681961384231582449)
                ·
                  refine ⟨7850647261471038173686837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10467529681961384231582449 7850647261471038173686837)
                  ·
                    refine ⟨735998180762909828783141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7850647261471038173686837 735998180762909828783141)
                    ·
                      rfl

theorem cell22_2150027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 5].length) (baseStart_2150027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2150027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2150027 prefixEnd_2150027 := by exact prefixLift 2150027
  have htrace : WordTrace (prefixWord ++ tailWord_2150027) baseStart_2150027 baseEnd_2150027 := by
    simpa [prefixWord, tailWord_2150027, baseEnd_2150027] using wordTrace_append hprefix tailTrace_2150027
  have hstable : (prefixWord ++ tailWord_2150027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150027).length < 2 ^ (prefixWord ++ tailWord_2150027).sum := by decide
  have hdescent : baseEnd_2150027 < baseStart_2150027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150046 : List Nat := [4, 3, 1, 1, 1, 2, 2, 3, 5]
def baseStart_2150046 : Nat := 118140960795 + 2150046 * 2 ^ 59
def prefixEnd_2150046 : Nat := 4983230072969 + 3 ^ 40 * 2150046 * 2
def baseEnd_2150046 : Nat := 245334894950400037519361

theorem tailTrace_2150046 : CollatzResearch.WordTrace tailWord_2150046 prefixEnd_2150046 245334894950400037519361 := by
  unfold tailWord_2150046
  simp only [CollatzResearch.WordTrace]
  refine ⟨9802327496094751933466749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52279079979172010311822661 9802327496094751933466749)
  ·
    refine ⟨3675872811035531975050031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9802327496094751933466749 3675872811035531975050031)
    ·
      refine ⟨5513809216553297962575047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3675872811035531975050031 5513809216553297962575047)
      ·
        refine ⟨8270713824829946943862571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5513809216553297962575047 8270713824829946943862571)
        ·
          refine ⟨12406070737244920415793857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8270713824829946943862571 12406070737244920415793857)
          ·
            refine ⟨9304553052933690311845393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12406070737244920415793857 9304553052933690311845393)
            ·
              refine ⟨6978414789700267733884045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9304553052933690311845393 6978414789700267733884045)
              ·
                refine ⟨2616905546137600400206517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6978414789700267733884045 2616905546137600400206517)
                ·
                  refine ⟨245334894950400037519361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2616905546137600400206517 245334894950400037519361)
                  ·
                    rfl

theorem cell22_2150046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_2150046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2150046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2150046 prefixEnd_2150046 := by exact prefixLift 2150046
  have htrace : WordTrace (prefixWord ++ tailWord_2150046) baseStart_2150046 baseEnd_2150046 := by
    simpa [prefixWord, tailWord_2150046, baseEnd_2150046] using wordTrace_append hprefix tailTrace_2150046
  have hstable : (prefixWord ++ tailWord_2150046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150046).length < 2 ^ (prefixWord ++ tailWord_2150046).sum := by decide
  have hdescent : baseEnd_2150046 < baseStart_2150046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150076 : List Nat := [2, 2, 2, 3, 1, 3, 1, 3, 1, 4]
def baseStart_2150076 : Nat := 118140960795 + 2150076 * 2 ^ 59
def prefixEnd_2150076 : Nat := 4983230072969 + 3 ^ 40 * 2150076 * 2
def baseEnd_2150076 : Nat := 736014954464290034307991

theorem tailTrace_2150076 : CollatzResearch.WordTrace tailWord_2150076 prefixEnd_2150076 736014954464290034307991 := by
  unfold tailWord_2150076
  simp only [CollatzResearch.WordTrace]
  refine ⟨39209857079324665295663041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52279809439099553727550721 39209857079324665295663041)
  ·
    refine ⟨29407392809493498971747281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39209857079324665295663041 29407392809493498971747281)
    ·
      refine ⟨22055544607120124228810461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29407392809493498971747281 22055544607120124228810461)
      ·
        refine ⟨8270829227670046585803923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22055544607120124228810461 8270829227670046585803923)
        ·
          refine ⟨12406243841505069878705885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8270829227670046585803923 12406243841505069878705885)
          ·
            refine ⟨4652341440564401204514707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12406243841505069878705885 4652341440564401204514707)
            ·
              refine ⟨6978512160846601806772061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4652341440564401204514707 6978512160846601806772061)
              ·
                refine ⟨2616942060317475677539523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6978512160846601806772061 2616942060317475677539523)
                ·
                  refine ⟨3925413090476213516309285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2616942060317475677539523 3925413090476213516309285)
                  ·
                    refine ⟨736014954464290034307991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3925413090476213516309285 736014954464290034307991)
                    ·
                      rfl

theorem cell22_2150076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_2150076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2150076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2150076 prefixEnd_2150076 := by exact prefixLift 2150076
  have htrace : WordTrace (prefixWord ++ tailWord_2150076) baseStart_2150076 baseEnd_2150076 := by
    simpa [prefixWord, tailWord_2150076, baseEnd_2150076] using wordTrace_append hprefix tailTrace_2150076
  have hstable : (prefixWord ++ tailWord_2150076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150076).length < 2 ^ (prefixWord ++ tailWord_2150076).sum := by decide
  have hdescent : baseEnd_2150076 < baseStart_2150076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150106 : List Nat := [3, 1, 1, 2, 2, 5, 1, 1, 1, 5]
def baseStart_2150106 : Nat := 118140960795 + 2150106 * 2 ^ 59
def prefixEnd_2150106 : Nat := 4983230072969 + 3 ^ 40 * 2150106 * 2
def baseEnd_2150106 : Nat := 736025224077379956057899

theorem tailTrace_2150106 : CollatzResearch.WordTrace tailWord_2150106 prefixEnd_2150106 736025224077379956057899 := by
  unfold tailWord_2150106
  simp only [CollatzResearch.WordTrace]
  refine ⟨19605202087135161428729543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52280538899027097143278781 19605202087135161428729543)
  ·
    refine ⟨29407803130702742143094315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19605202087135161428729543 29407803130702742143094315)
    ·
      refine ⟨44111704696054113214641473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29407803130702742143094315 44111704696054113214641473)
      ·
        refine ⟨33083778522040584910981105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44111704696054113214641473 33083778522040584910981105)
        ·
          refine ⟨24812833891530438683235829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33083778522040584910981105 24812833891530438683235829)
          ·
            refine ⟨2326203177330978626553359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24812833891530438683235829 2326203177330978626553359)
            ·
              refine ⟨3489304765996467939830039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2326203177330978626553359 3489304765996467939830039)
              ·
                refine ⟨5233957148994701909745059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3489304765996467939830039 5233957148994701909745059)
                ·
                  refine ⟨7850935723492052864617589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5233957148994701909745059 7850935723492052864617589)
                  ·
                    refine ⟨736025224077379956057899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7850935723492052864617589 736025224077379956057899)
                    ·
                      rfl

theorem cell22_2150106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 1, 5].length) (baseStart_2150106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2150106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2150106 prefixEnd_2150106 := by exact prefixLift 2150106
  have htrace : WordTrace (prefixWord ++ tailWord_2150106) baseStart_2150106 baseEnd_2150106 := by
    simpa [prefixWord, tailWord_2150106, baseEnd_2150106] using wordTrace_append hprefix tailTrace_2150106
  have hstable : (prefixWord ++ tailWord_2150106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150106).length < 2 ^ (prefixWord ++ tailWord_2150106).sum := by decide
  have hdescent : baseEnd_2150106 < baseStart_2150106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150198 : List Nat := [5, 1, 2, 2, 1, 1, 1, 4, 5]
def baseStart_2150198 : Nat := 118140960795 + 2150198 * 2 ^ 59
def prefixEnd_2150198 : Nat := 4983230072969 + 3 ^ 40 * 2150198 * 2
def baseEnd_2150198 : Nat := 245352239185840794252539

theorem tailTrace_2150198 : CollatzResearch.WordTrace tailWord_2150198 prefixEnd_2150198 245352239185840794252539 := by
  unfold tailWord_2150198
  simp only [CollatzResearch.WordTrace]
  refine ⟨4901510241512959089204203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52282775909471563618178165 4901510241512959089204203)
  ·
    refine ⟨7352265362269438633806305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4901510241512959089204203 7352265362269438633806305)
    ·
      refine ⟨5514199021702078975354729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7352265362269438633806305 5514199021702078975354729)
      ·
        refine ⟨4135649266276559231516047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5514199021702078975354729 4135649266276559231516047)
        ·
          refine ⟨6203473899414838847274071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4135649266276559231516047 6203473899414838847274071)
          ·
            refine ⟨9305210849122258270911107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6203473899414838847274071 9305210849122258270911107)
            ·
              refine ⟨13957816273683387406366661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9305210849122258270911107 13957816273683387406366661)
              ·
                refine ⟨2617090551315635138693749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13957816273683387406366661 2617090551315635138693749)
                ·
                  refine ⟨245352239185840794252539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2617090551315635138693749 245352239185840794252539)
                  ·
                    rfl

theorem cell22_2150198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_2150198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2150198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2150198 prefixEnd_2150198 := by exact prefixLift 2150198
  have htrace : WordTrace (prefixWord ++ tailWord_2150198) baseStart_2150198 baseEnd_2150198 := by
    simpa [prefixWord, tailWord_2150198, baseEnd_2150198] using wordTrace_append hprefix tailTrace_2150198
  have hstable : (prefixWord ++ tailWord_2150198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150198).length < 2 ^ (prefixWord ++ tailWord_2150198).sum := by decide
  have hdescent : baseEnd_2150198 < baseStart_2150198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150202 : List Nat := [3, 1, 1, 1, 5, 3, 2, 2, 1, 3]
def baseStart_2150202 : Nat := 118140960795 + 2150202 * 2 ^ 59
def prefixEnd_2150202 : Nat := 4983230072969 + 3 ^ 40 * 2150202 * 2
def baseEnd_2150202 : Nat := 736058086839267705657605

theorem tailTrace_2150202 : CollatzResearch.WordTrace tailWord_2150202 prefixEnd_2150202 736058086839267705657605 := by
  unfold tailWord_2150202
  simp only [CollatzResearch.WordTrace]
  refine ⟨19606077439048213527603215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52282873170795236073608573 19606077439048213527603215)
  ·
    refine ⟨29409116158572320291404823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19606077439048213527603215 29409116158572320291404823)
    ·
      refine ⟨44113674237858480437107235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29409116158572320291404823 44113674237858480437107235)
      ·
        refine ⟨66170511356787720655660853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44113674237858480437107235 66170511356787720655660853)
        ·
          refine ⟨6203485439698848811468205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66170511356787720655660853 6203485439698848811468205)
          ·
            refine ⟨2326307039887068304300577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6203485439698848811468205 2326307039887068304300577)
            ·
              refine ⟨1744730279915301228225433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2326307039887068304300577 1744730279915301228225433)
              ·
                refine ⟨1308547709936475921169075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1744730279915301228225433 1308547709936475921169075)
                ·
                  refine ⟨1962821564904713881753613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1308547709936475921169075 1962821564904713881753613)
                  ·
                    refine ⟨736058086839267705657605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1962821564904713881753613 736058086839267705657605)
                    ·
                      rfl

theorem cell22_2150202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 2, 1, 3].length) (baseStart_2150202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2150202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2150202 prefixEnd_2150202 := by exact prefixLift 2150202
  have htrace : WordTrace (prefixWord ++ tailWord_2150202) baseStart_2150202 baseEnd_2150202 := by
    simpa [prefixWord, tailWord_2150202, baseEnd_2150202] using wordTrace_append hprefix tailTrace_2150202
  have hstable : (prefixWord ++ tailWord_2150202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150202).length < 2 ^ (prefixWord ++ tailWord_2150202).sum := by decide
  have hdescent : baseEnd_2150202 < baseStart_2150202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150226 : List Nat := [3, 2, 2, 1, 1, 4, 1, 2, 6]
def baseStart_2150226 : Nat := 118140960795 + 2150226 * 2 ^ 59
def prefixEnd_2150226 : Nat := 4983230072969 + 3 ^ 40 * 2150226 * 2
def baseEnd_2150226 : Nat := 245355434176579881019177

theorem tailTrace_2150226 : CollatzResearch.WordTrace tailWord_2150226 prefixEnd_2150226 245355434176579881019177 := by
  unfold tailWord_2150226
  simp only [CollatzResearch.WordTrace]
  refine ⟨19606296277026476552321633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52283456738737270806191021 19606296277026476552321633)
  ·
    refine ⟨14704722207769857414241225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19606296277026476552321633 14704722207769857414241225)
    ·
      refine ⟨11028541655827393060680919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14704722207769857414241225 11028541655827393060680919)
      ·
        refine ⟨16542812483741089591021379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11028541655827393060680919 16542812483741089591021379)
        ·
          refine ⟨24814218725611634386532069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16542812483741089591021379 24814218725611634386532069)
          ·
            refine ⟨4652666011052181447474763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24814218725611634386532069 4652666011052181447474763)
            ·
              refine ⟨6978999016578272171212145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4652666011052181447474763 6978999016578272171212145)
              ·
                refine ⟨5234249262433704128409109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6978999016578272171212145 5234249262433704128409109)
                ·
                  refine ⟨245355434176579881019177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5234249262433704128409109 245355434176579881019177)
                  ·
                    rfl

theorem cell22_2150226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_2150226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2150226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2150226 prefixEnd_2150226 := by exact prefixLift 2150226
  have htrace : WordTrace (prefixWord ++ tailWord_2150226) baseStart_2150226 baseEnd_2150226 := by
    simpa [prefixWord, tailWord_2150226, baseEnd_2150226] using wordTrace_append hprefix tailTrace_2150226
  have hstable : (prefixWord ++ tailWord_2150226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150226).length < 2 ^ (prefixWord ++ tailWord_2150226).sum := by decide
  have hdescent : baseEnd_2150226 < baseStart_2150226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150241 : List Nat := [1, 2, 3, 1, 1, 1, 4, 2, 4, 3]
def baseStart_2150241 : Nat := 118140960795 + 2150241 * 2 ^ 59
def prefixEnd_2150241 : Nat := 4983230072969 + 3 ^ 40 * 2150241 * 2
def baseEnd_2150241 : Nat := 736071437336284603932485

theorem tailTrace_2150241 : CollatzResearch.WordTrace tailWord_2150241 prefixEnd_2150241 736071437336284603932485 := by
  unfold tailWord_2150241
  simp only [CollatzResearch.WordTrace]
  refine ⟨78425732203051563771082577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52283821468701042514055051 78425732203051563771082577)
  ·
    refine ⟨58819299152288672828311933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78425732203051563771082577 58819299152288672828311933)
    ·
      refine ⟨22057237182108252310616975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58819299152288672828311933 22057237182108252310616975)
      ·
        refine ⟨33085855773162378465925463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22057237182108252310616975 33085855773162378465925463)
        ·
          refine ⟨49628783659743567698888195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33085855773162378465925463 49628783659743567698888195)
          ·
            refine ⟨74443175489615351548332293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49628783659743567698888195 74443175489615351548332293)
            ·
              refine ⟨13958095404302878415312305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74443175489615351548332293 13958095404302878415312305)
              ·
                refine ⟨10468571553227158811484229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13958095404302878415312305 10468571553227158811484229)
                ·
                  refine ⟨1962857166230092277153293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10468571553227158811484229 1962857166230092277153293)
                  ·
                    refine ⟨736071437336284603932485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1962857166230092277153293 736071437336284603932485)
                    ·
                      rfl

theorem cell22_2150241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_2150241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2150241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2150241 prefixEnd_2150241 := by exact prefixLift 2150241
  have htrace : WordTrace (prefixWord ++ tailWord_2150241) baseStart_2150241 baseEnd_2150241 := by
    simpa [prefixWord, tailWord_2150241, baseEnd_2150241] using wordTrace_append hprefix tailTrace_2150241
  have hstable : (prefixWord ++ tailWord_2150241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150241).length < 2 ^ (prefixWord ++ tailWord_2150241).sum := by decide
  have hdescent : baseEnd_2150241 < baseStart_2150241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150275 : List Nat := [1, 1, 1, 3, 4, 3, 3, 1, 2, 3]
def baseStart_2150275 : Nat := 118140960795 + 2150275 * 2 ^ 59
def prefixEnd_2150275 : Nat := 4983230072969 + 3 ^ 40 * 2150275 * 2
def baseEnd_2150275 : Nat := 736083076231119848582381

theorem tailTrace_2150275 : CollatzResearch.WordTrace tailWord_2150275 prefixEnd_2150275 736083076231119848582381 := by
  unfold tailWord_2150275
  simp only [CollatzResearch.WordTrace]
  refine ⟨78426972284928387577820279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52284648189952258385213519 78426972284928387577820279)
  ·
    refine ⟨117640458427392581366730419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78426972284928387577820279 117640458427392581366730419)
    ·
      refine ⟨176460687641088872050095629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117640458427392581366730419 176460687641088872050095629)
      ·
        refine ⟨66172757865408327018785861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176460687641088872050095629 66172757865408327018785861)
        ·
          refine ⟨12407392099764061316022349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66172757865408327018785861 12407392099764061316022349)
          ·
            refine ⟨4652772037411522993508381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12407392099764061316022349 4652772037411522993508381)
            ·
              refine ⟨1744789514029321122565643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4652772037411522993508381 1744789514029321122565643)
              ·
                refine ⟨2617184271043981683848465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1744789514029321122565643 2617184271043981683848465)
                ·
                  refine ⟨1962888203282986262886349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2617184271043981683848465 1962888203282986262886349)
                  ·
                    refine ⟨736083076231119848582381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1962888203282986262886349 736083076231119848582381)
                    ·
                      rfl

theorem cell22_2150275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 2, 3].length) (baseStart_2150275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2150275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2150275 prefixEnd_2150275 := by exact prefixLift 2150275
  have htrace : WordTrace (prefixWord ++ tailWord_2150275) baseStart_2150275 baseEnd_2150275 := by
    simpa [prefixWord, tailWord_2150275, baseEnd_2150275] using wordTrace_append hprefix tailTrace_2150275
  have hstable : (prefixWord ++ tailWord_2150275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150275).length < 2 ^ (prefixWord ++ tailWord_2150275).sum := by decide
  have hdescent : baseEnd_2150275 < baseStart_2150275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150333 : List Nat := [1, 4, 1, 2, 3, 2, 1, 3, 5]
def baseStart_2150333 : Nat := 118140960795 + 2150333 * 2 ^ 59
def prefixEnd_2150333 : Nat := 4983230072969 + 3 ^ 40 * 2150333 * 2
def baseEnd_2150333 : Nat := 245367643605475676877401

theorem tailTrace_2150333 : CollatzResearch.WordTrace tailWord_2150333 prefixEnd_2150333 245367643605475676877401 := by
  unfold tailWord_2150333
  simp only [CollatzResearch.WordTrace]
  refine ⟨78429087718718263483431653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52286058479145508988954435 78429087718718263483431653)
  ·
    refine ⟨14705453947259674403143435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78429087718718263483431653 14705453947259674403143435)
    ·
      refine ⟨22058180920889511604715153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14705453947259674403143435 22058180920889511604715153)
      ·
        refine ⟨16543635690667133703536365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22058180920889511604715153 16543635690667133703536365)
        ·
          refine ⟨6203863384000175138826137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16543635690667133703536365 6203863384000175138826137)
          ·
            refine ⟨4652897538000131354119603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6203863384000175138826137 4652897538000131354119603)
            ·
              refine ⟨6979346307000197031179405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4652897538000131354119603 6979346307000197031179405)
              ·
                refine ⟨2617254865125073886692277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6979346307000197031179405 2617254865125073886692277)
                ·
                  refine ⟨245367643605475676877401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2617254865125073886692277 245367643605475676877401)
                  ·
                    rfl

theorem cell22_2150333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_2150333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2150333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2150333 prefixEnd_2150333 := by exact prefixLift 2150333
  have htrace : WordTrace (prefixWord ++ tailWord_2150333) baseStart_2150333 baseEnd_2150333 := by
    simpa [prefixWord, tailWord_2150333, baseEnd_2150333] using wordTrace_append hprefix tailTrace_2150333
  have hstable : (prefixWord ++ tailWord_2150333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150333).length < 2 ^ (prefixWord ++ tailWord_2150333).sum := by decide
  have hdescent : baseEnd_2150333 < baseStart_2150333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150376 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 5, 5]
def baseStart_2150376 : Nat := 118140960795 + 2150376 * 2 ^ 59
def prefixEnd_2150376 : Nat := 4983230072969 + 3 ^ 40 * 2150376 * 2
def baseEnd_2150376 : Nat := 736117650595189251807071

theorem tailTrace_2150376 : CollatzResearch.WordTrace tailWord_2150376 prefixEnd_2150376 736117650595189251807071 := by
  unfold tailWord_2150376
  simp only [CollatzResearch.WordTrace]
  refine ⟨39215328028781240913623491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52287104038374987884831321 39215328028781240913623491)
  ·
    refine ⟨58822992043171861370435237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39215328028781240913623491 58822992043171861370435237)
    ·
      refine ⟨11029311008094724006956607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58822992043171861370435237 11029311008094724006956607)
      ·
        refine ⟨16543966512142086010434911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11029311008094724006956607 16543966512142086010434911)
        ·
          refine ⟨24815949768213129015652367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16543966512142086010434911 24815949768213129015652367)
          ·
            refine ⟨37223924652319693523478551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24815949768213129015652367 37223924652319693523478551)
            ·
              refine ⟨55835886978479540285217827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37223924652319693523478551 55835886978479540285217827)
              ·
                refine ⟨83753830467719310427826741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55835886978479540285217827 83753830467719310427826741)
                ·
                  refine ⟨7851921606348685352608757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 83753830467719310427826741 7851921606348685352608757)
                  ·
                    refine ⟨736117650595189251807071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7851921606348685352608757 736117650595189251807071)
                    ·
                      rfl

theorem cell22_2150376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_2150376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2150376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2150376 prefixEnd_2150376 := by exact prefixLift 2150376
  have htrace : WordTrace (prefixWord ++ tailWord_2150376) baseStart_2150376 baseEnd_2150376 := by
    simpa [prefixWord, tailWord_2150376, baseEnd_2150376] using wordTrace_append hprefix tailTrace_2150376
  have hstable : (prefixWord ++ tailWord_2150376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150376).length < 2 ^ (prefixWord ++ tailWord_2150376).sum := by decide
  have hdescent : baseEnd_2150376 < baseStart_2150376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150393 : List Nat := [1, 2, 1, 3, 1, 5, 2, 1, 1, 5]
def baseStart_2150393 : Nat := 118140960795 + 2150393 * 2 ^ 59
def prefixEnd_2150393 : Nat := 4983230072969 + 3 ^ 40 * 2150393 * 2
def baseEnd_2150393 : Nat := 736123470042606874132019

theorem tailTrace_2150393 : CollatzResearch.WordTrace tailWord_2150393 prefixEnd_2150393 736123470042606874132019 := by
  unfold tailWord_2150393
  simp only [CollatzResearch.WordTrace]
  refine ⟨78431276098500893730615833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52287517399000595820410555 78431276098500893730615833)
  ·
    refine ⟨58823457073875670297961875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78431276098500893730615833 58823457073875670297961875)
    ·
      refine ⟨88235185610813505446942813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58823457073875670297961875 88235185610813505446942813)
      ·
        refine ⟨33088194604055064542603555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88235185610813505446942813 33088194604055064542603555)
        ·
          refine ⟨49632291906082596813905333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33088194604055064542603555 49632291906082596813905333)
          ·
            refine ⟨4653027366195243451303625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49632291906082596813905333 4653027366195243451303625)
            ·
              refine ⟨3489770524646432588477719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4653027366195243451303625 3489770524646432588477719)
              ·
                refine ⟨5234655786969648882716579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3489770524646432588477719 5234655786969648882716579)
                ·
                  refine ⟨7851983680454473324074869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5234655786969648882716579 7851983680454473324074869)
                  ·
                    refine ⟨736123470042606874132019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7851983680454473324074869 736123470042606874132019)
                    ·
                      rfl

theorem cell22_2150393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 5].length) (baseStart_2150393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2150393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2150393 prefixEnd_2150393 := by exact prefixLift 2150393
  have htrace : WordTrace (prefixWord ++ tailWord_2150393) baseStart_2150393 baseEnd_2150393 := by
    simpa [prefixWord, tailWord_2150393, baseEnd_2150393] using wordTrace_append hprefix tailTrace_2150393
  have hstable : (prefixWord ++ tailWord_2150393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150393).length < 2 ^ (prefixWord ++ tailWord_2150393).sum := by decide
  have hdescent : baseEnd_2150393 < baseStart_2150393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150423 : List Nat := [1, 1, 3, 5, 2, 1, 9]
def baseStart_2150423 : Nat := 118140960795 + 2150423 * 2 ^ 59
def prefixEnd_2150423 : Nat := 4983230072969 + 3 ^ 40 * 2150423 * 2
def baseEnd_2150423 : Nat := 27264212579840622069701

theorem tailTrace_2150423 : CollatzResearch.WordTrace tailWord_2150423 prefixEnd_2150423 27264212579840622069701 := by
  unfold tailWord_2150423
  simp only [CollatzResearch.WordTrace]
  refine ⟨78432370288392208854207923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52288246858928139236138615 78432370288392208854207923)
  ·
    refine ⟨117648555432588313281311885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78432370288392208854207923 117648555432588313281311885)
    ·
      refine ⟨44118208287220617480491957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117648555432588313281311885 44118208287220617480491957)
      ·
        refine ⟨4136082026926932888796121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44118208287220617480491957 4136082026926932888796121)
        ·
          refine ⟨3102061520195199666597091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4136082026926932888796121 3102061520195199666597091)
          ·
            refine ⟨4653092280292799499895637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3102061520195199666597091 4653092280292799499895637)
            ·
              refine ⟨27264212579840622069701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4653092280292799499895637 27264212579840622069701)
              ·
                rfl

theorem cell22_2150423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 9].length) (baseStart_2150423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2150423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2150423 prefixEnd_2150423 := by exact prefixLift 2150423
  have htrace : WordTrace (prefixWord ++ tailWord_2150423) baseStart_2150423 baseEnd_2150423 := by
    simpa [prefixWord, tailWord_2150423, baseEnd_2150423] using wordTrace_append hprefix tailTrace_2150423
  have hstable : (prefixWord ++ tailWord_2150423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150423).length < 2 ^ (prefixWord ++ tailWord_2150423).sum := by decide
  have hdescent : baseEnd_2150423 < baseStart_2150423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150457 : List Nat := [1, 2, 1, 5, 4, 1, 2, 6]
def baseStart_2150457 : Nat := 118140960795 + 2150457 * 2 ^ 59
def prefixEnd_2150457 : Nat := 4983230072969 + 3 ^ 40 * 2150457 * 2
def baseEnd_2150457 : Nat := 81793930950059115614647

theorem tailTrace_2150457 : CollatzResearch.WordTrace tailWord_2150457 prefixEnd_2150457 81793930950059115614647 := by
  unfold tailWord_2150457
  simp only [CollatzResearch.WordTrace]
  refine ⟨78433610370269032660945625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52289073580179355107297083 78433610370269032660945625)
  ·
    refine ⟨58825207777701774495709219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78433610370269032660945625 58825207777701774495709219)
    ·
      refine ⟨88237811666552661743563829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58825207777701774495709219 88237811666552661743563829)
      ·
        refine ⟨8272294843739312038459109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88237811666552661743563829 8272294843739312038459109)
        ·
          refine ⟨1551055283201121007211083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8272294843739312038459109 1551055283201121007211083)
          ·
            refine ⟨2326582924801681510816625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1551055283201121007211083 2326582924801681510816625)
            ·
              refine ⟨1744937193601261133112469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2326582924801681510816625 1744937193601261133112469)
              ·
                refine ⟨81793930950059115614647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1744937193601261133112469 81793930950059115614647)
                ·
                  rfl

theorem cell22_2150457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 6].length) (baseStart_2150457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2150457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2150457 prefixEnd_2150457 := by exact prefixLift 2150457
  have htrace : WordTrace (prefixWord ++ tailWord_2150457) baseStart_2150457 baseEnd_2150457 := by
    simpa [prefixWord, tailWord_2150457, baseEnd_2150457] using wordTrace_append hprefix tailTrace_2150457
  have hstable : (prefixWord ++ tailWord_2150457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150457).length < 2 ^ (prefixWord ++ tailWord_2150457).sum := by decide
  have hdescent : baseEnd_2150457 < baseStart_2150457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150532 : List Nat := [2, 3, 2, 1, 2, 1, 5, 1, 1, 4]
def baseStart_2150532 : Nat := 118140960795 + 2150532 * 2 ^ 59
def prefixEnd_2150532 : Nat := 4983230072969 + 3 ^ 40 * 2150532 * 2
def baseEnd_2150532 : Nat := 736171052583256844906593

theorem tailTrace_2150532 : CollatzResearch.WordTrace tailWord_2150532 prefixEnd_2150532 736171052583256844906593 := by
  unfold tailWord_2150532
  simp only [CollatzResearch.WordTrace]
  refine ⟨39218172922498660234962925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52290897229998213646617233 39218172922498660234962925)
  ·
    refine ⟨14706814845936997588111097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39218172922498660234962925 14706814845936997588111097)
    ·
      refine ⟨11030111134452748191083323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14706814845936997588111097 11030111134452748191083323)
      ·
        refine ⟨16545166701679122286624985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11030111134452748191083323 16545166701679122286624985)
        ·
          refine ⟨12408875026259341714968739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16545166701679122286624985 12408875026259341714968739)
          ·
            refine ⟨18613312539389012572453109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12408875026259341714968739 18613312539389012572453109)
            ·
              refine ⟨1744998050567719928667479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18613312539389012572453109 1744998050567719928667479)
              ·
                refine ⟨2617497075851579893001219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1744998050567719928667479 2617497075851579893001219)
                ·
                  refine ⟨3926245613777369839501829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2617497075851579893001219 3926245613777369839501829)
                  ·
                    refine ⟨736171052583256844906593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3926245613777369839501829 736171052583256844906593)
                    ·
                      rfl

theorem cell22_2150532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_2150532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2150532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2150532 prefixEnd_2150532 := by exact prefixLift 2150532
  have htrace : WordTrace (prefixWord ++ tailWord_2150532) baseStart_2150532 baseEnd_2150532 := by
    simpa [prefixWord, tailWord_2150532, baseEnd_2150532] using wordTrace_append hprefix tailTrace_2150532
  have hstable : (prefixWord ++ tailWord_2150532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150532).length < 2 ^ (prefixWord ++ tailWord_2150532).sum := by decide
  have hdescent : baseEnd_2150532 < baseStart_2150532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150562 : List Nat := [3, 3, 1, 3, 1, 2, 2, 1, 1, 5]
def baseStart_2150562 : Nat := 118140960795 + 2150562 * 2 ^ 59
def prefixEnd_2150562 : Nat := 4983230072969 + 3 ^ 40 * 2150562 * 2
def baseEnd_2150562 : Nat := 736181322196346766656501

theorem tailTrace_2150562 : CollatzResearch.WordTrace tailWord_2150562 prefixEnd_2150562 736181322196346766656501 := by
  unfold tailWord_2150562
  simp only [CollatzResearch.WordTrace]
  refine ⟨19609360008722158898379485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52291626689925757062345293 19609360008722158898379485)
  ·
    refine ⟨7353510003270809586892307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19609360008722158898379485 7353510003270809586892307)
    ·
      refine ⟨11030265004906214380338461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7353510003270809586892307 11030265004906214380338461)
      ·
        refine ⟨4136349376839830392626923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11030265004906214380338461 4136349376839830392626923)
        ·
          refine ⟨6204524065259745588940385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4136349376839830392626923 6204524065259745588940385)
          ·
            refine ⟨4653393048944809191705289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6204524065259745588940385 4653393048944809191705289)
            ·
              refine ⟨3490044786708606893778967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4653393048944809191705289 3490044786708606893778967)
              ·
                refine ⟨5235067180062910340668451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3490044786708606893778967 5235067180062910340668451)
                ·
                  refine ⟨7852600770094365511002677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5235067180062910340668451 7852600770094365511002677)
                  ·
                    refine ⟨736181322196346766656501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7852600770094365511002677 736181322196346766656501)
                    ·
                      rfl

theorem cell22_2150562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_2150562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2150562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2150562 prefixEnd_2150562 := by exact prefixLift 2150562
  have htrace : WordTrace (prefixWord ++ tailWord_2150562) baseStart_2150562 baseEnd_2150562 := by
    simpa [prefixWord, tailWord_2150562, baseEnd_2150562] using wordTrace_append hprefix tailTrace_2150562
  have hstable : (prefixWord ++ tailWord_2150562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150562).length < 2 ^ (prefixWord ++ tailWord_2150562).sum := by decide
  have hdescent : baseEnd_2150562 < baseStart_2150562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150603 : List Nat := [1, 1, 1, 1, 3, 2, 5, 1, 7]
def baseStart_2150603 : Nat := 118140960795 + 2150603 * 2 ^ 59
def prefixEnd_2150603 : Nat := 4983230072969 + 3 ^ 40 * 2150603 * 2
def baseEnd_2150603 : Nat := 245398452444745442127125

theorem tailTrace_2150603 : CollatzResearch.WordTrace tailWord_2150603 prefixEnd_2150603 245398452444745442127125 := by
  unfold tailWord_2150603
  simp only [CollatzResearch.WordTrace]
  refine ⟨78438935427740099595760463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52292623618493399730506975 78438935427740099595760463)
  ·
    refine ⟨117658403141610149393640695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78438935427740099595760463 117658403141610149393640695)
    ·
      refine ⟨176487604712415224090461043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117658403141610149393640695 176487604712415224090461043)
      ·
        refine ⟨264731407068622836135691565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176487604712415224090461043 264731407068622836135691565)
        ·
          refine ⟨99274277650733563550884337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 264731407068622836135691565 99274277650733563550884337)
          ·
            refine ⟨74455708238050172663163253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99274277650733563550884337 74455708238050172663163253)
            ·
              refine ⟨6980222647317203687171555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74455708238050172663163253 6980222647317203687171555)
              ·
                refine ⟨10470333970975805530757333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6980222647317203687171555 10470333970975805530757333)
                ·
                  refine ⟨245398452444745442127125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10470333970975805530757333 245398452444745442127125)
                  ·
                    rfl

theorem cell22_2150603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 7].length) (baseStart_2150603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2150603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2150603 prefixEnd_2150603 := by exact prefixLift 2150603
  have htrace : WordTrace (prefixWord ++ tailWord_2150603) baseStart_2150603 baseEnd_2150603 := by
    simpa [prefixWord, tailWord_2150603, baseEnd_2150603] using wordTrace_append hprefix tailTrace_2150603
  have hstable : (prefixWord ++ tailWord_2150603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150603).length < 2 ^ (prefixWord ++ tailWord_2150603).sum := by decide
  have hdescent : baseEnd_2150603 < baseStart_2150603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150607 : List Nat := [1, 1, 2, 1, 1, 3, 3, 6, 1, 3]
def baseStart_2150607 : Nat := 118140960795 + 2150607 * 2 ^ 59
def prefixEnd_2150607 : Nat := 4983230072969 + 3 ^ 40 * 2150607 * 2
def baseEnd_2150607 : Nat := 736196726615981649281363

theorem tailTrace_2150607 : CollatzResearch.WordTrace tailWord_2150607 prefixEnd_2150607 736196726615981649281363 := by
  unfold tailWord_2150607
  simp only [CollatzResearch.WordTrace]
  refine ⟨78439081319725608278906075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52292720879817072185937383 78439081319725608278906075)
  ·
    refine ⟨117658621979588412418359113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78439081319725608278906075 117658621979588412418359113)
    ·
      refine ⟨88243966484691309313769335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117658621979588412418359113 88243966484691309313769335)
      ·
        refine ⟨132365949727036963970654003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88243966484691309313769335 132365949727036963970654003)
        ·
          refine ⟨198548924590555445955981005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132365949727036963970654003 198548924590555445955981005)
          ·
            refine ⟨74455846721458292233492877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 198548924590555445955981005 74455846721458292233492877)
            ·
              refine ⟨27920942520546859587559829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74455846721458292233492877 27920942520546859587559829)
              ·
                refine ⟨1308794180650634043166867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27920942520546859587559829 1308794180650634043166867)
                ·
                  refine ⟨1963191270975951064750301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1308794180650634043166867 1963191270975951064750301)
                  ·
                    refine ⟨736196726615981649281363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1963191270975951064750301 736196726615981649281363)
                    ·
                      rfl

theorem cell22_2150607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 6, 1, 3].length) (baseStart_2150607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2150607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2150607 prefixEnd_2150607 := by exact prefixLift 2150607
  have htrace : WordTrace (prefixWord ++ tailWord_2150607) baseStart_2150607 baseEnd_2150607 := by
    simpa [prefixWord, tailWord_2150607, baseEnd_2150607] using wordTrace_append hprefix tailTrace_2150607
  have hstable : (prefixWord ++ tailWord_2150607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150607).length < 2 ^ (prefixWord ++ tailWord_2150607).sum := by decide
  have hdescent : baseEnd_2150607 < baseStart_2150607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150648 : List Nat := [2, 1, 2, 1, 1, 2, 1, 4, 8]
def baseStart_2150648 : Nat := 118140960795 + 2150648 * 2 ^ 59
def prefixEnd_2150648 : Nat := 4983230072969 + 3 ^ 40 * 2150648 * 2
def baseEnd_2150648 : Nat := 245403587251290403002079

theorem tailTrace_2150648 : CollatzResearch.WordTrace tailWord_2150648 prefixEnd_2150648 245403587251290403002079 := by
  unfold tailWord_2150648
  simp only [CollatzResearch.WordTrace]
  refine ⟨39220288356288536140574299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52293717808384714854099065 39220288356288536140574299)
  ·
    refine ⟨58830432534432804210861449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39220288356288536140574299 58830432534432804210861449)
    ·
      refine ⟨44122824400824603158146087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58830432534432804210861449 44122824400824603158146087)
      ·
        refine ⟨66184236601236904737219131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44122824400824603158146087 66184236601236904737219131)
        ·
          refine ⟨99276354901855357105828697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66184236601236904737219131 99276354901855357105828697)
          ·
            refine ⟨74457266176391517829371523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99276354901855357105828697 74457266176391517829371523)
            ·
              refine ⟨111685899264587276744057285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74457266176391517829371523 111685899264587276744057285)
              ·
                refine ⟨20941106112110114389510741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111685899264587276744057285 20941106112110114389510741)
                ·
                  refine ⟨245403587251290403002079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20941106112110114389510741 245403587251290403002079)
                  ·
                    rfl

theorem cell22_2150648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 8].length) (baseStart_2150648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2150648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2150648 prefixEnd_2150648 := by exact prefixLift 2150648
  have htrace : WordTrace (prefixWord ++ tailWord_2150648) baseStart_2150648 baseEnd_2150648 := by
    simpa [prefixWord, tailWord_2150648, baseEnd_2150648] using wordTrace_append hprefix tailTrace_2150648
  have hstable : (prefixWord ++ tailWord_2150648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150648).length < 2 ^ (prefixWord ++ tailWord_2150648).sum := by decide
  have hdescent : baseEnd_2150648 < baseStart_2150648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150658 : List Nat := [3, 4, 1, 1, 2, 2, 3, 2, 1, 3]
def baseStart_2150658 : Nat := 118140960795 + 2150658 * 2 ^ 59
def prefixEnd_2150658 : Nat := 4983230072969 + 3 ^ 40 * 2150658 * 2
def baseEnd_2150658 : Nat := 736214184958234516256207

theorem tailTrace_2150658 : CollatzResearch.WordTrace tailWord_2150658 prefixEnd_2150658 736214184958234516256207 := by
  unfold tailWord_2150658
  simp only [CollatzResearch.WordTrace]
  refine ⟨19610235360635210997253157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52293960961693895992675085 19610235360635210997253157)
  ·
    refine ⟨3676919130119102061984967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19610235360635210997253157 3676919130119102061984967)
    ·
      refine ⟨5515378695178653092977451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3676919130119102061984967 5515378695178653092977451)
      ·
        refine ⟨8273068042767979639466177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5515378695178653092977451 8273068042767979639466177)
        ·
          refine ⟨6204801032075984729599633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8273068042767979639466177 6204801032075984729599633)
          ·
            refine ⟨4653600774056988547199725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6204801032075984729599633 4653600774056988547199725)
            ·
              refine ⟨1745100290271370705199897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4653600774056988547199725 1745100290271370705199897)
              ·
                refine ⟨1308825217703528028899923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1745100290271370705199897 1308825217703528028899923)
                ·
                  refine ⟨1963237826555292043349885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1308825217703528028899923 1963237826555292043349885)
                  ·
                    refine ⟨736214184958234516256207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1963237826555292043349885 736214184958234516256207)
                    ·
                      rfl

theorem cell22_2150658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_2150658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2150658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2150658 prefixEnd_2150658 := by exact prefixLift 2150658
  have htrace : WordTrace (prefixWord ++ tailWord_2150658) baseStart_2150658 baseEnd_2150658 := by
    simpa [prefixWord, tailWord_2150658, baseEnd_2150658] using wordTrace_append hprefix tailTrace_2150658
  have hstable : (prefixWord ++ tailWord_2150658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150658).length < 2 ^ (prefixWord ++ tailWord_2150658).sum := by decide
  have hdescent : baseEnd_2150658 < baseStart_2150658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150665 : List Nat := [1, 2, 1, 1, 3, 4, 3, 1, 6]
def baseStart_2150665 : Nat := 118140960795 + 2150665 * 2 ^ 59
def prefixEnd_2150665 : Nat := 4983230072969 + 3 ^ 40 * 2150665 * 2
def baseEnd_2150665 : Nat := 245405527067096277110395

theorem tailTrace_2150665 : CollatzResearch.WordTrace tailWord_2150665 prefixEnd_2150665 245405527067096277110395 := by
  unfold tailWord_2150665
  simp only [CollatzResearch.WordTrace]
  refine ⟨78441196753515484184517449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52294131169010322789678299 78441196753515484184517449)
  ·
    refine ⟨58830897565136613138388087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78441196753515484184517449 58830897565136613138388087)
    ·
      refine ⟨88246346347704919707582131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58830897565136613138388087 88246346347704919707582131)
      ·
        refine ⟨132369519521557379561373197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88246346347704919707582131 132369519521557379561373197)
        ·
          refine ⟨49638569820584017335514949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132369519521557379561373197 49638569820584017335514949)
          ·
            refine ⟨9307231841359503250409053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49638569820584017335514949 9307231841359503250409053)
            ·
              refine ⟨3490211940509813718903395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9307231841359503250409053 3490211940509813718903395)
              ·
                refine ⟨5235317910764720578355093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3490211940509813718903395 5235317910764720578355093)
                ·
                  refine ⟨245405527067096277110395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5235317910764720578355093 245405527067096277110395)
                  ·
                    rfl

theorem cell22_2150665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 6].length) (baseStart_2150665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2150665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2150665 prefixEnd_2150665 := by exact prefixLift 2150665
  have htrace : WordTrace (prefixWord ++ tailWord_2150665) baseStart_2150665 baseEnd_2150665 := by
    simpa [prefixWord, tailWord_2150665, baseEnd_2150665] using wordTrace_append hprefix tailTrace_2150665
  have hstable : (prefixWord ++ tailWord_2150665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150665).length < 2 ^ (prefixWord ++ tailWord_2150665).sum := by decide
  have hdescent : baseEnd_2150665 < baseStart_2150665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150680 : List Nat := [2, 1, 2, 3, 1, 2, 2, 3, 1, 5]
def baseStart_2150680 : Nat := 118140960795 + 2150680 * 2 ^ 59
def prefixEnd_2150680 : Nat := 4983230072969 + 3 ^ 40 * 2150680 * 2
def baseEnd_2150680 : Nat := 736221716007833792206139

theorem tailTrace_2150680 : CollatzResearch.WordTrace tailWord_2150680 prefixEnd_2150680 736221716007833792206139 := by
  unfold tailWord_2150680
  simp only [CollatzResearch.WordTrace]
  refine ⟨39220871924230570873156747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52294495898974094497542329 39220871924230570873156747)
  ·
    refine ⟨58831307886345856309735121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39220871924230570873156747 58831307886345856309735121)
    ·
      refine ⟨44123480914759392232301341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58831307886345856309735121 44123480914759392232301341)
      ·
        refine ⟨16546305343034772087113003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44123480914759392232301341 16546305343034772087113003)
        ·
          refine ⟨24819458014552158130669505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16546305343034772087113003 24819458014552158130669505)
          ·
            refine ⟨18614593510914118598002129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24819458014552158130669505 18614593510914118598002129)
            ·
              refine ⟨13960945133185588948501597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18614593510914118598002129 13960945133185588948501597)
              ·
                refine ⟨5235354424944595855688099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13960945133185588948501597 5235354424944595855688099)
                ·
                  refine ⟨7853031637416893783532149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5235354424944595855688099 7853031637416893783532149)
                  ·
                    refine ⟨736221716007833792206139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7853031637416893783532149 736221716007833792206139)
                    ·
                      rfl

theorem cell22_2150680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_2150680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2150680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2150680 prefixEnd_2150680 := by exact prefixLift 2150680
  have htrace : WordTrace (prefixWord ++ tailWord_2150680) baseStart_2150680 baseEnd_2150680 := by
    simpa [prefixWord, tailWord_2150680, baseEnd_2150680] using wordTrace_append hprefix tailTrace_2150680
  have hstable : (prefixWord ++ tailWord_2150680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150680).length < 2 ^ (prefixWord ++ tailWord_2150680).sum := by decide
  have hdescent : baseEnd_2150680 < baseStart_2150680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150710 : List Nat := [5, 1, 2, 14]
def baseStart_2150710 : Nat := 118140960795 + 2150710 * 2 ^ 59
def prefixEnd_2150710 : Nat := 4983230072969 + 3 ^ 40 * 2150710 * 2
def baseEnd_2150710 : Nat := 1009920419233091514343

theorem tailTrace_2150710 : CollatzResearch.WordTrace tailWord_2150710 prefixEnd_2150710 1009920419233091514343 := by
  unfold tailWord_2150710
  simp only [CollatzResearch.WordTrace]
  refine ⟨4902677377397028554369099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52295225358901637913270389 4902677377397028554369099)
  ·
    refine ⟨7354016066095542831553649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4902677377397028554369099 7354016066095542831553649)
    ·
      refine ⟨5515512049571657123665237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7354016066095542831553649 5515512049571657123665237)
      ·
        refine ⟨1009920419233091514343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 5515512049571657123665237 1009920419233091514343)
        ·
          rfl

theorem cell22_2150710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 14].length) (baseStart_2150710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2150710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2150710 prefixEnd_2150710 := by exact prefixLift 2150710
  have htrace : WordTrace (prefixWord ++ tailWord_2150710) baseStart_2150710 baseEnd_2150710 := by
    simpa [prefixWord, tailWord_2150710, baseEnd_2150710] using wordTrace_append hprefix tailTrace_2150710
  have hstable : (prefixWord ++ tailWord_2150710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150710).length < 2 ^ (prefixWord ++ tailWord_2150710).sum := by decide
  have hdescent : baseEnd_2150710 < baseStart_2150710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150714 : List Nat := [3, 1, 1, 1, 4, 3, 2, 2, 2, 3]
def baseStart_2150714 : Nat := 118140960795 + 2150714 * 2 ^ 59
def prefixEnd_2150714 : Nat := 4983230072969 + 3 ^ 40 * 2150714 * 2
def baseEnd_2150714 : Nat := 736233354902669036856035

theorem tailTrace_2150714 : CollatzResearch.WordTrace tailWord_2150714 prefixEnd_2150714 736233354902669036856035 := by
  unfold tailWord_2150714
  simp only [CollatzResearch.WordTrace]
  refine ⟨19610745982584491388262799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52295322620225310368700797 19610745982584491388262799)
  ·
    refine ⟨29416118973876737082394199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19610745982584491388262799 29416118973876737082394199)
    ·
      refine ⟨44124178460815105623591299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29416118973876737082394199 44124178460815105623591299)
      ·
        refine ⟨66186267691222658435386949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44124178460815105623591299 66186267691222658435386949)
        ·
          refine ⟨12409925192104248456635053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66186267691222658435386949 12409925192104248456635053)
          ·
            refine ⟨4653721947039093171238145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12409925192104248456635053 4653721947039093171238145)
            ·
              refine ⟨3490291460279319878428609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4653721947039093171238145 3490291460279319878428609)
              ·
                refine ⟨2617718595209489908821457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3490291460279319878428609 2617718595209489908821457)
                ·
                  refine ⟨1963288946407117431616093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2617718595209489908821457 1963288946407117431616093)
                  ·
                    refine ⟨736233354902669036856035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1963288946407117431616093 736233354902669036856035)
                    ·
                      rfl

theorem cell22_2150714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 2, 3].length) (baseStart_2150714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2150714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2150714 prefixEnd_2150714 := by exact prefixLift 2150714
  have htrace : WordTrace (prefixWord ++ tailWord_2150714) baseStart_2150714 baseEnd_2150714 := by
    simpa [prefixWord, tailWord_2150714, baseEnd_2150714] using wordTrace_append hprefix tailTrace_2150714
  have hstable : (prefixWord ++ tailWord_2150714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150714).length < 2 ^ (prefixWord ++ tailWord_2150714).sum := by decide
  have hdescent : baseEnd_2150714 < baseStart_2150714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150755 : List Nat := [1, 1, 1, 5, 2, 1, 2, 2, 7]
def baseStart_2150755 : Nat := 118140960795 + 2150755 * 2 ^ 59
def prefixEnd_2150755 : Nat := 4983230072969 + 3 ^ 40 * 2150755 * 2
def baseEnd_2150755 : Nat := 245415796680186198860303

theorem tailTrace_2150755 : CollatzResearch.WordTrace tailWord_2150755 prefixEnd_2150755 245415796680186198860303 := by
  unfold tailWord_2150755
  simp only [CollatzResearch.WordTrace]
  refine ⟨78444479323189429555293719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52296319548792953036862479 78444479323189429555293719)
  ·
    refine ⟨117666718984784144332940579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78444479323189429555293719 117666718984784144332940579)
    ·
      refine ⟨176500078477176216499410869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117666718984784144332940579 176500078477176216499410869)
      ·
        refine ⟨16546882357235270296819769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 176500078477176216499410869 16546882357235270296819769)
        ·
          refine ⟨12410161767926452722614827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16546882357235270296819769 12410161767926452722614827)
          ·
            refine ⟨18615242651889679083922241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12410161767926452722614827 18615242651889679083922241)
            ·
              refine ⟨13961431988917259312941681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18615242651889679083922241 13961431988917259312941681)
              ·
                refine ⟨10471073991687944484706261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13961431988917259312941681 10471073991687944484706261)
                ·
                  refine ⟨245415796680186198860303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10471073991687944484706261 245415796680186198860303)
                  ·
                    rfl

theorem cell22_2150755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 7].length) (baseStart_2150755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2150755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2150755 prefixEnd_2150755 := by exact prefixLift 2150755
  have htrace : WordTrace (prefixWord ++ tailWord_2150755) baseStart_2150755 baseEnd_2150755 := by
    simpa [prefixWord, tailWord_2150755, baseEnd_2150755] using wordTrace_append hprefix tailTrace_2150755
  have hstable : (prefixWord ++ tailWord_2150755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150755).length < 2 ^ (prefixWord ++ tailWord_2150755).sum := by decide
  have hdescent : baseEnd_2150755 < baseStart_2150755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150866 : List Nat := [3, 2, 2, 4, 1, 1, 1, 2, 1, 5]
def baseStart_2150866 : Nat := 118140960795 + 2150866 * 2 ^ 59
def prefixEnd_2150866 : Nat := 4983230072969 + 3 ^ 40 * 2150866 * 2
def baseEnd_2150866 : Nat := 736285387608991307055569

theorem tailTrace_2150866 : CollatzResearch.WordTrace tailWord_2150866 prefixEnd_2150866 736285387608991307055569 := by
  unfold tailWord_2150866
  simp only [CollatzResearch.WordTrace]
  refine ⟨19612131956446823878146113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52299018550524863675056301 19612131956446823878146113)
  ·
    refine ⟨14709098967335117908609585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19612131956446823878146113 14709098967335117908609585)
    ·
      refine ⟨11031824225501338431457189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14709098967335117908609585 11031824225501338431457189)
      ·
        refine ⟨2068467042281500955898223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11031824225501338431457189 2068467042281500955898223)
        ·
          refine ⟨3102700563422251433847335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2068467042281500955898223 3102700563422251433847335)
          ·
            refine ⟨4654050845133377150771003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3102700563422251433847335 4654050845133377150771003)
            ·
              refine ⟨6981076267700065726156505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4654050845133377150771003 6981076267700065726156505)
              ·
                refine ⟨5235807200775049294617379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6981076267700065726156505 5235807200775049294617379)
                ·
                  refine ⟨7853710801162573941926069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5235807200775049294617379 7853710801162573941926069)
                  ·
                    refine ⟨736285387608991307055569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7853710801162573941926069 736285387608991307055569)
                    ·
                      rfl

theorem cell22_2150866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_2150866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2150866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2150866 prefixEnd_2150866 := by exact prefixLift 2150866
  have htrace : WordTrace (prefixWord ++ tailWord_2150866) baseStart_2150866 baseEnd_2150866 := by
    simpa [prefixWord, tailWord_2150866, baseEnd_2150866] using wordTrace_append hprefix tailTrace_2150866
  have hstable : (prefixWord ++ tailWord_2150866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150866).length < 2 ^ (prefixWord ++ tailWord_2150866).sum := by decide
  have hdescent : baseEnd_2150866 < baseStart_2150866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150885 : List Nat := [1, 3, 1, 5, 3, 1, 2, 2, 4]
def baseStart_2150885 : Nat := 118140960795 + 2150885 * 2 ^ 59
def prefixEnd_2150885 : Nat := 4983230072969 + 3 ^ 40 * 2150885 * 2
def baseEnd_2150885 : Nat := 245430630565760530276837

theorem tailTrace_2150885 : CollatzResearch.WordTrace tailWord_2150885 prefixEnd_2150885 245430630565760530276837 := by
  unfold tailWord_2150885
  simp only [CollatzResearch.WordTrace]
  refine ⟨78449220812718461757526109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52299480541812307838350739 78449220812718461757526109)
  ·
    refine ⟨29418457804769423159072291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78449220812718461757526109 29418457804769423159072291)
    ·
      refine ⟨44127686707154134738608437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29418457804769423159072291 44127686707154134738608437)
      ·
        refine ⟨4136970628795700131744541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44127686707154134738608437 4136970628795700131744541)
        ·
          refine ⟨1551363985798387549404203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4136970628795700131744541 1551363985798387549404203)
          ·
            refine ⟨2327045978697581324106305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1551363985798387549404203 2327045978697581324106305)
            ·
              refine ⟨1745284484023185993079729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2327045978697581324106305 1745284484023185993079729)
              ·
                refine ⟨1308963363017389494809797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1745284484023185993079729 1308963363017389494809797)
                ·
                  refine ⟨245430630565760530276837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1308963363017389494809797 245430630565760530276837)
                  ·
                    rfl

theorem cell22_2150885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 2, 4].length) (baseStart_2150885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2150885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2150885 prefixEnd_2150885 := by exact prefixLift 2150885
  have htrace : WordTrace (prefixWord ++ tailWord_2150885) baseStart_2150885 baseEnd_2150885 := by
    simpa [prefixWord, tailWord_2150885, baseEnd_2150885] using wordTrace_append hprefix tailTrace_2150885
  have hstable : (prefixWord ++ tailWord_2150885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150885).length < 2 ^ (prefixWord ++ tailWord_2150885).sum := by decide
  have hdescent : baseEnd_2150885 < baseStart_2150885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150922 : List Nat := [3, 1, 2, 2, 2, 1, 1, 2, 1, 7]
def baseStart_2150922 : Nat := 118140960795 + 2150922 * 2 ^ 59
def prefixEnd_2150922 : Nat := 4983230072969 + 3 ^ 40 * 2150922 * 2
def baseEnd_2150922 : Nat := 736304557553425827655397

theorem tailTrace_2150922 : CollatzResearch.WordTrace tailWord_2150922 prefixEnd_2150922 736304557553425827655397 := by
  unfold tailWord_2150922
  simp only [CollatzResearch.WordTrace]
  refine ⟨19612642578396104269155755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52300380209056278051082013 19612642578396104269155755)
  ·
    refine ⟨29418963867594156403733633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19612642578396104269155755 29418963867594156403733633)
    ·
      refine ⟨22064222900695617302800225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29418963867594156403733633 22064222900695617302800225)
      ·
        refine ⟨16548167175521712977100169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22064222900695617302800225 16548167175521712977100169)
        ·
          refine ⟨12411125381641284732825127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16548167175521712977100169 12411125381641284732825127)
          ·
            refine ⟨18616688072461927099237691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12411125381641284732825127 18616688072461927099237691)
            ·
              refine ⟨27925032108692890648856537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18616688072461927099237691 27925032108692890648856537)
              ·
                refine ⟨20943774081519667986642403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27925032108692890648856537 20943774081519667986642403)
                ·
                  refine ⟨31415661122279501979963605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20943774081519667986642403 31415661122279501979963605)
                  ·
                    refine ⟨736304557553425827655397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31415661122279501979963605 736304557553425827655397)
                    ·
                      rfl

theorem cell22_2150922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_2150922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2150922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2150922 prefixEnd_2150922 := by exact prefixLift 2150922
  have htrace : WordTrace (prefixWord ++ tailWord_2150922) baseStart_2150922 baseEnd_2150922 := by
    simpa [prefixWord, tailWord_2150922, baseEnd_2150922] using wordTrace_append hprefix tailTrace_2150922
  have hstable : (prefixWord ++ tailWord_2150922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150922).length < 2 ^ (prefixWord ++ tailWord_2150922).sum := by decide
  have hdescent : baseEnd_2150922 < baseStart_2150922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150941 : List Nat := [1, 4, 2, 2, 1, 4, 1, 2, 5]
def baseStart_2150941 : Nat := 118140960795 + 2150941 * 2 ^ 59
def prefixEnd_2150941 : Nat := 4983230072969 + 3 ^ 40 * 2150941 * 2
def baseEnd_2150941 : Nat := 245437020547238703810113

theorem tailTrace_2150941 : CollatzResearch.WordTrace tailWord_2150941 prefixEnd_2150941 245437020547238703810113 := by
  unfold tailWord_2150941
  simp only [CollatzResearch.WordTrace]
  refine ⟨78451263300515583321564677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52300842200343722214376451 78451263300515583321564677)
  ·
    refine ⟨14709611868846671872793377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78451263300515583321564677 14709611868846671872793377)
    ·
      refine ⟨11032208901635003904595033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14709611868846671872793377 11032208901635003904595033)
      ·
        refine ⟨8274156676226252928446275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11032208901635003904595033 8274156676226252928446275)
        ·
          refine ⟨12411235014339379392669413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8274156676226252928446275 12411235014339379392669413)
          ·
            refine ⟨2327106565188633636125515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12411235014339379392669413 2327106565188633636125515)
            ·
              refine ⟨3490659847782950454188273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2327106565188633636125515 3490659847782950454188273)
              ·
                refine ⟨2617994885837212840641205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3490659847782950454188273 2617994885837212840641205)
                ·
                  refine ⟨245437020547238703810113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2617994885837212840641205 245437020547238703810113)
                  ·
                    rfl

theorem cell22_2150941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_2150941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2150941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2150941 prefixEnd_2150941 := by exact prefixLift 2150941
  have htrace : WordTrace (prefixWord ++ tailWord_2150941) baseStart_2150941 baseEnd_2150941 := by
    simpa [prefixWord, tailWord_2150941, baseEnd_2150941] using wordTrace_append hprefix tailTrace_2150941
  have hstable : (prefixWord ++ tailWord_2150941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150941).length < 2 ^ (prefixWord ++ tailWord_2150941).sum := by decide
  have hdescent : baseEnd_2150941 < baseStart_2150941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150958 : List Nat := [4, 1, 3, 1, 3, 1, 3, 1, 5]
def baseStart_2150958 : Nat := 118140960795 + 2150958 * 2 ^ 59
def prefixEnd_2150958 : Nat := 4983230072969 + 3 ^ 40 * 2150958 * 2
def baseEnd_2150958 : Nat := 245438960363044577918429

theorem tailTrace_2150958 : CollatzResearch.WordTrace tailWord_2150958 prefixEnd_2150958 245438960363044577918429 := by
  unfold tailWord_2150958
  simp only [CollatzResearch.WordTrace]
  refine ⟨9806485417681749403116691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52301255560969330149955685 9806485417681749403116691)
  ·
    refine ⟨14709728126522624104675037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9806485417681749403116691 14709728126522624104675037)
    ·
      refine ⟨5516148047445984039253139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14709728126522624104675037 5516148047445984039253139)
      ·
        refine ⟨8274222071168976058879709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5516148047445984039253139 8274222071168976058879709)
        ·
          refine ⟨3102833276688366022079891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8274222071168976058879709 3102833276688366022079891)
          ·
            refine ⟨4654249915032549033119837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3102833276688366022079891 4654249915032549033119837)
            ·
              refine ⟨1745343718137205887419939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4654249915032549033119837 1745343718137205887419939)
              ·
                refine ⟨2618015577205808831129909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1745343718137205887419939 2618015577205808831129909)
                ·
                  refine ⟨245438960363044577918429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2618015577205808831129909 245438960363044577918429)
                  ·
                    rfl

theorem cell22_2150958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_2150958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2150958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2150958 prefixEnd_2150958 := by exact prefixLift 2150958
  have htrace : WordTrace (prefixWord ++ tailWord_2150958) baseStart_2150958 baseEnd_2150958 := by
    simpa [prefixWord, tailWord_2150958, baseEnd_2150958] using wordTrace_append hprefix tailTrace_2150958
  have hstable : (prefixWord ++ tailWord_2150958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150958).length < 2 ^ (prefixWord ++ tailWord_2150958).sum := by decide
  have hdescent : baseEnd_2150958 < baseStart_2150958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150986 : List Nat := [3, 1, 2, 1, 1, 4, 3, 3, 4]
def baseStart_2150986 : Nat := 118140960795 + 2150986 * 2 ^ 59
def prefixEnd_2150986 : Nat := 4983230072969 + 3 ^ 40 * 2150986 * 2
def baseEnd_2150986 : Nat := 245442155353783664685067

theorem tailTrace_2150986 : CollatzResearch.WordTrace tailWord_2150986 prefixEnd_2150986 245442155353783664685067 := by
  unfold tailWord_2150986
  simp only [CollatzResearch.WordTrace]
  refine ⟨19613226146338139001738203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52301936390235037337968541 19613226146338139001738203)
  ·
    refine ⟨29419839219507208502607305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19613226146338139001738203 29419839219507208502607305)
    ·
      refine ⟨22064879414630406376955479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29419839219507208502607305 22064879414630406376955479)
      ·
        refine ⟨33097319121945609565433219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22064879414630406376955479 33097319121945609565433219)
        ·
          refine ⟨49645978682918414348149829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33097319121945609565433219 49645978682918414348149829)
          ·
            refine ⟨9308621003047202690278093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49645978682918414348149829 9308621003047202690278093)
            ·
              refine ⟨3490732876142701008854285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9308621003047202690278093 3490732876142701008854285)
              ·
                refine ⟨1309024828553512878320357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3490732876142701008854285 1309024828553512878320357)
                ·
                  refine ⟨245442155353783664685067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1309024828553512878320357 245442155353783664685067)
                  ·
                    rfl

theorem cell22_2150986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 3, 4].length) (baseStart_2150986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2150986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2150986 prefixEnd_2150986 := by exact prefixLift 2150986
  have htrace : WordTrace (prefixWord ++ tailWord_2150986) baseStart_2150986 baseEnd_2150986 := by
    simpa [prefixWord, tailWord_2150986, baseEnd_2150986] using wordTrace_append hprefix tailTrace_2150986
  have hstable : (prefixWord ++ tailWord_2150986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150986).length < 2 ^ (prefixWord ++ tailWord_2150986).sum := by decide
  have hdescent : baseEnd_2150986 < baseStart_2150986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150997 : List Nat := [1, 3, 2, 2, 1, 1, 12]
def baseStart_2150997 : Nat := 118140960795 + 2150997 * 2 ^ 59
def prefixEnd_2150997 : Nat := 4983230072969 + 3 ^ 40 * 2150997 * 2
def baseEnd_2150997 : Nat := 27271490058746319704821

theorem tailTrace_2150997 : CollatzResearch.WordTrace tailWord_2150997 prefixEnd_2150997 27271490058746319704821 := by
  unfold tailWord_2150997
  simp only [CollatzResearch.WordTrace]
  refine ⟨78453305788312704885603245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52302203858875136590402163 78453305788312704885603245)
  ·
    refine ⟨29419989670617264332101217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78453305788312704885603245 29419989670617264332101217)
    ·
      refine ⟨22064992252962948249075913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29419989670617264332101217 22064992252962948249075913)
      ·
        refine ⟨16548744189722211186806935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22064992252962948249075913 16548744189722211186806935)
        ·
          refine ⟨24823116284583316780210403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16548744189722211186806935 24823116284583316780210403)
          ·
            refine ⟨37234674426874975170315605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24823116284583316780210403 37234674426874975170315605)
            ·
              refine ⟨27271490058746319704821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 37234674426874975170315605 27271490058746319704821)
              ·
                rfl

theorem cell22_2150997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 12].length) (baseStart_2150997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2150997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2150997 prefixEnd_2150997 := by exact prefixLift 2150997
  have htrace : WordTrace (prefixWord ++ tailWord_2150997) baseStart_2150997 baseEnd_2150997 := by
    simpa [prefixWord, tailWord_2150997, baseEnd_2150997] using wordTrace_append hprefix tailTrace_2150997
  have hstable : (prefixWord ++ tailWord_2150997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150997).length < 2 ^ (prefixWord ++ tailWord_2150997).sum := by decide
  have hdescent : baseEnd_2150997 < baseStart_2150997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150999 : List Nat := [1, 1, 3, 2, 2, 2, 3, 2, 2, 4]
def baseStart_2150999 : Nat := 118140960795 + 2150999 * 2 ^ 59
def prefixEnd_2150999 : Nat := 4983230072969 + 3 ^ 40 * 2150999 * 2
def baseEnd_2150999 : Nat := 736330916227023293480161

theorem tailTrace_2150999 : CollatzResearch.WordTrace tailWord_2150999 prefixEnd_2150999 736330916227023293480161 := by
  unfold tailWord_2150999
  simp only [CollatzResearch.WordTrace]
  refine ⟨78453378734305459227176051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52302252489536972818117367 78453378734305459227176051)
  ·
    refine ⟨117680068101458188840764077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78453378734305459227176051 117680068101458188840764077)
    ·
      refine ⟨44130025538046820815286529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117680068101458188840764077 44130025538046820815286529)
      ·
        refine ⟨33097519153535115611464897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44130025538046820815286529 33097519153535115611464897)
        ·
          refine ⟨24823139365151336708598673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33097519153535115611464897 24823139365151336708598673)
          ·
            refine ⟨18617354523863502531449005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24823139365151336708598673 18617354523863502531449005)
            ·
              refine ⟨6981507946448813449293377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18617354523863502531449005 6981507946448813449293377)
              ·
                refine ⟨5236130959836610086970033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6981507946448813449293377 5236130959836610086970033)
                ·
                  refine ⟨3927098219877457565227525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5236130959836610086970033 3927098219877457565227525)
                  ·
                    refine ⟨736330916227023293480161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3927098219877457565227525 736330916227023293480161)
                    ·
                      rfl

theorem cell22_2150999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_2150999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2150999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2150999 prefixEnd_2150999 := by exact prefixLift 2150999
  have htrace : WordTrace (prefixWord ++ tailWord_2150999) baseStart_2150999 baseEnd_2150999 := by
    simpa [prefixWord, tailWord_2150999, baseEnd_2150999] using wordTrace_append hprefix tailTrace_2150999
  have hstable : (prefixWord ++ tailWord_2150999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150999).length < 2 ^ (prefixWord ++ tailWord_2150999).sum := by decide
  have hdescent : baseEnd_2150999 < baseStart_2150999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151027 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 4, 6]
def baseStart_2151027 : Nat := 118140960795 + 2151027 * 2 ^ 59
def prefixEnd_2151027 : Nat := 4983230072969 + 3 ^ 40 * 2151027 * 2
def baseEnd_2151027 : Nat := 736340501199240553780075

theorem tailTrace_2151027 : CollatzResearch.WordTrace tailWord_2151027 prefixEnd_2151027 736340501199240553780075 := by
  unfold tailWord_2151027
  simp only [CollatzResearch.WordTrace]
  refine ⟨78454399978204020009195335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52302933318802680006130223 78454399978204020009195335)
  ·
    refine ⟨117681599967306030013793003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78454399978204020009195335 117681599967306030013793003)
    ·
      refine ⟨176522399950959045020689505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117681599967306030013793003 176522399950959045020689505)
      ·
        refine ⟨132391799963219283765517129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176522399950959045020689505 132391799963219283765517129)
        ·
          refine ⟨99293849972414462824137847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132391799963219283765517129 99293849972414462824137847)
          ·
            refine ⟨148940774958621694236206771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99293849972414462824137847 148940774958621694236206771)
            ·
              refine ⟨223411162437932541354310157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148940774958621694236206771 223411162437932541354310157)
              ·
                refine ⟨83779185914224703007866309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 223411162437932541354310157 83779185914224703007866309)
                ·
                  refine ⟨15708597358917131813974933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83779185914224703007866309 15708597358917131813974933)
                  ·
                    refine ⟨736340501199240553780075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15708597358917131813974933 736340501199240553780075)
                    ·
                      rfl

theorem cell22_2151027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 6].length) (baseStart_2151027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2151027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2151027 prefixEnd_2151027 := by exact prefixLift 2151027
  have htrace : WordTrace (prefixWord ++ tailWord_2151027) baseStart_2151027 baseEnd_2151027 := by
    simpa [prefixWord, tailWord_2151027, baseEnd_2151027] using wordTrace_append hprefix tailTrace_2151027
  have hstable : (prefixWord ++ tailWord_2151027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151027).length < 2 ^ (prefixWord ++ tailWord_2151027).sum := by decide
  have hdescent : baseEnd_2151027 < baseStart_2151027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151063 : List Nat := [1, 1, 3, 3, 2, 1, 3, 4, 1, 3]
def baseStart_2151063 : Nat := 118140960795 + 2151063 * 2 ^ 59
def prefixEnd_2151063 : Nat := 4983230072969 + 3 ^ 40 * 2151063 * 2
def baseEnd_2151063 : Nat := 736352824734948459879965

theorem tailTrace_2151063 : CollatzResearch.WordTrace tailWord_2151063 prefixEnd_2151063 736352824734948459879965 := by
  unfold tailWord_2151063
  simp only [CollatzResearch.WordTrace]
  refine ⟨78455713006073598157505843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52303808670715732105003895 78455713006073598157505843)
  ·
    refine ⟨117683569509110397236258765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78455713006073598157505843 117683569509110397236258765)
    ·
      refine ⟨44131338565916398963597037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117683569509110397236258765 44131338565916398963597037)
      ·
        refine ⟨16549251962218649611348889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44131338565916398963597037 16549251962218649611348889)
        ·
          refine ⟨12411938971663987208511667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16549251962218649611348889 12411938971663987208511667)
          ·
            refine ⟨18617908457495980812767501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12411938971663987208511667 18617908457495980812767501)
            ·
              refine ⟨6981715671560992804787813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18617908457495980812767501 6981715671560992804787813)
              ·
                refine ⟨1309071688417686150897715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6981715671560992804787813 1309071688417686150897715)
                ·
                  refine ⟨1963607532626529226346573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1309071688417686150897715 1963607532626529226346573)
                  ·
                    refine ⟨736352824734948459879965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1963607532626529226346573 736352824734948459879965)
                    ·
                      rfl

theorem cell22_2151063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 4, 1, 3].length) (baseStart_2151063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2151063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2151063 prefixEnd_2151063 := by exact prefixLift 2151063
  have htrace : WordTrace (prefixWord ++ tailWord_2151063) baseStart_2151063 baseEnd_2151063 := by
    simpa [prefixWord, tailWord_2151063, baseEnd_2151063] using wordTrace_append hprefix tailTrace_2151063
  have hstable : (prefixWord ++ tailWord_2151063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151063).length < 2 ^ (prefixWord ++ tailWord_2151063).sum := by decide
  have hdescent : baseEnd_2151063 < baseStart_2151063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151110 : List Nat := [6, 1, 2, 1, 2, 1, 1, 1, 7]
def baseStart_2151110 : Nat := 118140960795 + 2151110 * 2 ^ 59
def prefixEnd_2151110 : Nat := 4983230072969 + 3 ^ 40 * 2151110 * 2
def baseEnd_2151110 : Nat := 245456304598485334651607

theorem tailTrace_2151110 : CollatzResearch.WordTrace tailWord_2151110 prefixEnd_2151110 245456304598485334651607 := by
  unfold tailWord_2151110
  simp only [CollatzResearch.WordTrace]
  refine ⟨2451794601153228912014587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 52304951491268883456311189 2451794601153228912014587)
  ·
    refine ⟨3677691901729843368021881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2451794601153228912014587 3677691901729843368021881)
    ·
      refine ⟨2758268926297382526016411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3677691901729843368021881 2758268926297382526016411)
      ·
        refine ⟨4137403389446073789024617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2758268926297382526016411 4137403389446073789024617)
        ·
          refine ⟨3103052542084555341768463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4137403389446073789024617 3103052542084555341768463)
          ·
            refine ⟨4654578813126833012652695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3103052542084555341768463 4654578813126833012652695)
            ·
              refine ⟨6981868219690249518979043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4654578813126833012652695 6981868219690249518979043)
              ·
                refine ⟨10472802329535374278468565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6981868219690249518979043 10472802329535374278468565)
                ·
                  refine ⟨245456304598485334651607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10472802329535374278468565 245456304598485334651607)
                  ·
                    rfl

theorem cell22_2151110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_2151110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2151110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2151110 prefixEnd_2151110 := by exact prefixLift 2151110
  have htrace : WordTrace (prefixWord ++ tailWord_2151110) baseStart_2151110 baseEnd_2151110 := by
    simpa [prefixWord, tailWord_2151110, baseEnd_2151110] using wordTrace_append hprefix tailTrace_2151110
  have hstable : (prefixWord ++ tailWord_2151110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151110).length < 2 ^ (prefixWord ++ tailWord_2151110).sum := by decide
  have hdescent : baseEnd_2151110 < baseStart_2151110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151121 : List Nat := [1, 2, 2, 1, 2, 3, 1, 6, 4]
def baseStart_2151121 : Nat := 118140960795 + 2151121 * 2 ^ 59
def prefixEnd_2151121 : Nat := 4983230072969 + 3 ^ 40 * 2151121 * 2
def baseEnd_2151121 : Nat := 245457559773418547309929

theorem tailTrace_2151121 : CollatzResearch.WordTrace tailWord_2151121 prefixEnd_2151121 245457559773418547309929 := by
  unfold tailWord_2151121
  simp only [CollatzResearch.WordTrace]
  refine ⟨78457828439863474063117217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52305218959908982708744811 78457828439863474063117217)
  ·
    refine ⟨58843371329897605547337913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78457828439863474063117217 58843371329897605547337913)
    ·
      refine ⟨44132528497423204160503435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58843371329897605547337913 44132528497423204160503435)
      ·
        refine ⟨66198792746134806240755153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44132528497423204160503435 66198792746134806240755153)
        ·
          refine ⟨49649094559601104680566365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66198792746134806240755153 49649094559601104680566365)
          ·
            refine ⟨18618410459850414255212387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49649094559601104680566365 18618410459850414255212387)
            ·
              refine ⟨27927615689775621382818581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18618410459850414255212387 27927615689775621382818581)
              ·
                refine ⟨1309106985458232252319621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27927615689775621382818581 1309106985458232252319621)
                ·
                  refine ⟨245457559773418547309929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1309106985458232252319621 245457559773418547309929)
                  ·
                    rfl

theorem cell22_2151121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 6, 4].length) (baseStart_2151121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2151121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2151121 prefixEnd_2151121 := by exact prefixLift 2151121
  have htrace : WordTrace (prefixWord ++ tailWord_2151121) baseStart_2151121 baseEnd_2151121 := by
    simpa [prefixWord, tailWord_2151121, baseEnd_2151121] using wordTrace_append hprefix tailTrace_2151121
  have hstable : (prefixWord ++ tailWord_2151121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151121).length < 2 ^ (prefixWord ++ tailWord_2151121).sum := by decide
  have hdescent : baseEnd_2151121 < baseStart_2151121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151166 : List Nat := [4, 2, 2, 1, 2, 1, 10]
def baseStart_2151166 : Nat := 118140960795 + 2151166 * 2 ^ 59
def prefixEnd_2151166 : Nat := 4983230072969 + 3 ^ 40 * 2151166 * 2
def baseEnd_2151166 : Nat := 27273632731107056464987

theorem tailTrace_2151166 : CollatzResearch.WordTrace tailWord_2151166 prefixEnd_2151166 27273632731107056464987 := by
  unfold tailWord_2151166
  simp only [CollatzResearch.WordTrace]
  refine ⟨9807433715587555843563169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52306313149800297832336901 9807433715587555843563169)
  ·
    refine ⟨7355575286690666882672377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9807433715587555843563169 7355575286690666882672377)
    ·
      refine ⟨5516681465018000162004283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7355575286690666882672377 5516681465018000162004283)
      ·
        refine ⟨8275022197527000243006425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5516681465018000162004283 8275022197527000243006425)
        ·
          refine ⟨6206266648145250182254819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8275022197527000243006425 6206266648145250182254819)
          ·
            refine ⟨9309399972217875273382229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6206266648145250182254819 9309399972217875273382229)
            ·
              refine ⟨27273632731107056464987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9309399972217875273382229 27273632731107056464987)
              ·
                rfl

theorem cell22_2151166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 10].length) (baseStart_2151166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2151166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2151166 prefixEnd_2151166 := by exact prefixLift 2151166
  have htrace : WordTrace (prefixWord ++ tailWord_2151166) baseStart_2151166 baseEnd_2151166 := by
    simpa [prefixWord, tailWord_2151166, baseEnd_2151166] using wordTrace_append hprefix tailTrace_2151166
  have hstable : (prefixWord ++ tailWord_2151166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151166).length < 2 ^ (prefixWord ++ tailWord_2151166).sum := by decide
  have hdescent : baseEnd_2151166 < baseStart_2151166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151179 : List Nat := [1, 1, 1, 1, 5, 1, 1, 3, 2, 6]
def baseStart_2151179 : Nat := 118140960795 + 2151179 * 2 ^ 59
def prefixEnd_2151179 : Nat := 4983230072969 + 3 ^ 40 * 2151179 * 2
def baseEnd_2151179 : Nat := 736392533905562823979609

theorem tailTrace_2151179 : CollatzResearch.WordTrace tailWord_2151179 prefixEnd_2151179 736392533905562823979609 := by
  unfold tailWord_2151179
  simp only [CollatzResearch.WordTrace]
  refine ⟨78459943873653349968728591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52306629249102233312485727 78459943873653349968728591)
  ·
    refine ⟨117689915810480024953092887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78459943873653349968728591 117689915810480024953092887)
    ·
      refine ⟨176534873715720037429639331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117689915810480024953092887 176534873715720037429639331)
      ·
        refine ⟨264802310573580056144458997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176534873715720037429639331 264802310573580056144458997)
        ·
          refine ⟨24825216616273130263543031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 264802310573580056144458997 24825216616273130263543031)
          ·
            refine ⟨37237824924409695395314547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24825216616273130263543031 37237824924409695395314547)
            ·
              refine ⟨55856737386614543092971821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37237824924409695395314547 55856737386614543092971821)
              ·
                refine ⟨20946276519980453659864433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55856737386614543092971821 20946276519980453659864433)
                ·
                  refine ⟨15709707389985340244898325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20946276519980453659864433 15709707389985340244898325)
                  ·
                    refine ⟨736392533905562823979609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15709707389985340244898325 736392533905562823979609)
                    ·
                      rfl

theorem cell22_2151179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 6].length) (baseStart_2151179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2151179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2151179 prefixEnd_2151179 := by exact prefixLift 2151179
  have htrace : WordTrace (prefixWord ++ tailWord_2151179) baseStart_2151179 baseEnd_2151179 := by
    simpa [prefixWord, tailWord_2151179, baseEnd_2151179] using wordTrace_append hprefix tailTrace_2151179
  have hstable : (prefixWord ++ tailWord_2151179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151179).length < 2 ^ (prefixWord ++ tailWord_2151179).sum := by decide
  have hdescent : baseEnd_2151179 < baseStart_2151179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151209 : List Nat := [1, 2, 1, 1, 1, 1, 1, 6, 1, 7]
def baseStart_2151209 : Nat := 118140960795 + 2151209 * 2 ^ 59
def prefixEnd_2151209 : Nat := 4983230072969 + 3 ^ 40 * 2151209 * 2
def baseEnd_2151209 : Nat := 736402803518652745729517

theorem tailTrace_2151209 : CollatzResearch.WordTrace tailWord_2151209 prefixEnd_2151209 736402803518652745729517 := by
  unfold tailWord_2151209
  simp only [CollatzResearch.WordTrace]
  refine ⟨78461038063544665092320681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52307358709029776728213787 78461038063544665092320681)
  ·
    refine ⟨58845778547658498819240511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78461038063544665092320681 58845778547658498819240511)
    ·
      refine ⟨88268667821487748228860767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58845778547658498819240511 88268667821487748228860767)
      ·
        refine ⟨132403001732231622343291151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88268667821487748228860767 132403001732231622343291151)
        ·
          refine ⟨198604502598347433514936727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132403001732231622343291151 198604502598347433514936727)
          ·
            refine ⟨297906753897521150272405091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198604502598347433514936727 297906753897521150272405091)
            ·
              refine ⟨446860130846281725408607637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 297906753897521150272405091 446860130846281725408607637)
              ·
                refine ⟨20946568633419455878528483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 446860130846281725408607637 20946568633419455878528483)
                ·
                  refine ⟨31419852950129183817792725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20946568633419455878528483 31419852950129183817792725)
                  ·
                    refine ⟨736402803518652745729517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31419852950129183817792725 736402803518652745729517)
                    ·
                      rfl

theorem cell22_2151209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 7].length) (baseStart_2151209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2151209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2151209 prefixEnd_2151209 := by exact prefixLift 2151209
  have htrace : WordTrace (prefixWord ++ tailWord_2151209) baseStart_2151209 baseEnd_2151209 := by
    simpa [prefixWord, tailWord_2151209, baseEnd_2151209] using wordTrace_append hprefix tailTrace_2151209
  have hstable : (prefixWord ++ tailWord_2151209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151209).length < 2 ^ (prefixWord ++ tailWord_2151209).sum := by decide
  have hdescent : baseEnd_2151209 < baseStart_2151209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151241 : List Nat := [1, 2, 1, 1, 2, 5, 1, 2, 3, 4]
def baseStart_2151241 : Nat := 118140960795 + 2151241 * 2 ^ 59
def prefixEnd_2151241 : Nat := 4983230072969 + 3 ^ 40 * 2151241 * 2
def baseEnd_2151241 : Nat := 736413757772615328929419

theorem tailTrace_2151241 : CollatzResearch.WordTrace tailWord_2151241 prefixEnd_2151241 736413757772615328929419 := by
  unfold tailWord_2151241
  simp only [CollatzResearch.WordTrace]
  refine ⟨78462205199428734557485577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52308136799619156371657051 78462205199428734557485577)
  ·
    refine ⟨58846653899571550918114183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78462205199428734557485577 58846653899571550918114183)
    ·
      refine ⟨88269980849357326377171275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58846653899571550918114183 88269980849357326377171275)
      ·
        refine ⟨132404971274035989565756913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88269980849357326377171275 132404971274035989565756913)
        ·
          refine ⟨99303728455526992174317685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132404971274035989565756913 99303728455526992174317685)
          ·
            refine ⟨9309724542705655516342283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 99303728455526992174317685 9309724542705655516342283)
            ·
              refine ⟨13964586814058483274513425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9309724542705655516342283 13964586814058483274513425)
              ·
                refine ⟨10473440110543862455885069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13964586814058483274513425 10473440110543862455885069)
                ·
                  refine ⟨3927540041453948420956901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10473440110543862455885069 3927540041453948420956901)
                  ·
                    refine ⟨736413757772615328929419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3927540041453948420956901 736413757772615328929419)
                    ·
                      rfl

theorem cell22_2151241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 4].length) (baseStart_2151241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2151241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2151241 prefixEnd_2151241 := by exact prefixLift 2151241
  have htrace : WordTrace (prefixWord ++ tailWord_2151241) baseStart_2151241 baseEnd_2151241 := by
    simpa [prefixWord, tailWord_2151241, baseEnd_2151241] using wordTrace_append hprefix tailTrace_2151241
  have hstable : (prefixWord ++ tailWord_2151241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151241).length < 2 ^ (prefixWord ++ tailWord_2151241).sum := by decide
  have hdescent : baseEnd_2151241 < baseStart_2151241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151288 : List Nat := [2, 1, 2, 1, 1, 1, 1, 8, 2, 3]
def baseStart_2151288 : Nat := 118140960795 + 2151288 * 2 ^ 59
def prefixEnd_2151288 : Nat := 4983230072969 + 3 ^ 40 * 2151288 * 2
def baseEnd_2151288 : Nat := 736429846833122873004275

theorem tailTrace_2151288 : CollatzResearch.WordTrace tailWord_2151288 prefixEnd_2151288 736429846833122873004275 := by
  unfold tailWord_2151288
  simp only [CollatzResearch.WordTrace]
  refine ⟨39231959715129230792223259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52309279620172307722964345 39231959715129230792223259)
  ·
    refine ⟨58847939572693846188334889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39231959715129230792223259 58847939572693846188334889)
    ·
      refine ⟨44135954679520384641251167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58847939572693846188334889 44135954679520384641251167)
      ·
        refine ⟨66203932019280576961876751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44135954679520384641251167 66203932019280576961876751)
        ·
          refine ⟨99305898028920865442815127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66203932019280576961876751 99305898028920865442815127)
          ·
            refine ⟨148958847043381298164222691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99305898028920865442815127 148958847043381298164222691)
            ·
              refine ⟨223438270565071947246334037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148958847043381298164222691 223438270565071947246334037)
              ·
                refine ⟨2618417233184436881792977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 223438270565071947246334037 2618417233184436881792977)
                ·
                  refine ⟨1963812924888327661344733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2618417233184436881792977 1963812924888327661344733)
                  ·
                    refine ⟨736429846833122873004275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1963812924888327661344733 736429846833122873004275)
                    ·
                      rfl

theorem cell22_2151288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 2, 3].length) (baseStart_2151288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2151288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2151288 prefixEnd_2151288 := by exact prefixLift 2151288
  have htrace : WordTrace (prefixWord ++ tailWord_2151288) baseStart_2151288 baseEnd_2151288 := by
    simpa [prefixWord, tailWord_2151288, baseEnd_2151288] using wordTrace_append hprefix tailTrace_2151288
  have hstable : (prefixWord ++ tailWord_2151288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151288).length < 2 ^ (prefixWord ++ tailWord_2151288).sum := by decide
  have hdescent : baseEnd_2151288 < baseStart_2151288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151324 : List Nat := [2, 2, 3, 3, 3, 1, 1, 3, 4]
def baseStart_2151324 : Nat := 118140960795 + 2151324 * 2 ^ 59
def prefixEnd_2151324 : Nat := 4983230072969 + 3 ^ 40 * 2151324 * 2
def baseEnd_2151324 : Nat := 245480723456276926368055

theorem tailTrace_2151324 : CollatzResearch.WordTrace tailWord_2151324 prefixEnd_2151324 245480723456276926368055 := by
  unfold tailWord_2151324
  simp only [CollatzResearch.WordTrace]
  refine ⟨39232616229064019866378513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52310154972085359821838017 39232616229064019866378513)
  ·
    refine ⟨29424462171798014899783885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39232616229064019866378513 29424462171798014899783885)
    ·
      refine ⟨11034173314424255587418957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29424462171798014899783885 11034173314424255587418957)
      ·
        refine ⟨4137814992909095845282109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11034173314424255587418957 4137814992909095845282109)
        ·
          refine ⟨1551680622340910941980791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4137814992909095845282109 1551680622340910941980791)
          ·
            refine ⟨2327520933511366412971187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1551680622340910941980791 2327520933511366412971187)
            ·
              refine ⟨3491281400267049619456781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2327520933511366412971187 3491281400267049619456781)
              ·
                refine ⟨1309230525100143607296293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3491281400267049619456781 1309230525100143607296293)
                ·
                  refine ⟨245480723456276926368055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1309230525100143607296293 245480723456276926368055)
                  ·
                    rfl

theorem cell22_2151324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 3, 4].length) (baseStart_2151324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2151324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2151324 prefixEnd_2151324 := by exact prefixLift 2151324
  have htrace : WordTrace (prefixWord ++ tailWord_2151324) baseStart_2151324 baseEnd_2151324 := by
    simpa [prefixWord, tailWord_2151324, baseEnd_2151324] using wordTrace_append hprefix tailTrace_2151324
  have hstable : (prefixWord ++ tailWord_2151324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151324).length < 2 ^ (prefixWord ++ tailWord_2151324).sum := by decide
  have hdescent : baseEnd_2151324 < baseStart_2151324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151335 : List Nat := [1, 1, 6, 1, 4, 1, 8]
def baseStart_2151335 : Nat := 118140960795 + 2151335 * 2 ^ 59
def prefixEnd_2151335 : Nat := 4983230072969 + 3 ^ 40 * 2151335 * 2
def baseEnd_2151335 : Nat := 27275775403467793225153

theorem tailTrace_2151335 : CollatzResearch.WordTrace tailWord_2151335 prefixEnd_2151335 27275775403467793225153 := by
  unfold tailWord_2151335
  simp only [CollatzResearch.WordTrace]
  refine ⟨78465633661088188611407459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52310422440725459074271639 78465633661088188611407459)
  ·
    refine ⟨117698450491632282917111189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78465633661088188611407459 117698450491632282917111189)
    ·
      refine ⟨5517114866795263261739587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 117698450491632282917111189 5517114866795263261739587)
      ·
        refine ⟨8275672300192894892609381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5517114866795263261739587 8275672300192894892609381)
        ·
          refine ⟨1551688556286167792364259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8275672300192894892609381 1551688556286167792364259)
          ·
            refine ⟨2327532834429251688546389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1551688556286167792364259 2327532834429251688546389)
            ·
              refine ⟨27275775403467793225153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2327532834429251688546389 27275775403467793225153)
              ·
                rfl

theorem cell22_2151335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 8].length) (baseStart_2151335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2151335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2151335 prefixEnd_2151335 := by exact prefixLift 2151335
  have htrace : WordTrace (prefixWord ++ tailWord_2151335) baseStart_2151335 baseEnd_2151335 := by
    simpa [prefixWord, tailWord_2151335, baseEnd_2151335] using wordTrace_append hprefix tailTrace_2151335
  have hstable : (prefixWord ++ tailWord_2151335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151335).length < 2 ^ (prefixWord ++ tailWord_2151335).sum := by decide
  have hdescent : baseEnd_2151335 < baseStart_2151335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151397 : List Nat := [1, 3, 1, 6, 1, 1, 2, 2, 5]
def baseStart_2151397 : Nat := 118140960795 + 2151397 * 2 ^ 59
def prefixEnd_2151397 : Nat := 4983230072969 + 3 ^ 40 * 2151397 * 2
def baseEnd_2151397 : Nat := 245489053253560974009647

theorem tailTrace_2151397 : CollatzResearch.WordTrace tailWord_2151397 prefixEnd_2151397 245489053253560974009647 := by
  unfold tailWord_2151397
  simp only [CollatzResearch.WordTrace]
  refine ⟨78467894986863573200164445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52311929991242382133442963 78467894986863573200164445)
  ·
    refine ⟨29425460620073839950061667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78467894986863573200164445 29425460620073839950061667)
    ·
      refine ⟨44138190930110759925092501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29425460620073839950061667 44138190930110759925092501)
      ·
        refine ⟨2068977699848941871488711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 44138190930110759925092501 2068977699848941871488711)
        ·
          refine ⟨3103466549773412807233067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2068977699848941871488711 3103466549773412807233067)
          ·
            refine ⟨4655199824660119210849601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3103466549773412807233067 4655199824660119210849601)
            ·
              refine ⟨3491399868495089408137201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4655199824660119210849601 3491399868495089408137201)
              ·
                refine ⟨2618549901371317056102901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3491399868495089408137201 2618549901371317056102901)
                ·
                  refine ⟨245489053253560974009647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2618549901371317056102901 245489053253560974009647)
                  ·
                    rfl

theorem cell22_2151397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 5].length) (baseStart_2151397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2151397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2151397 prefixEnd_2151397 := by exact prefixLift 2151397
  have htrace : WordTrace (prefixWord ++ tailWord_2151397) baseStart_2151397 baseEnd_2151397 := by
    simpa [prefixWord, tailWord_2151397, baseEnd_2151397] using wordTrace_append hprefix tailTrace_2151397
  have hstable : (prefixWord ++ tailWord_2151397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151397).length < 2 ^ (prefixWord ++ tailWord_2151397).sum := by decide
  have hdescent : baseEnd_2151397 < baseStart_2151397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151423 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 8, 3]
def baseStart_2151423 : Nat := 118140960795 + 2151423 * 2 ^ 59
def prefixEnd_2151423 : Nat := 4983230072969 + 3 ^ 40 * 2151423 * 2
def baseEnd_2151423 : Nat := 736476060092027520878861

theorem tailTrace_2151423 : CollatzResearch.WordTrace tailWord_2151423 prefixEnd_2151423 736476060092027520878861 := by
  unfold tailWord_2151423
  simp only [CollatzResearch.WordTrace]
  refine ⟨78468843284769379640610923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52312562189846253093740615 78468843284769379640610923)
  ·
    refine ⟨117703264927154069460916385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78468843284769379640610923 117703264927154069460916385)
    ·
      refine ⟨88277448695365552095687289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117703264927154069460916385 88277448695365552095687289)
      ·
        refine ⟨66208086521524164071765467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88277448695365552095687289 66208086521524164071765467)
        ·
          refine ⟨99312129782286246107648201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66208086521524164071765467 99312129782286246107648201)
          ·
            refine ⟨74484097336714684580736151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99312129782286246107648201 74484097336714684580736151)
            ·
              refine ⟨111726146005072026871104227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74484097336714684580736151 111726146005072026871104227)
              ·
                refine ⟨167589219007608040306656341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111726146005072026871104227 167589219007608040306656341)
                ·
                  refine ⟨1963936160245406722343629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 167589219007608040306656341 1963936160245406722343629)
                  ·
                    refine ⟨736476060092027520878861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1963936160245406722343629 736476060092027520878861)
                    ·
                      rfl

theorem cell22_2151423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 8, 3].length) (baseStart_2151423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2151423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2151423 prefixEnd_2151423 := by exact prefixLift 2151423
  have htrace : WordTrace (prefixWord ++ tailWord_2151423) baseStart_2151423 baseEnd_2151423 := by
    simpa [prefixWord, tailWord_2151423, baseEnd_2151423] using wordTrace_append hprefix tailTrace_2151423
  have hstable : (prefixWord ++ tailWord_2151423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151423).length < 2 ^ (prefixWord ++ tailWord_2151423).sum := by decide
  have hdescent : baseEnd_2151423 < baseStart_2151423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151457 : List Nat := [1, 2, 3, 2, 3, 1, 3, 2, 2, 3]
def baseStart_2151457 : Nat := 118140960795 + 2151457 * 2 ^ 59
def prefixEnd_2151457 : Nat := 4983230072969 + 3 ^ 40 * 2151457 * 2
def baseEnd_2151457 : Nat := 736487698986862765528757

theorem tailTrace_2151457 : CollatzResearch.WordTrace tailWord_2151457 prefixEnd_2151457 736487698986862765528757 := by
  unfold tailWord_2151457
  simp only [CollatzResearch.WordTrace]
  refine ⟨78470083366646203447348625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52313388911097468964899083 78470083366646203447348625)
  ·
    refine ⟨58852562524984652585511469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78470083366646203447348625 58852562524984652585511469)
    ·
      refine ⟨22069710946869244719566801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58852562524984652585511469 22069710946869244719566801)
      ·
        refine ⟨16552283210151933539675101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22069710946869244719566801 16552283210151933539675101)
        ·
          refine ⟨6207106203806975077378163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16552283210151933539675101 6207106203806975077378163)
          ·
            refine ⟨9310659305710462616067245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6207106203806975077378163 9310659305710462616067245)
            ·
              refine ⟨3491497239641423481025217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9310659305710462616067245 3491497239641423481025217)
              ·
                refine ⟨2618622929731067610768913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3491497239641423481025217 2618622929731067610768913)
                ·
                  refine ⟨1963967197298300708076685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2618622929731067610768913 1963967197298300708076685)
                  ·
                    refine ⟨736487698986862765528757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1963967197298300708076685 736487698986862765528757)
                    ·
                      rfl

theorem cell22_2151457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_2151457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2151457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2151457 prefixEnd_2151457 := by exact prefixLift 2151457
  have htrace : WordTrace (prefixWord ++ tailWord_2151457) baseStart_2151457 baseEnd_2151457 := by
    simpa [prefixWord, tailWord_2151457, baseEnd_2151457] using wordTrace_append hprefix tailTrace_2151457
  have hstable : (prefixWord ++ tailWord_2151457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151457).length < 2 ^ (prefixWord ++ tailWord_2151457).sum := by decide
  have hdescent : baseEnd_2151457 < baseStart_2151457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151498 : List Nat := [3, 1, 2, 1, 1, 2, 3, 2, 7]
def baseStart_2151498 : Nat := 118140960795 + 2151498 * 2 ^ 59
def prefixEnd_2151498 : Nat := 4983230072969 + 3 ^ 40 * 2151498 * 2
def baseEnd_2151498 : Nat := 245500578041584108417877

theorem tailTrace_2151498 : CollatzResearch.WordTrace tailWord_2151498 prefixEnd_2151498 245500578041584108417877 := by
  unfold tailWord_2151498
  simp only [CollatzResearch.WordTrace]
  refine ⟨19617894689874416862397787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52314385839665111633060765 19617894689874416862397787)
  ·
    refine ⟨29426842034811625293596681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19617894689874416862397787 29426842034811625293596681)
    ·
      refine ⟨22070131526108718970197511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29426842034811625293596681 22070131526108718970197511)
      ·
        refine ⟨33105197289163078455296267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22070131526108718970197511 33105197289163078455296267)
        ·
          refine ⟨49657795933744617682944401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33105197289163078455296267 49657795933744617682944401)
          ·
            refine ⟨37243346950308463262208301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49657795933744617682944401 37243346950308463262208301)
            ·
              refine ⟨13966255106365673723328113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37243346950308463262208301 13966255106365673723328113)
              ·
                refine ⟨10474691329774255292496085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13966255106365673723328113 10474691329774255292496085)
                ·
                  refine ⟨245500578041584108417877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10474691329774255292496085 245500578041584108417877)
                  ·
                    rfl

theorem cell22_2151498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 7].length) (baseStart_2151498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2151498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2151498 prefixEnd_2151498 := by exact prefixLift 2151498
  have htrace : WordTrace (prefixWord ++ tailWord_2151498) baseStart_2151498 baseEnd_2151498 := by
    simpa [prefixWord, tailWord_2151498, baseEnd_2151498] using wordTrace_append hprefix tailTrace_2151498
  have hstable : (prefixWord ++ tailWord_2151498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151498).length < 2 ^ (prefixWord ++ tailWord_2151498).sum := by decide
  have hdescent : baseEnd_2151498 < baseStart_2151498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151513 : List Nat := [1, 2, 1, 2, 2, 1, 2, 4, 2, 5]
def baseStart_2151513 : Nat := 118140960795 + 2151513 * 2 ^ 59
def prefixEnd_2151513 : Nat := 4983230072969 + 3 ^ 40 * 2151513 * 2
def baseEnd_2151513 : Nat := 736506868931297286128585

theorem tailTrace_2151513 : CollatzResearch.WordTrace tailWord_2151513 prefixEnd_2151513 736506868931297286128585 := by
  unfold tailWord_2151513
  simp only [CollatzResearch.WordTrace]
  refine ⟨78472125854443325011387193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52314750569628883340924795 78472125854443325011387193)
  ·
    refine ⟨58854094390832493758540395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78472125854443325011387193 58854094390832493758540395)
    ·
      refine ⟨88281141586248740637810593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58854094390832493758540395 88281141586248740637810593)
      ·
        refine ⟨66210856189686555478357945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88281141586248740637810593 66210856189686555478357945)
        ·
          refine ⟨49658142142264916608768459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66210856189686555478357945 49658142142264916608768459)
          ·
            refine ⟨74487213213397374913152689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49658142142264916608768459 74487213213397374913152689)
            ·
              refine ⟨55865409910048031184864517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74487213213397374913152689 55865409910048031184864517)
              ·
                refine ⟨10474764358134005847162097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55865409910048031184864517 10474764358134005847162097)
                ·
                  refine ⟨7856073268600504385371573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10474764358134005847162097 7856073268600504385371573)
                  ·
                    refine ⟨736506868931297286128585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7856073268600504385371573 736506868931297286128585)
                    ·
                      rfl

theorem cell22_2151513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 5].length) (baseStart_2151513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2151513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2151513 prefixEnd_2151513 := by exact prefixLift 2151513
  have htrace : WordTrace (prefixWord ++ tailWord_2151513) baseStart_2151513 baseEnd_2151513 := by
    simpa [prefixWord, tailWord_2151513, baseEnd_2151513] using wordTrace_append hprefix tailTrace_2151513
  have hstable : (prefixWord ++ tailWord_2151513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151513).length < 2 ^ (prefixWord ++ tailWord_2151513).sum := by decide
  have hdescent : baseEnd_2151513 < baseStart_2151513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151519 : List Nat := [1, 1, 2, 3, 1, 1, 7, 2, 1, 3]
def baseStart_2151519 : Nat := 118140960795 + 2151519 * 2 ^ 59
def prefixEnd_2151519 : Nat := 4983230072969 + 3 ^ 40 * 2151519 * 2
def baseEnd_2151519 : Nat := 736508922853915270478567

theorem tailTrace_2151519 : CollatzResearch.WordTrace tailWord_2151519 prefixEnd_2151519 736508922853915270478567 := by
  unfold tailWord_2151519
  simp only [CollatzResearch.WordTrace]
  refine ⟨78472344692421588036105611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52314896461614392024070407 78472344692421588036105611)
  ·
    refine ⟨117708517038632382054158417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78472344692421588036105611 117708517038632382054158417)
    ·
      refine ⟨88281387778974286540618813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117708517038632382054158417 88281387778974286540618813)
      ·
        refine ⟨33105520417115357452732055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88281387778974286540618813 33105520417115357452732055)
        ·
          refine ⟨49658280625673036179098083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33105520417115357452732055 49658280625673036179098083)
          ·
            refine ⟨74487420938509554268647125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49658280625673036179098083 74487420938509554268647125)
            ·
              refine ⟨1745798928246317678171417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 74487420938509554268647125 1745798928246317678171417)
              ·
                refine ⟨1309349196184738258628563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1745798928246317678171417 1309349196184738258628563)
                ·
                  refine ⟨1964023794277107387942845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1309349196184738258628563 1964023794277107387942845)
                  ·
                    refine ⟨736508922853915270478567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1964023794277107387942845 736508922853915270478567)
                    ·
                      rfl

theorem cell22_2151519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 2, 1, 3].length) (baseStart_2151519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2151519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2151519 prefixEnd_2151519 := by exact prefixLift 2151519
  have htrace : WordTrace (prefixWord ++ tailWord_2151519) baseStart_2151519 baseEnd_2151519 := by
    simpa [prefixWord, tailWord_2151519, baseEnd_2151519] using wordTrace_append hprefix tailTrace_2151519
  have hstable : (prefixWord ++ tailWord_2151519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151519).length < 2 ^ (prefixWord ++ tailWord_2151519).sum := by decide
  have hdescent : baseEnd_2151519 < baseStart_2151519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151543 : List Nat := [1, 1, 3, 1, 1, 4, 2, 1, 8]
def baseStart_2151543 : Nat := 118140960795 + 2151543 * 2 ^ 59
def prefixEnd_2151543 : Nat := 4983230072969 + 3 ^ 40 * 2151543 * 2
def baseEnd_2151543 : Nat := 245505712848129069292831

theorem tailTrace_2151543 : CollatzResearch.WordTrace tailWord_2151543 prefixEnd_2151543 245505712848129069292831 := by
  unfold tailWord_2151543
  simp only [CollatzResearch.WordTrace]
  refine ⟨78473220044334640134979283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52315480029556426756652855 78473220044334640134979283)
  ·
    refine ⟨117709830066501960202468925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78473220044334640134979283 117709830066501960202468925)
    ·
      refine ⟨44141186274938235075925847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117709830066501960202468925 44141186274938235075925847)
      ·
        refine ⟨66211779412407352613888771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44141186274938235075925847 66211779412407352613888771)
        ·
          refine ⟨99317669118611028920833157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66211779412407352613888771 99317669118611028920833157)
          ·
            refine ⟨18622062959739567922656217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99317669118611028920833157 18622062959739567922656217)
            ·
              refine ⟨13966547219804675941992163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18622062959739567922656217 13966547219804675941992163)
              ·
                refine ⟨20949820829707013912988245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13966547219804675941992163 20949820829707013912988245)
                ·
                  refine ⟨245505712848129069292831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20949820829707013912988245 245505712848129069292831)
                  ·
                    rfl

theorem cell22_2151543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 8].length) (baseStart_2151543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2151543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2151543 prefixEnd_2151543 := by exact prefixLift 2151543
  have htrace : WordTrace (prefixWord ++ tailWord_2151543) baseStart_2151543 baseEnd_2151543 := by
    simpa [prefixWord, tailWord_2151543, baseEnd_2151543] using wordTrace_append hprefix tailTrace_2151543
  have hstable : (prefixWord ++ tailWord_2151543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151543).length < 2 ^ (prefixWord ++ tailWord_2151543).sum := by decide
  have hdescent : baseEnd_2151543 < baseStart_2151543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151680 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 5, 4]
def baseStart_2151680 : Nat := 118140960795 + 2151680 * 2 ^ 59
def prefixEnd_2151680 : Nat := 4983230072969 + 3 ^ 40 * 2151680 * 2
def baseEnd_2151680 : Nat := 736564036444164517203073

theorem tailTrace_2151680 : CollatzResearch.WordTrace tailWord_2151680 prefixEnd_2151680 736564036444164517203073 := by
  unfold tailWord_2151680
  simp only [CollatzResearch.WordTrace]
  refine ⟨39239108422419156266358247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52318811229892208355144329 39239108422419156266358247)
  ·
    refine ⟨58858662633628734399537371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39239108422419156266358247 58858662633628734399537371)
    ·
      refine ⟨88287993950443101599306057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58858662633628734399537371 88287993950443101599306057)
      ·
        refine ⟨66215995462832326199479543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88287993950443101599306057 66215995462832326199479543)
        ·
          refine ⟨99323993194248489299219315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66215995462832326199479543 99323993194248489299219315)
          ·
            refine ⟨148985989791372733948828973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99323993194248489299219315 148985989791372733948828973)
            ·
              refine ⟨55869746171764775230810865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148985989791372733948828973 55869746171764775230810865)
              ·
                refine ⟨41902309628823581423108149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55869746171764775230810865 41902309628823581423108149)
                ·
                  refine ⟨3928341527702210758416389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41902309628823581423108149 3928341527702210758416389)
                  ·
                    refine ⟨736564036444164517203073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3928341527702210758416389 736564036444164517203073)
                    ·
                      rfl

theorem cell22_2151680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 5, 4].length) (baseStart_2151680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2151680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2151680 prefixEnd_2151680 := by exact prefixLift 2151680
  have htrace : WordTrace (prefixWord ++ tailWord_2151680) baseStart_2151680 baseEnd_2151680 := by
    simpa [prefixWord, tailWord_2151680, baseEnd_2151680] using wordTrace_append hprefix tailTrace_2151680
  have hstable : (prefixWord ++ tailWord_2151680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151680).length < 2 ^ (prefixWord ++ tailWord_2151680).sum := by decide
  have hdescent : baseEnd_2151680 < baseStart_2151680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151688 : List Nat := [2, 1, 3, 2, 4, 1, 3, 2, 1, 3]
def baseStart_2151688 : Nat := 118140960795 + 2151688 * 2 ^ 59
def prefixEnd_2151688 : Nat := 4983230072969 + 3 ^ 40 * 2151688 * 2
def baseEnd_2151688 : Nat := 736566775007655163003049

theorem tailTrace_2151688 : CollatzResearch.WordTrace tailWord_2151688 prefixEnd_2151688 736566775007655163003049 := by
  unfold tailWord_2151688
  simp only [CollatzResearch.WordTrace]
  refine ⟨39239254314404664949503859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52319005752539553266005145 39239254314404664949503859)
  ·
    refine ⟨58858881471606997424255789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39239254314404664949503859 58858881471606997424255789)
    ·
      refine ⟨22072080551852624034095921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58858881471606997424255789 22072080551852624034095921)
      ·
        refine ⟨16554060413889468025571941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22072080551852624034095921 16554060413889468025571941)
        ·
          refine ⟨3103886327604275254794739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16554060413889468025571941 3103886327604275254794739)
          ·
            refine ⟨4655829491406412882192109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3103886327604275254794739 4655829491406412882192109)
            ·
              refine ⟨1745936059277404830822041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4655829491406412882192109 1745936059277404830822041)
              ·
                refine ⟨1309452044458053623116531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1745936059277404830822041 1309452044458053623116531)
                ·
                  refine ⟨1964178066687080434674797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1309452044458053623116531 1964178066687080434674797)
                  ·
                    refine ⟨736566775007655163003049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1964178066687080434674797 736566775007655163003049)
                    ·
                      rfl

theorem cell22_2151688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 2, 1, 3].length) (baseStart_2151688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2151688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2151688 prefixEnd_2151688 := by exact prefixLift 2151688
  have htrace : WordTrace (prefixWord ++ tailWord_2151688) baseStart_2151688 baseEnd_2151688 := by
    simpa [prefixWord, tailWord_2151688, baseEnd_2151688] using wordTrace_append hprefix tailTrace_2151688
  have hstable : (prefixWord ++ tailWord_2151688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151688).length < 2 ^ (prefixWord ++ tailWord_2151688).sum := by decide
  have hdescent : baseEnd_2151688 < baseStart_2151688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151714 : List Nat := [3, 3, 1, 1, 4, 1, 1, 1, 3, 4]
def baseStart_2151714 : Nat := 118140960795 + 2151714 * 2 ^ 59
def prefixEnd_2151714 : Nat := 4983230072969 + 3 ^ 40 * 2151714 * 2
def baseEnd_2151714 : Nat := 736575675338999761852969

theorem tailTrace_2151714 : CollatzResearch.WordTrace tailWord_2151714 prefixEnd_2151714 736575675338999761852969 := by
  unfold tailWord_2151714
  simp only [CollatzResearch.WordTrace]
  refine ⟨19619864231678784084863549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52319637951143424226302797 19619864231678784084863549)
  ·
    refine ⟨7357449086879544031823831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19619864231678784084863549 7357449086879544031823831)
    ·
      refine ⟨11036173630319316047735747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7357449086879544031823831 11036173630319316047735747)
      ·
        refine ⟨16554260445478974071603621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11036173630319316047735747 16554260445478974071603621)
        ·
          refine ⟨3103923833527307638425679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16554260445478974071603621 3103923833527307638425679)
          ·
            refine ⟨4655885750290961457638519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3103923833527307638425679 4655885750290961457638519)
            ·
              refine ⟨6983828625436442186457779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4655885750290961457638519 6983828625436442186457779)
              ·
                refine ⟨10475742938154663279686669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6983828625436442186457779 10475742938154663279686669)
                ·
                  refine ⟨3928403601807998729882501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10475742938154663279686669 3928403601807998729882501)
                  ·
                    refine ⟨736575675338999761852969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3928403601807998729882501 736575675338999761852969)
                    ·
                      rfl

theorem cell22_2151714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_2151714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2151714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2151714 prefixEnd_2151714 := by exact prefixLift 2151714
  have htrace : WordTrace (prefixWord ++ tailWord_2151714) baseStart_2151714 baseEnd_2151714 := by
    simpa [prefixWord, tailWord_2151714, baseEnd_2151714] using wordTrace_append hprefix tailTrace_2151714
  have hstable : (prefixWord ++ tailWord_2151714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151714).length < 2 ^ (prefixWord ++ tailWord_2151714).sum := by decide
  have hdescent : baseEnd_2151714 < baseStart_2151714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151740 : List Nat := [2, 2, 2, 2, 1, 13]
def baseStart_2151740 : Nat := 118140960795 + 2151740 * 2 ^ 59
def prefixEnd_2151740 : Nat := 4983230072969 + 3 ^ 40 * 2151740 * 2
def baseEnd_2151740 : Nat := 9093636736670918033369

theorem tailTrace_2151740 : CollatzResearch.WordTrace tailWord_2151740 prefixEnd_2151740 9093636736670918033369 := by
  unfold tailWord_2151740
  simp only [CollatzResearch.WordTrace]
  refine ⟨39240202612310471389950337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52320270149747295186600449 39240202612310471389950337)
  ·
    refine ⟨29430151959232853542462753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39240202612310471389950337 29430151959232853542462753)
    ·
      refine ⟨22072613969424640156847065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29430151959232853542462753 22072613969424640156847065)
      ·
        refine ⟨16554460477068480117635299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22072613969424640156847065 16554460477068480117635299)
        ·
          refine ⟨24831690715602720176452949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16554460477068480117635299 24831690715602720176452949)
          ·
            refine ⟨9093636736670918033369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 24831690715602720176452949 9093636736670918033369)
            ·
              rfl

theorem cell22_2151740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 13].length) (baseStart_2151740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2151740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2151740 prefixEnd_2151740 := by exact prefixLift 2151740
  have htrace : WordTrace (prefixWord ++ tailWord_2151740) baseStart_2151740 baseEnd_2151740 := by
    simpa [prefixWord, tailWord_2151740, baseEnd_2151740] using wordTrace_append hprefix tailTrace_2151740
  have hstable : (prefixWord ++ tailWord_2151740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151740).length < 2 ^ (prefixWord ++ tailWord_2151740).sum := by decide
  have hdescent : baseEnd_2151740 < baseStart_2151740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151744 : List Nat := [2, 1, 1, 2, 2, 1, 6, 2, 2, 3]
def baseStart_2151744 : Nat := 118140960795 + 2151744 * 2 ^ 59
def prefixEnd_2151744 : Nat := 4983230072969 + 3 ^ 40 * 2151744 * 2
def baseEnd_2151744 : Nat := 736585944952089683602877

theorem tailTrace_2151744 : CollatzResearch.WordTrace tailWord_2151744 prefixEnd_2151744 736585944952089683602877 := by
  unfold tailWord_2151744
  simp only [CollatzResearch.WordTrace]
  refine ⟨39240275558303225731523143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52320367411070967642030857 39240275558303225731523143)
  ·
    refine ⟨58860413337454838597284715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39240275558303225731523143 58860413337454838597284715)
    ·
      refine ⟨88290620006182257895927073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58860413337454838597284715 88290620006182257895927073)
      ·
        refine ⟨66217965004636693421945305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88290620006182257895927073 66217965004636693421945305)
        ·
          refine ⟨49663473753477520066458979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66217965004636693421945305 49663473753477520066458979)
          ·
            refine ⟨74495210630216280099688469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49663473753477520066458979 74495210630216280099688469)
            ·
              refine ⟨3491962998291388129672897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 74495210630216280099688469 3491962998291388129672897)
              ·
                refine ⟨2618972248718541097254673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3491962998291388129672897 2618972248718541097254673)
                ·
                  refine ⟨1964229186538905822941005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2618972248718541097254673 1964229186538905822941005)
                  ·
                    refine ⟨736585944952089683602877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1964229186538905822941005 736585944952089683602877)
                    ·
                      rfl

theorem cell22_2151744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 2, 3].length) (baseStart_2151744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2151744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2151744 prefixEnd_2151744 := by exact prefixLift 2151744
  have htrace : WordTrace (prefixWord ++ tailWord_2151744) baseStart_2151744 baseEnd_2151744 := by
    simpa [prefixWord, tailWord_2151744, baseEnd_2151744] using wordTrace_append hprefix tailTrace_2151744
  have hstable : (prefixWord ++ tailWord_2151744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151744).length < 2 ^ (prefixWord ++ tailWord_2151744).sum := by decide
  have hdescent : baseEnd_2151744 < baseStart_2151744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151819 : List Nat := [1, 1, 1, 1, 4, 3, 5, 1, 5]
def baseStart_2151819 : Nat := 118140960795 + 2151819 * 2 ^ 59
def prefixEnd_2151819 : Nat := 4983230072969 + 3 ^ 40 * 2151819 * 2
def baseEnd_2151819 : Nat := 245537206328271495992549

theorem tailTrace_2151819 : CollatzResearch.WordTrace tailWord_2151819 prefixEnd_2151819 245537206328271495992549 := by
  unfold tailWord_2151819
  simp only [CollatzResearch.WordTrace]
  refine ⟨78483286591334739272026511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52322191060889826181351007 78483286591334739272026511)
  ·
    refine ⟨117724929887002108908039767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78483286591334739272026511 117724929887002108908039767)
    ·
      refine ⟨176587394830503163362059651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117724929887002108908039767 176587394830503163362059651)
      ·
        refine ⟨264881092245754745043089477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176587394830503163362059651 264881092245754745043089477)
        ·
          refine ⟨49665204796079014695579277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 264881092245754745043089477 49665204796079014695579277)
          ·
            refine ⟨18624451798529630510842229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49665204796079014695579277 18624451798529630510842229)
            ·
              refine ⟨1746042356112152860391459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18624451798529630510842229 1746042356112152860391459)
              ·
                refine ⟨2619063534168229290587189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1746042356112152860391459 2619063534168229290587189)
                ·
                  refine ⟨245537206328271495992549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2619063534168229290587189 245537206328271495992549)
                  ·
                    rfl

theorem cell22_2151819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 5].length) (baseStart_2151819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2151819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2151819 prefixEnd_2151819 := by exact prefixLift 2151819
  have htrace : WordTrace (prefixWord ++ tailWord_2151819) baseStart_2151819 baseEnd_2151819 := by
    simpa [prefixWord, tailWord_2151819, baseEnd_2151819] using wordTrace_append hprefix tailTrace_2151819
  have hstable : (prefixWord ++ tailWord_2151819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151819).length < 2 ^ (prefixWord ++ tailWord_2151819).sum := by decide
  have hdescent : baseEnd_2151819 < baseStart_2151819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151864 : List Nat := [2, 1, 2, 1, 2, 2, 2, 6, 4]
def baseStart_2151864 : Nat := 118140960795 + 2151864 * 2 ^ 59
def prefixEnd_2151864 : Nat := 4983230072969 + 3 ^ 40 * 2151864 * 2
def baseEnd_2151864 : Nat := 245542341134816456867503

theorem tailTrace_2151864 : CollatzResearch.WordTrace tailWord_2151864 prefixEnd_2151864 245542341134816456867503 := by
  unfold tailWord_2151864
  simp only [CollatzResearch.WordTrace]
  refine ⟨39242463938085855978707323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52323285250781141304943097 39242463938085855978707323)
  ·
    refine ⟨58863695907128783968060985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39242463938085855978707323 58863695907128783968060985)
    ·
      refine ⟨44147771930346587976045739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58863695907128783968060985 44147771930346587976045739)
      ·
        refine ⟨66221657895519881964068609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44147771930346587976045739 66221657895519881964068609)
        ·
          refine ⟨49666243421639911473051457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66221657895519881964068609 49666243421639911473051457)
          ·
            refine ⟨37249682566229933604788593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49666243421639911473051457 37249682566229933604788593)
            ·
              refine ⟨27937261924672450203591445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37249682566229933604788593 27937261924672450203591445)
              ·
                refine ⟨1309559152719021103293349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27937261924672450203591445 1309559152719021103293349)
                ·
                  refine ⟨245542341134816456867503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1309559152719021103293349 245542341134816456867503)
                  ·
                    rfl

theorem cell22_2151864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 6, 4].length) (baseStart_2151864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2151864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2151864 prefixEnd_2151864 := by exact prefixLift 2151864
  have htrace : WordTrace (prefixWord ++ tailWord_2151864) baseStart_2151864 baseEnd_2151864 := by
    simpa [prefixWord, tailWord_2151864, baseEnd_2151864] using wordTrace_append hprefix tailTrace_2151864
  have hstable : (prefixWord ++ tailWord_2151864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151864).length < 2 ^ (prefixWord ++ tailWord_2151864).sum := by decide
  have hdescent : baseEnd_2151864 < baseStart_2151864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151926 : List Nat := [5, 1, 1, 1, 2, 4, 1, 7]
def baseStart_2151926 : Nat := 118140960795 + 2151926 * 2 ^ 59
def prefixEnd_2151926 : Nat := 4983230072969 + 3 ^ 40 * 2151926 * 2
def baseEnd_2151926 : Nat := 81849805252389097283591

theorem tailTrace_2151926 : CollatzResearch.WordTrace tailWord_2151926 prefixEnd_2151926 81849805252389097283591 := by
  unfold tailWord_2151926
  simp only [CollatzResearch.WordTrace]
  refine ⟨4905449325121693534135727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52324792801298064364114421 4905449325121693534135727)
  ·
    refine ⟨7358173987682540301203591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4905449325121693534135727 7358173987682540301203591)
    ·
      refine ⟨11037260981523810451805387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7358173987682540301203591 11037260981523810451805387)
      ·
        refine ⟨16555891472285715677708081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11037260981523810451805387 16555891472285715677708081)
        ·
          refine ⟨12416918604214286758281061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16555891472285715677708081 12416918604214286758281061)
          ·
            refine ⟨2328172238290178767177699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12416918604214286758281061 2328172238290178767177699)
            ·
              refine ⟨3492258357435268150766549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2328172238290178767177699 3492258357435268150766549)
              ·
                refine ⟨81849805252389097283591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3492258357435268150766549 81849805252389097283591)
                ·
                  rfl

theorem cell22_2151926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_2151926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2151926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2151926 prefixEnd_2151926 := by exact prefixLift 2151926
  have htrace : WordTrace (prefixWord ++ tailWord_2151926) baseStart_2151926 baseEnd_2151926 := by
    simpa [prefixWord, tailWord_2151926, baseEnd_2151926] using wordTrace_append hprefix tailTrace_2151926
  have hstable : (prefixWord ++ tailWord_2151926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151926).length < 2 ^ (prefixWord ++ tailWord_2151926).sum := by decide
  have hdescent : baseEnd_2151926 < baseStart_2151926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151969 : List Nat := [1, 2, 3, 2, 2, 2, 1, 2, 2, 5]
def baseStart_2151969 : Nat := 118140960795 + 2151969 * 2 ^ 59
def prefixEnd_2151969 : Nat := 4983230072969 + 3 ^ 40 * 2151969 * 2
def baseEnd_2151969 : Nat := 736662967050264096727187

theorem tailTrace_2151969 : CollatzResearch.WordTrace tailWord_2151969 prefixEnd_2151969 736662967050264096727187 := by
  unfold tailWord_2151969
  simp only [CollatzResearch.WordTrace]
  refine ⟨78488757540791314889986961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52325838360527543259991307 78488757540791314889986961)
  ·
    refine ⟨58866568155593486167490221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78488757540791314889986961 58866568155593486167490221)
    ·
      refine ⟨22074963058347557312808833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58866568155593486167490221 22074963058347557312808833)
      ·
        refine ⟨16556222293760667984606625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22074963058347557312808833 16556222293760667984606625)
        ·
          refine ⟨12417166720320500988454969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16556222293760667984606625 12417166720320500988454969)
          ·
            refine ⟨9312875040240375741341227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12417166720320500988454969 9312875040240375741341227)
            ·
              refine ⟨13969312560360563612011841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9312875040240375741341227 13969312560360563612011841)
              ·
                refine ⟨10476984420270422709008881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13969312560360563612011841 10476984420270422709008881)
                ·
                  refine ⟨7857738315202817031756661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10476984420270422709008881 7857738315202817031756661)
                  ·
                    refine ⟨736662967050264096727187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7857738315202817031756661 736662967050264096727187)
                    ·
                      rfl

theorem cell22_2151969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_2151969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2151969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2151969 prefixEnd_2151969 := by exact prefixLift 2151969
  have htrace : WordTrace (prefixWord ++ tailWord_2151969) baseStart_2151969 baseEnd_2151969 := by
    simpa [prefixWord, tailWord_2151969, baseEnd_2151969] using wordTrace_append hprefix tailTrace_2151969
  have hstable : (prefixWord ++ tailWord_2151969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151969).length < 2 ^ (prefixWord ++ tailWord_2151969).sum := by decide
  have hdescent : baseEnd_2151969 < baseStart_2151969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151999 : List Nat := [1, 1, 2, 2, 3, 3, 2, 2, 6]
def baseStart_2151999 : Nat := 118140960795 + 2151999 * 2 ^ 59
def prefixEnd_2151999 : Nat := 4983230072969 + 3 ^ 40 * 2151999 * 2
def baseEnd_2151999 : Nat := 245557745554451339492365

theorem tailTrace_2151999 : CollatzResearch.WordTrace tailWord_2151999 prefixEnd_2151999 245557745554451339492365 := by
  unfold tailWord_2151999
  simp only [CollatzResearch.WordTrace]
  refine ⟨78489851730682630013579051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52326567820455086675719367 78489851730682630013579051)
  ·
    refine ⟨117734777596023945020368577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78489851730682630013579051 117734777596023945020368577)
    ·
      refine ⟨88301083197017958765276433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117734777596023945020368577 88301083197017958765276433)
      ·
        refine ⟨66225812397763469073957325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88301083197017958765276433 66225812397763469073957325)
        ·
          refine ⟨24834679649161300902733997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66225812397763469073957325 24834679649161300902733997)
          ·
            refine ⟨9313004868435487838525249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24834679649161300902733997 9313004868435487838525249)
            ·
              refine ⟨6984753651326615878893937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9313004868435487838525249 6984753651326615878893937)
              ·
                refine ⟨5238565238494961909170453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6984753651326615878893937 5238565238494961909170453)
                ·
                  refine ⟨245557745554451339492365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5238565238494961909170453 245557745554451339492365)
                  ·
                    rfl

theorem cell22_2151999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 6].length) (baseStart_2151999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2151999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2151999 prefixEnd_2151999 := by exact prefixLift 2151999
  have htrace : WordTrace (prefixWord ++ tailWord_2151999) baseStart_2151999 baseEnd_2151999 := by
    simpa [prefixWord, tailWord_2151999, baseEnd_2151999] using wordTrace_append hprefix tailTrace_2151999
  have hstable : (prefixWord ++ tailWord_2151999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151999).length < 2 ^ (prefixWord ++ tailWord_2151999).sum := by decide
  have hdescent : baseEnd_2151999 < baseStart_2151999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152014 : List Nat := [4, 1, 1, 1, 1, 2, 1, 3, 3, 5]
def baseStart_2152014 : Nat := 118140960795 + 2152014 * 2 ^ 59
def prefixEnd_2152014 : Nat := 4983230072969 + 3 ^ 40 * 2152014 * 2
def baseEnd_2152014 : Nat := 736678371469898979352049

theorem tailTrace_2152014 : CollatzResearch.WordTrace tailWord_2152014 prefixEnd_2152014 736678371469898979352049 := by
  unfold tailWord_2152014
  simp only [CollatzResearch.WordTrace]
  refine ⟨9811299853203535946921887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52326932550418858383583397 9811299853203535946921887)
  ·
    refine ⟨14716949779805303920382831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9811299853203535946921887 14716949779805303920382831)
    ·
      refine ⟨22075424669707955880574247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14716949779805303920382831 22075424669707955880574247)
      ·
        refine ⟨33113137004561933820861371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22075424669707955880574247 33113137004561933820861371)
        ·
          refine ⟨49669705506842900731292057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33113137004561933820861371 49669705506842900731292057)
          ·
            refine ⟨37252279130132175548469043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49669705506842900731292057 37252279130132175548469043)
            ·
              refine ⟨55878418695198263322703565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37252279130132175548469043 55878418695198263322703565)
              ·
                refine ⟨20954407010699348746013837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55878418695198263322703565 20954407010699348746013837)
                ·
                  refine ⟨7857902629012255779755189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20954407010699348746013837 7857902629012255779755189)
                  ·
                    refine ⟨736678371469898979352049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7857902629012255779755189 736678371469898979352049)
                    ·
                      rfl

theorem cell22_2152014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_2152014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2152014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2152014 prefixEnd_2152014 := by exact prefixLift 2152014
  have htrace : WordTrace (prefixWord ++ tailWord_2152014) baseStart_2152014 baseEnd_2152014 := by
    simpa [prefixWord, tailWord_2152014, baseEnd_2152014] using wordTrace_append hprefix tailTrace_2152014
  have hstable : (prefixWord ++ tailWord_2152014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152014).length < 2 ^ (prefixWord ++ tailWord_2152014).sum := by decide
  have hdescent : baseEnd_2152014 < baseStart_2152014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152033 : List Nat := [1, 2, 3, 1, 1, 3, 5, 2, 4]
def baseStart_2152033 : Nat := 118140960795 + 2152033 * 2 ^ 59
def prefixEnd_2152033 : Nat := 4983230072969 + 3 ^ 40 * 2152033 * 2
def baseEnd_2152033 : Nat := 245561625186063087708997

theorem tailTrace_2152033 : CollatzResearch.WordTrace tailWord_2152033 prefixEnd_2152033 245561625186063087708997 := by
  unfold tailWord_2152033
  simp only [CollatzResearch.WordTrace]
  refine ⟨78491091812559453820316753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52327394541706302546877835 78491091812559453820316753)
  ·
    refine ⟨58868318859419590365237565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78491091812559453820316753 58868318859419590365237565)
    ·
      refine ⟨22075619572282346386964087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58868318859419590365237565 22075619572282346386964087)
      ·
        refine ⟨33113429358423519580446131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22075619572282346386964087 33113429358423519580446131)
        ·
          refine ⟨49670144037635279370669197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33113429358423519580446131 49670144037635279370669197)
          ·
            refine ⟨18626304014113229764000949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49670144037635279370669197 18626304014113229764000949)
            ·
              refine ⟨1746216001323115290375089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18626304014113229764000949 1746216001323115290375089)
              ·
                refine ⟨1309662000992336467781317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1746216001323115290375089 1309662000992336467781317)
                ·
                  refine ⟨245561625186063087708997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1309662000992336467781317 245561625186063087708997)
                  ·
                    rfl

theorem cell22_2152033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 2, 4].length) (baseStart_2152033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2152033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2152033 prefixEnd_2152033 := by exact prefixLift 2152033
  have htrace : WordTrace (prefixWord ++ tailWord_2152033) baseStart_2152033 baseEnd_2152033 := by
    simpa [prefixWord, tailWord_2152033, baseEnd_2152033] using wordTrace_append hprefix tailTrace_2152033
  have hstable : (prefixWord ++ tailWord_2152033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152033).length < 2 ^ (prefixWord ++ tailWord_2152033).sum := by decide
  have hdescent : baseEnd_2152033 < baseStart_2152033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152048 : List Nat := [2, 1, 1, 1, 6, 2, 1, 3, 2, 3]
def baseStart_2152048 : Nat := 118140960795 + 2152048 * 2 ^ 59
def prefixEnd_2152048 : Nat := 4983230072969 + 3 ^ 40 * 2152048 * 2
def baseEnd_2152048 : Nat := 736690010364734224001945

theorem tailTrace_2152048 : CollatzResearch.WordTrace tailWord_2152048 prefixEnd_2152048 736690010364734224001945 := by
  unfold tailWord_2152048
  simp only [CollatzResearch.WordTrace]
  refine ⟨39245819453752555691056399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52327759271670074254741865 39245819453752555691056399)
  ·
    refine ⟨58868729180628833536584599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39245819453752555691056399 58868729180628833536584599)
    ·
      refine ⟨88303093770943250304876899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58868729180628833536584599 88303093770943250304876899)
      ·
        refine ⟨132454640656414875457315349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88303093770943250304876899 132454640656414875457315349)
        ·
          refine ⟨6208811280769447287061657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 132454640656414875457315349 6208811280769447287061657)
          ·
            refine ⟨4656608460577085465296243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6208811280769447287061657 4656608460577085465296243)
            ·
              refine ⟨6984912690865628197944365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4656608460577085465296243 6984912690865628197944365)
              ·
                refine ⟨2619342259074610574229137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6984912690865628197944365 2619342259074610574229137)
                ·
                  refine ⟨1964506694305957930671853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2619342259074610574229137 1964506694305957930671853)
                  ·
                    refine ⟨736690010364734224001945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1964506694305957930671853 736690010364734224001945)
                    ·
                      rfl

theorem cell22_2152048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 2, 3].length) (baseStart_2152048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2152048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2152048 prefixEnd_2152048 := by exact prefixLift 2152048
  have htrace : WordTrace (prefixWord ++ tailWord_2152048) baseStart_2152048 baseEnd_2152048 := by
    simpa [prefixWord, tailWord_2152048, baseEnd_2152048] using wordTrace_append hprefix tailTrace_2152048
  have hstable : (prefixWord ++ tailWord_2152048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152048).length < 2 ^ (prefixWord ++ tailWord_2152048).sum := by decide
  have hdescent : baseEnd_2152048 < baseStart_2152048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152084 : List Nat := [2, 4, 2, 2, 3, 1, 2, 2, 4]
def baseStart_2152084 : Nat := 118140960795 + 2152084 * 2 ^ 59
def prefixEnd_2152084 : Nat := 4983230072969 + 3 ^ 40 * 2152084 * 2
def baseEnd_2152084 : Nat := 245567444633480710033945

theorem tailTrace_2152084 : CollatzResearch.WordTrace tailWord_2152084 prefixEnd_2152084 245567444633480710033945 := by
  unfold tailWord_2152084
  simp only [CollatzResearch.WordTrace]
  refine ⟨39246475967687344765211653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52328634623583126353615537 39246475967687344765211653)
  ·
    refine ⟨7358714243941377143477185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39246475967687344765211653 7358714243941377143477185)
    ·
      refine ⟨5519035682956032857607889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7358714243941377143477185 5519035682956032857607889)
      ·
        refine ⟨4139276762217024643205917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5519035682956032857607889 4139276762217024643205917)
        ·
          refine ⟨1552228785831384241202219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4139276762217024643205917 1552228785831384241202219)
          ·
            refine ⟨2328343178747076361803329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1552228785831384241202219 2328343178747076361803329)
            ·
              refine ⟨1746257384060307271352497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2328343178747076361803329 1746257384060307271352497)
              ·
                refine ⟨1309693038045230453514373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1746257384060307271352497 1309693038045230453514373)
                ·
                  refine ⟨245567444633480710033945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1309693038045230453514373 245567444633480710033945)
                  ·
                    rfl

theorem cell22_2152084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_2152084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2152084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2152084 prefixEnd_2152084 := by exact prefixLift 2152084
  have htrace : WordTrace (prefixWord ++ tailWord_2152084) baseStart_2152084 baseEnd_2152084 := by
    simpa [prefixWord, tailWord_2152084, baseEnd_2152084] using wordTrace_append hprefix tailTrace_2152084
  have hstable : (prefixWord ++ tailWord_2152084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152084).length < 2 ^ (prefixWord ++ tailWord_2152084).sum := by decide
  have hdescent : baseEnd_2152084 < baseStart_2152084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152095 : List Nat := [1, 1, 2, 7, 2, 1, 1, 7]
def baseStart_2152095 : Nat := 118140960795 + 2152095 * 2 ^ 59
def prefixEnd_2152095 : Nat := 4983230072969 + 3 ^ 40 * 2152095 * 2
def baseEnd_2152095 : Nat := 81856233269471307564089

theorem tailTrace_2152095 : CollatzResearch.WordTrace tailWord_2152095 prefixEnd_2152095 81856233269471307564089 := by
  unfold tailWord_2152095
  simp only [CollatzResearch.WordTrace]
  refine ⟨78493353138334838409073739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52328902092223225606049159 78493353138334838409073739)
  ·
    refine ⟨117740029707502257613610609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78493353138334838409073739 117740029707502257613610609)
    ·
      refine ⟨88305022280626693210207957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117740029707502257613610609 88305022280626693210207957)
      ·
        refine ⟨2069648959702188122114249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 88305022280626693210207957 2069648959702188122114249)
        ·
          refine ⟨1552236719776641091585687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2069648959702188122114249 1552236719776641091585687)
          ·
            refine ⟨2328355079664961637378531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1552236719776641091585687 2328355079664961637378531)
            ·
              refine ⟨3492532619497442456067797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2328355079664961637378531 3492532619497442456067797)
              ·
                refine ⟨81856233269471307564089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3492532619497442456067797 81856233269471307564089)
                ·
                  rfl

theorem cell22_2152095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 7].length) (baseStart_2152095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2152095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2152095 prefixEnd_2152095 := by exact prefixLift 2152095
  have htrace : WordTrace (prefixWord ++ tailWord_2152095) baseStart_2152095 baseEnd_2152095 := by
    simpa [prefixWord, tailWord_2152095, baseEnd_2152095] using wordTrace_append hprefix tailTrace_2152095
  have hstable : (prefixWord ++ tailWord_2152095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152095).length < 2 ^ (prefixWord ++ tailWord_2152095).sum := by decide
  have hdescent : baseEnd_2152095 < baseStart_2152095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152140 : List Nat := [2, 2, 1, 5, 2, 2, 1, 2, 5]
def baseStart_2152140 : Nat := 118140960795 + 2152140 * 2 ^ 59
def prefixEnd_2152140 : Nat := 4983230072969 + 3 ^ 40 * 2152140 * 2
def baseEnd_2152140 : Nat := 245573834614958883567221

theorem tailTrace_2152140 : CollatzResearch.WordTrace tailWord_2152140 prefixEnd_2152140 245573834614958883567221 := by
  unfold tailWord_2152140
  simp only [CollatzResearch.WordTrace]
  refine ⟨39247497211585905547230937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52329996282114540729641249 39247497211585905547230937)
  ·
    refine ⟨29435622908689429160423203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39247497211585905547230937 29435622908689429160423203)
    ·
      refine ⟨44153434363034143740634805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29435622908689429160423203 44153434363034143740634805)
      ·
        refine ⟨4139384471534450975684513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44153434363034143740634805 4139384471534450975684513)
        ·
          refine ⟨3104538353650838231763385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4139384471534450975684513 3104538353650838231763385)
          ·
            refine ⟨2328403765238128673822539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3104538353650838231763385 2328403765238128673822539)
            ·
              refine ⟨3492605647857193010733809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2328403765238128673822539 3492605647857193010733809)
              ·
                refine ⟨2619454235892894758050357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3492605647857193010733809 2619454235892894758050357)
                ·
                  refine ⟨245573834614958883567221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2619454235892894758050357 245573834614958883567221)
                  ·
                    rfl

theorem cell22_2152140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 5].length) (baseStart_2152140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2152140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2152140 prefixEnd_2152140 := by exact prefixLift 2152140
  have htrace : WordTrace (prefixWord ++ tailWord_2152140) baseStart_2152140 baseEnd_2152140 := by
    simpa [prefixWord, tailWord_2152140, baseEnd_2152140] using wordTrace_append hprefix tailTrace_2152140
  have hstable : (prefixWord ++ tailWord_2152140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152140).length < 2 ^ (prefixWord ++ tailWord_2152140).sum := by decide
  have hdescent : baseEnd_2152140 < baseStart_2152140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152151 : List Nat := [1, 1, 3, 2, 1, 3, 4, 1, 6]
def baseStart_2152151 : Nat := 118140960795 + 2152151 * 2 ^ 59
def prefixEnd_2152151 : Nat := 4983230072969 + 3 ^ 40 * 2152151 * 2
def baseEnd_2152151 : Nat := 245575089789892096225543

theorem tailTrace_2152151 : CollatzResearch.WordTrace tailWord_2152151 prefixEnd_2152151 245575089789892096225543 := by
  unfold tailWord_2152151
  simp only [CollatzResearch.WordTrace]
  refine ⟨78495395626131959973112307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52330263750754639982074871 78495395626131959973112307)
  ·
    refine ⟨117743093439197939959668461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78495395626131959973112307 117743093439197939959668461)
    ·
      refine ⟨44153660039699227484875673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117743093439197939959668461 44153660039699227484875673)
      ·
        refine ⟨33115245029774420613656755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44153660039699227484875673 33115245029774420613656755)
        ·
          refine ⟨49672867544661630920485133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33115245029774420613656755 49672867544661630920485133)
          ·
            refine ⟨18627325329248111595181925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49672867544661630920485133 18627325329248111595181925)
            ·
              refine ⟨3492623499234020924096611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18627325329248111595181925 3492623499234020924096611)
              ·
                refine ⟨5238935248851031386144917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3492623499234020924096611 5238935248851031386144917)
                ·
                  refine ⟨245575089789892096225543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5238935248851031386144917 245575089789892096225543)
                  ·
                    rfl

theorem cell22_2152151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 6].length) (baseStart_2152151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2152151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2152151 prefixEnd_2152151 := by exact prefixLift 2152151
  have htrace : WordTrace (prefixWord ++ tailWord_2152151) baseStart_2152151 baseEnd_2152151 := by
    simpa [prefixWord, tailWord_2152151, baseEnd_2152151] using wordTrace_append hprefix tailTrace_2152151
  have hstable : (prefixWord ++ tailWord_2152151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152151).length < 2 ^ (prefixWord ++ tailWord_2152151).sum := by decide
  have hdescent : baseEnd_2152151 < baseStart_2152151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152157 : List Nat := [1, 4, 3, 3, 1, 1, 3, 1, 5]
def baseStart_2152157 : Nat := 118140960795 + 2152157 * 2 ^ 59
def prefixEnd_2152157 : Nat := 4983230072969 + 3 ^ 40 * 2152157 * 2
def baseEnd_2152157 : Nat := 245575774430764757675537

theorem tailTrace_2152157 : CollatzResearch.WordTrace tailWord_2152157 prefixEnd_2152157 245575774430764757675537 := by
  unfold tailWord_2152157
  simp only [CollatzResearch.WordTrace]
  refine ⟨78495614464110222997830725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52330409642740148665220483 78495614464110222997830725)
  ·
    refine ⟨14717927712020666812093261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78495614464110222997830725 14717927712020666812093261)
    ·
      refine ⟨5519222892007750054534973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14717927712020666812093261 5519222892007750054534973)
      ·
        refine ⟨2069708584502906270450615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5519222892007750054534973 2069708584502906270450615)
        ·
          refine ⟨3104562876754359405675923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2069708584502906270450615 3104562876754359405675923)
          ·
            refine ⟨4656844315131539108513885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3104562876754359405675923 4656844315131539108513885)
            ·
              refine ⟨1746316618174327165692707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4656844315131539108513885 1746316618174327165692707)
              ·
                refine ⟨2619474927261490748539061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1746316618174327165692707 2619474927261490748539061)
                ·
                  refine ⟨245575774430764757675537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2619474927261490748539061 245575774430764757675537)
                  ·
                    rfl

theorem cell22_2152157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_2152157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2152157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2152157 prefixEnd_2152157 := by exact prefixLift 2152157
  have htrace : WordTrace (prefixWord ++ tailWord_2152157) baseStart_2152157 baseEnd_2152157 := by
    simpa [prefixWord, tailWord_2152157, baseEnd_2152157] using wordTrace_append hprefix tailTrace_2152157
  have hstable : (prefixWord ++ tailWord_2152157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152157).length < 2 ^ (prefixWord ++ tailWord_2152157).sum := by decide
  have hdescent : baseEnd_2152157 < baseStart_2152157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152196 : List Nat := [2, 3, 2, 2, 1, 2, 10]
def baseStart_2152196 : Nat := 118140960795 + 2152196 * 2 ^ 59
def prefixEnd_2152196 : Nat := 4983230072969 + 3 ^ 40 * 2152196 * 2
def baseEnd_2152196 : Nat := 27286691621826339677833

theorem tailTrace_2152196 : CollatzResearch.WordTrace tailWord_2152196 prefixEnd_2152196 27286691621826339677833 := by
  unfold tailWord_2152196
  simp only [CollatzResearch.WordTrace]
  refine ⟨39248518455484466329250221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52331357940645955105666961 39248518455484466329250221)
  ·
    refine ⟨14718194420806674873468833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39248518455484466329250221 14718194420806674873468833)
    ·
      refine ⟨11038645815605006155101625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14718194420806674873468833 11038645815605006155101625)
      ·
        refine ⟨8278984361703754616326219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11038645815605006155101625 8278984361703754616326219)
        ·
          refine ⟨12418476542555631924489329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8278984361703754616326219 12418476542555631924489329)
          ·
            refine ⟨9313857406916723943366997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12418476542555631924489329 9313857406916723943366997)
            ·
              refine ⟨27286691621826339677833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9313857406916723943366997 27286691621826339677833)
              ·
                rfl

theorem cell22_2152196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 10].length) (baseStart_2152196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2152196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2152196 prefixEnd_2152196 := by exact prefixLift 2152196
  have htrace : WordTrace (prefixWord ++ tailWord_2152196) baseStart_2152196 baseEnd_2152196 := by
    simpa [prefixWord, tailWord_2152196, baseEnd_2152196] using wordTrace_append hprefix tailTrace_2152196
  have hstable : (prefixWord ++ tailWord_2152196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152196).length < 2 ^ (prefixWord ++ tailWord_2152196).sum := by decide
  have hdescent : baseEnd_2152196 < baseStart_2152196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152273 : List Nat := [1, 2, 2, 1, 5, 2, 1, 1, 2, 5]
def baseStart_2152273 : Nat := 118140960795 + 2152273 * 2 ^ 59
def prefixEnd_2152273 : Nat := 4983230072969 + 3 ^ 40 * 2152273 * 2
def baseEnd_2152273 : Nat := 736767032462908637126255

theorem tailTrace_2152273 : CollatzResearch.WordTrace tailWord_2152273 prefixEnd_2152273 736767032462908637126255 := by
  unfold tailWord_2152273
  simp only [CollatzResearch.WordTrace]
  refine ⟨78499845331689974809053473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52333230221126649872702315 78499845331689974809053473)
  ·
    refine ⟨58874883998767481106790105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78499845331689974809053473 58874883998767481106790105)
    ·
      refine ⟨44156162999075610830092579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58874883998767481106790105 44156162999075610830092579)
      ·
        refine ⟨66234244498613416245138869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44156162999075610830092579 66234244498613416245138869)
        ·
          refine ⟨6209460421745007772981769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66234244498613416245138869 6209460421745007772981769)
          ·
            refine ⟨4657095316308755829736327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6209460421745007772981769 4657095316308755829736327)
            ·
              refine ⟨6985642974463133744604491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4657095316308755829736327 6985642974463133744604491)
              ·
                refine ⟨10478464461694700616906737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6985642974463133744604491 10478464461694700616906737)
                ·
                  refine ⟨7858848346271025462680053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10478464461694700616906737 7858848346271025462680053)
                  ·
                    refine ⟨736767032462908637126255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7858848346271025462680053 736767032462908637126255)
                    ·
                      rfl

theorem cell22_2152273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_2152273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2152273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2152273 prefixEnd_2152273 := by exact prefixLift 2152273
  have htrace : WordTrace (prefixWord ++ tailWord_2152273) baseStart_2152273 baseEnd_2152273 := by
    simpa [prefixWord, tailWord_2152273, baseEnd_2152273] using wordTrace_append hprefix tailTrace_2152273
  have hstable : (prefixWord ++ tailWord_2152273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152273).length < 2 ^ (prefixWord ++ tailWord_2152273).sum := by decide
  have hdescent : baseEnd_2152273 < baseStart_2152273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152288 : List Nat := [2, 1, 1, 3, 3, 2, 2, 1, 3, 4]
def baseStart_2152288 : Nat := 118140960795 + 2152288 * 2 ^ 59
def prefixEnd_2152288 : Nat := 4983230072969 + 3 ^ 40 * 2152288 * 2
def baseEnd_2152288 : Nat := 736772167269453598001209

theorem tailTrace_2152288 : CollatzResearch.WordTrace tailWord_2152288 prefixEnd_2152288 736772167269453598001209 := by
  unfold tailWord_2152288
  simp only [CollatzResearch.WordTrace]
  refine ⟨39250196213317816185424759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52333594951090421580566345 39250196213317816185424759)
  ·
    refine ⟨58875294319976724278137139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39250196213317816185424759 58875294319976724278137139)
    ·
      refine ⟨88312941479965086417205709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58875294319976724278137139 88312941479965086417205709)
      ·
        refine ⟨33117353054986907406452141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88312941479965086417205709 33117353054986907406452141)
        ·
          refine ⟨12419007395620090277419553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33117353054986907406452141 12419007395620090277419553)
          ·
            refine ⟨9314255546715067708064665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12419007395620090277419553 9314255546715067708064665)
            ·
              refine ⟨6985691660036300781048499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9314255546715067708064665 6985691660036300781048499)
              ·
                refine ⟨10478537490054451171572749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6985691660036300781048499 10478537490054451171572749)
                ·
                  refine ⟨3929451558770419189339781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10478537490054451171572749 3929451558770419189339781)
                  ·
                    refine ⟨736772167269453598001209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3929451558770419189339781 736772167269453598001209)
                    ·
                      rfl

theorem cell22_2152288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 3, 4].length) (baseStart_2152288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2152288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2152288 prefixEnd_2152288 := by exact prefixLift 2152288
  have htrace : WordTrace (prefixWord ++ tailWord_2152288) baseStart_2152288 baseEnd_2152288 := by
    simpa [prefixWord, tailWord_2152288, baseEnd_2152288] using wordTrace_append hprefix tailTrace_2152288
  have hstable : (prefixWord ++ tailWord_2152288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152288).length < 2 ^ (prefixWord ++ tailWord_2152288).sum := by decide
  have hdescent : baseEnd_2152288 < baseStart_2152288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152331 : List Nat := [1, 1, 1, 1, 4, 2, 1, 11]
def baseStart_2152331 : Nat := 118140960795 + 2152331 * 2 ^ 59
def prefixEnd_2152331 : Nat := 4983230072969 + 3 ^ 40 * 2152331 * 2
def baseEnd_2152331 : Nat := 81865209672023979908453

theorem tailTrace_2152331 : CollatzResearch.WordTrace tailWord_2152331 prefixEnd_2152331 81865209672023979908453 := by
  unfold tailWord_2152331
  simp only [CollatzResearch.WordTrace]
  refine ⟨78501960765479850714664847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52334640510319900476443231 78501960765479850714664847)
  ·
    refine ⟨117752941148219776071997271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78501960765479850714664847 117752941148219776071997271)
    ·
      refine ⟨176629411722329664107995907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117752941148219776071997271 176629411722329664107995907)
      ·
        refine ⟨264944117583494496161993861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176629411722329664107995907 264944117583494496161993861)
        ·
          refine ⟨49677022046905218030373849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 264944117583494496161993861 49677022046905218030373849)
          ·
            refine ⟨37257766535178913522780387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49677022046905218030373849 37257766535178913522780387)
            ·
              refine ⟨55886649802768370284170581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37257766535178913522780387 55886649802768370284170581)
              ·
                refine ⟨81865209672023979908453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 55886649802768370284170581 81865209672023979908453)
                ·
                  rfl

theorem cell22_2152331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 11].length) (baseStart_2152331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2152331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2152331 prefixEnd_2152331 := by exact prefixLift 2152331
  have htrace : WordTrace (prefixWord ++ tailWord_2152331) baseStart_2152331 baseEnd_2152331 := by
    simpa [prefixWord, tailWord_2152331, baseEnd_2152331] using wordTrace_append hprefix tailTrace_2152331
  have hstable : (prefixWord ++ tailWord_2152331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152331).length < 2 ^ (prefixWord ++ tailWord_2152331).sum := by decide
  have hdescent : baseEnd_2152331 < baseStart_2152331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152354 : List Nat := [3, 3, 1, 2, 3, 2, 1, 3, 4]
def baseStart_2152354 : Nat := 118140960795 + 2152354 * 2 ^ 59
def prefixEnd_2152354 : Nat := 4983230072969 + 3 ^ 40 * 2152354 * 2
def baseEnd_2152354 : Nat := 245598253472750475283669

theorem tailTrace_2152354 : CollatzResearch.WordTrace tailWord_2152354 prefixEnd_2152354 245598253472750475283669 := by
  unfold tailWord_2152354
  simp only [CollatzResearch.WordTrace]
  refine ⟨19625699911099131410688029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52335199762931017095168077 19625699911099131410688029)
  ·
    refine ⟨7359637466662174279008011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19625699911099131410688029 7359637466662174279008011)
    ·
      refine ⟨11039456199993261418512017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7359637466662174279008011 11039456199993261418512017)
      ·
        refine ⟨8279592149994946063884013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11039456199993261418512017 8279592149994946063884013)
        ·
          refine ⟨3104847056248104773956505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8279592149994946063884013 3104847056248104773956505)
          ·
            refine ⟨2328635292186078580467379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3104847056248104773956505 2328635292186078580467379)
            ·
              refine ⟨3492952938279117870701069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2328635292186078580467379 3492952938279117870701069)
              ·
                refine ⟨1309857351854669201512901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3492952938279117870701069 1309857351854669201512901)
                ·
                  refine ⟨245598253472750475283669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1309857351854669201512901 245598253472750475283669)
                  ·
                    rfl

theorem cell22_2152354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_2152354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2152354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2152354 prefixEnd_2152354 := by exact prefixLift 2152354
  have htrace : WordTrace (prefixWord ++ tailWord_2152354) baseStart_2152354 baseEnd_2152354 := by
    simpa [prefixWord, tailWord_2152354, baseEnd_2152354] using wordTrace_append hprefix tailTrace_2152354
  have hstable : (prefixWord ++ tailWord_2152354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152354).length < 2 ^ (prefixWord ++ tailWord_2152354).sum := by decide
  have hdescent : baseEnd_2152354 < baseStart_2152354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152393 : List Nat := [1, 2, 1, 1, 2, 1, 2, 7, 5]
def baseStart_2152393 : Nat := 118140960795 + 2152393 * 2 ^ 59
def prefixEnd_2152393 : Nat := 4983230072969 + 3 ^ 40 * 2152393 * 2
def baseEnd_2152393 : Nat := 245602703638422774708629

theorem tailTrace_2152393 : CollatzResearch.WordTrace tailWord_2152393 prefixEnd_2152393 245602703638422774708629 := by
  unfold tailWord_2152393
  simp only [CollatzResearch.WordTrace]
  refine ⟨78504222091255235303421833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52336148060836823535614555 78504222091255235303421833)
  ·
    refine ⟨58878166568441426477566375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78504222091255235303421833 58878166568441426477566375)
    ·
      refine ⟨88317249852662139716349563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58878166568441426477566375 88317249852662139716349563)
      ·
        refine ⟨132475874778993209574524345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88317249852662139716349563 132475874778993209574524345)
        ·
          refine ⟨99356906084244907180893259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132475874778993209574524345 99356906084244907180893259)
          ·
            refine ⟨149035359126367360771339889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99356906084244907180893259 149035359126367360771339889)
            ·
              refine ⟨111776519344775520578504917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149035359126367360771339889 111776519344775520578504917)
              ·
                refine ⟨2619762172143176263558709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 111776519344775520578504917 2619762172143176263558709)
                ·
                  refine ⟨245602703638422774708629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2619762172143176263558709 245602703638422774708629)
                  ·
                    rfl

theorem cell22_2152393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 5].length) (baseStart_2152393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2152393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2152393 prefixEnd_2152393 := by exact prefixLift 2152393
  have htrace : WordTrace (prefixWord ++ tailWord_2152393) baseStart_2152393 baseEnd_2152393 := by
    simpa [prefixWord, tailWord_2152393, baseEnd_2152393] using wordTrace_append hprefix tailTrace_2152393
  have hstable : (prefixWord ++ tailWord_2152393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152393).length < 2 ^ (prefixWord ++ tailWord_2152393).sum := by decide
  have hdescent : baseEnd_2152393 < baseStart_2152393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152455 : List Nat := [1, 1, 4, 3, 1, 3, 1, 2, 6]
def baseStart_2152455 : Nat := 118140960795 + 2152455 * 2 ^ 59
def prefixEnd_2152455 : Nat := 4983230072969 + 3 ^ 40 * 2152455 * 2
def baseEnd_2152455 : Nat := 245609778260773609691899

theorem tailTrace_2152455 : CollatzResearch.WordTrace tailWord_2152455 prefixEnd_2152455 245609778260773609691899 := by
  unfold tailWord_2152455
  simp only [CollatzResearch.WordTrace]
  refine ⟨78506483417030619892178819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52337655611353746594785879 78506483417030619892178819)
  ·
    refine ⟨117759725125545929838268229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78506483417030619892178819 117759725125545929838268229)
    ·
      refine ⟨22079948461039861844675293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117759725125545929838268229 22079948461039861844675293)
      ·
        refine ⟨8279980672889948191753235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22079948461039861844675293 8279980672889948191753235)
        ·
          refine ⟨12419971009334922287629853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8279980672889948191753235 12419971009334922287629853)
          ·
            refine ⟨4657489128500595857861195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12419971009334922287629853 4657489128500595857861195)
            ·
              refine ⟨6986233692750893786791793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4657489128500595857861195 6986233692750893786791793)
              ·
                refine ⟨5239675269563170340093845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6986233692750893786791793 5239675269563170340093845)
                ·
                  refine ⟨245609778260773609691899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5239675269563170340093845 245609778260773609691899)
                  ·
                    rfl

theorem cell22_2152455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 6].length) (baseStart_2152455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2152455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2152455 prefixEnd_2152455 := by exact prefixLift 2152455
  have htrace : WordTrace (prefixWord ++ tailWord_2152455) baseStart_2152455 baseEnd_2152455 := by
    simpa [prefixWord, tailWord_2152455, baseEnd_2152455] using wordTrace_append hprefix tailTrace_2152455
  have hstable : (prefixWord ++ tailWord_2152455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152455).length < 2 ^ (prefixWord ++ tailWord_2152455).sum := by decide
  have hdescent : baseEnd_2152455 < baseStart_2152455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152472 : List Nat := [2, 1, 2, 3, 2, 1, 4, 3, 4]
def baseStart_2152472 : Nat := 118140960795 + 2152472 * 2 ^ 59
def prefixEnd_2152472 : Nat := 4983230072969 + 3 ^ 40 * 2152472 * 2
def baseEnd_2152472 : Nat := 245611718076579483800215

theorem tailTrace_2152472 : CollatzResearch.WordTrace tailWord_2152472 prefixEnd_2152472 245611718076579483800215 := by
  unfold tailWord_2152472
  simp only [CollatzResearch.WordTrace]
  refine ⟨39253551728984515897773835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52338068971979354530365113 39253551728984515897773835)
  ·
    refine ⟨58880327593476773846660753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39253551728984515897773835 58880327593476773846660753)
    ·
      refine ⟨44160245695107580384995565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58880327593476773846660753 44160245695107580384995565)
      ·
        refine ⟨16560092135665342644373337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44160245695107580384995565 16560092135665342644373337)
        ·
          refine ⟨12420069101749006983280003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16560092135665342644373337 12420069101749006983280003)
          ·
            refine ⟨18630103652623510474920005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12420069101749006983280003 18630103652623510474920005)
            ·
              refine ⟨3493144434866908214047501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18630103652623510474920005 3493144434866908214047501)
              ·
                refine ⟨1309929163075090580267813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3493144434866908214047501 1309929163075090580267813)
                ·
                  refine ⟨245611718076579483800215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1309929163075090580267813 245611718076579483800215)
                  ·
                    rfl

theorem cell22_2152472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 3, 4].length) (baseStart_2152472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2152472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2152472 prefixEnd_2152472 := by exact prefixLift 2152472
  have htrace : WordTrace (prefixWord ++ tailWord_2152472) baseStart_2152472 baseEnd_2152472 := by
    simpa [prefixWord, tailWord_2152472, baseEnd_2152472] using wordTrace_append hprefix tailTrace_2152472
  have hstable : (prefixWord ++ tailWord_2152472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152472).length < 2 ^ (prefixWord ++ tailWord_2152472).sum := by decide
  have hdescent : baseEnd_2152472 < baseStart_2152472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152474 : List Nat := [3, 1, 1, 3, 1, 5, 2, 1, 1, 4]
def baseStart_2152474 : Nat := 118140960795 + 2152474 * 2 ^ 59
def prefixEnd_2152474 : Nat := 4983230072969 + 3 ^ 40 * 2152474 * 2
def baseEnd_2152474 : Nat := 736835838870611112850639

theorem tailTrace_2152474 : CollatzResearch.WordTrace tailWord_2152474 prefixEnd_2152474 736835838870611112850639 := by
  unfold tailWord_2152474
  simp only [CollatzResearch.WordTrace]
  refine ⟨19626794100990446534280119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52338117602641190758080317 19626794100990446534280119)
  ·
    refine ⟨29440191151485669801420179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19626794100990446534280119 29440191151485669801420179)
    ·
      refine ⟨44160286727228504702130269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29440191151485669801420179 44160286727228504702130269)
      ·
        refine ⟨16560107522710689263298851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44160286727228504702130269 16560107522710689263298851)
        ·
          refine ⟨24840161284066033894948277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16560107522710689263298851 24840161284066033894948277)
          ·
            refine ⟨2328765120381190677651401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24840161284066033894948277 2328765120381190677651401)
            ·
              refine ⟨1746573840285893008238551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2328765120381190677651401 1746573840285893008238551)
              ·
                refine ⟨2619860760428839512357827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1746573840285893008238551 2619860760428839512357827)
                ·
                  refine ⟨3929791140643259268536741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2619860760428839512357827 3929791140643259268536741)
                  ·
                    refine ⟨736835838870611112850639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3929791140643259268536741 736835838870611112850639)
                    ·
                      rfl

theorem cell22_2152474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 1, 4].length) (baseStart_2152474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2152474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2152474 prefixEnd_2152474 := by exact prefixLift 2152474
  have htrace : WordTrace (prefixWord ++ tailWord_2152474) baseStart_2152474 baseEnd_2152474 := by
    simpa [prefixWord, tailWord_2152474, baseEnd_2152474] using wordTrace_append hprefix tailTrace_2152474
  have hstable : (prefixWord ++ tailWord_2152474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152474).length < 2 ^ (prefixWord ++ tailWord_2152474).sum := by decide
  have hdescent : baseEnd_2152474 < baseStart_2152474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152483 : List Nat := [1, 1, 1, 4, 3, 1, 11]
def baseStart_2152483 : Nat := 118140960795 + 2152483 * 2 ^ 59
def prefixEnd_2152483 : Nat := 4983230072969 + 3 ^ 40 * 2152483 * 2
def baseEnd_2152483 : Nat := 27290330361279188495393

theorem tailTrace_2152483 : CollatzResearch.WordTrace tailWord_2152483 prefixEnd_2152483 27290330361279188495393 := by
  unfold tailWord_2152483
  simp only [CollatzResearch.WordTrace]
  refine ⟨78507504660929180674198103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52338336440619453782798735 78507504660929180674198103)
  ·
    refine ⟨117761256991393771011297155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78507504660929180674198103 117761256991393771011297155)
    ·
      refine ⟨176641885487090656516945733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117761256991393771011297155 176641885487090656516945733)
      ·
        refine ⟨33120353528829498096927325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 176641885487090656516945733 33120353528829498096927325)
        ·
          refine ⟨12420132573311061786347747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33120353528829498096927325 12420132573311061786347747)
          ·
            refine ⟨18630198859966592679521621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12420132573311061786347747 18630198859966592679521621)
            ·
              refine ⟨27290330361279188495393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 18630198859966592679521621 27290330361279188495393)
              ·
                rfl

theorem cell22_2152483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 11].length) (baseStart_2152483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2152483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2152483 prefixEnd_2152483 := by exact prefixLift 2152483
  have htrace : WordTrace (prefixWord ++ tailWord_2152483) baseStart_2152483 baseEnd_2152483 := by
    simpa [prefixWord, tailWord_2152483, baseEnd_2152483] using wordTrace_append hprefix tailTrace_2152483
  have hstable : (prefixWord ++ tailWord_2152483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152483).length < 2 ^ (prefixWord ++ tailWord_2152483).sum := by decide
  have hdescent : baseEnd_2152483 < baseStart_2152483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152504 : List Nat := [2, 1, 2, 1, 7, 1, 1, 1, 1, 5]
def baseStart_2152504 : Nat := 118140960795 + 2152504 * 2 ^ 59
def prefixEnd_2152504 : Nat := 4983230072969 + 3 ^ 40 * 2152504 * 2
def baseEnd_2152504 : Nat := 736846108483701034600547

theorem tailTrace_2152504 : CollatzResearch.WordTrace tailWord_2152504 prefixEnd_2152504 736846108483701034600547 := by
  unfold tailWord_2152504
  simp only [CollatzResearch.WordTrace]
  refine ⟨39254135296926550630356283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52338847062568734173808377 39254135296926550630356283)
  ·
    refine ⟨58881202945389825945534425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39254135296926550630356283 58881202945389825945534425)
    ·
      refine ⟨44160902209042369459150819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58881202945389825945534425 44160902209042369459150819)
      ·
        refine ⟨66241353313563554188726229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44160902209042369459150819 66241353313563554188726229)
        ·
          refine ⟨1552531718286645801298271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 66241353313563554188726229 1552531718286645801298271)
          ·
            refine ⟨2328797577429968701947407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1552531718286645801298271 2328797577429968701947407)
            ·
              refine ⟨3493196366144953052921111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2328797577429968701947407 3493196366144953052921111)
              ·
                refine ⟨5239794549217429579381667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3493196366144953052921111 5239794549217429579381667)
                ·
                  refine ⟨7859691823826144369072501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5239794549217429579381667 7859691823826144369072501)
                  ·
                    refine ⟨736846108483701034600547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7859691823826144369072501 736846108483701034600547)
                    ·
                      rfl

theorem cell22_2152504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 1, 5].length) (baseStart_2152504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2152504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2152504 prefixEnd_2152504 := by exact prefixLift 2152504
  have htrace : WordTrace (prefixWord ++ tailWord_2152504) baseStart_2152504 baseEnd_2152504 := by
    simpa [prefixWord, tailWord_2152504, baseEnd_2152504] using wordTrace_append hprefix tailTrace_2152504
  have hstable : (prefixWord ++ tailWord_2152504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152504).length < 2 ^ (prefixWord ++ tailWord_2152504).sum := by decide
  have hdescent : baseEnd_2152504 < baseStart_2152504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152515 : List Nat := [1, 1, 1, 3, 1, 2, 2, 3, 5, 3]
def baseStart_2152515 : Nat := 118140960795 + 2152515 * 2 ^ 59
def prefixEnd_2152515 : Nat := 4983230072969 + 3 ^ 40 * 2152515 * 2
def baseEnd_2152515 : Nat := 736849874008500672575513

theorem tailTrace_2152515 : CollatzResearch.WordTrace tailWord_2152515 prefixEnd_2152515 736849874008500672575513 := by
  unfold tailWord_2152515
  simp only [CollatzResearch.WordTrace]
  refine ⟨78508671796813250139362999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52339114531208833426241999 78508671796813250139362999)
  ·
    refine ⟨117763007695219875209044499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78508671796813250139362999 117763007695219875209044499)
    ·
      refine ⟨176644511542829812813566749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117763007695219875209044499 176644511542829812813566749)
      ·
        refine ⟨66241691828561179805087531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176644511542829812813566749 66241691828561179805087531)
        ·
          refine ⟨99362537742841769707631297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66241691828561179805087531 99362537742841769707631297)
          ·
            refine ⟨74521903307131327280723473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99362537742841769707631297 74521903307131327280723473)
            ·
              refine ⟨55891427480348495460542605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74521903307131327280723473 55891427480348495460542605)
              ·
                refine ⟨20959285305130685797703477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55891427480348495460542605 20959285305130685797703477)
                ·
                  refine ⟨1964932997356001793534701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20959285305130685797703477 1964932997356001793534701)
                  ·
                    refine ⟨736849874008500672575513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1964932997356001793534701 736849874008500672575513)
                    ·
                      rfl

theorem cell22_2152515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 5, 3].length) (baseStart_2152515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2152515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2152515 prefixEnd_2152515 := by exact prefixLift 2152515
  have htrace : WordTrace (prefixWord ++ tailWord_2152515) baseStart_2152515 baseEnd_2152515 := by
    simpa [prefixWord, tailWord_2152515, baseEnd_2152515] using wordTrace_append hprefix tailTrace_2152515
  have hstable : (prefixWord ++ tailWord_2152515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152515).length < 2 ^ (prefixWord ++ tailWord_2152515).sum := by decide
  have hdescent : baseEnd_2152515 < baseStart_2152515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152534 : List Nat := [5, 2, 2, 1, 1, 3, 8]
def baseStart_2152534 : Nat := 118140960795 + 2152534 * 2 ^ 59
def prefixEnd_2152534 : Nat := 4983230072969 + 3 ^ 40 * 2152534 * 2
def baseEnd_2152534 : Nat := 27290976966547813198165

theorem tailTrace_2152534 : CollatzResearch.WordTrace tailWord_2152534 prefixEnd_2152534 27290976966547813198165 := by
  unfold tailWord_2152534
  simp only [CollatzResearch.WordTrace]
  refine ⟨4906835298984026024019041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52339576522496277589536437 4906835298984026024019041)
  ·
    refine ⟨3680126474238019518014281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4906835298984026024019041 3680126474238019518014281)
    ·
      refine ⟨2760094855678514638510711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3680126474238019518014281 2760094855678514638510711)
      ·
        refine ⟨4140142283517771957766067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2760094855678514638510711 4140142283517771957766067)
        ·
          refine ⟨6210213425276657936649101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4140142283517771957766067 6210213425276657936649101)
          ·
            refine ⟨2328830034478746726243413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6210213425276657936649101 2328830034478746726243413)
            ·
              refine ⟨27290976966547813198165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2328830034478746726243413 27290976966547813198165)
              ·
                rfl

theorem cell22_2152534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 8].length) (baseStart_2152534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2152534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2152534 prefixEnd_2152534 := by exact prefixLift 2152534
  have htrace : WordTrace (prefixWord ++ tailWord_2152534) baseStart_2152534 baseEnd_2152534 := by
    simpa [prefixWord, tailWord_2152534, baseEnd_2152534] using wordTrace_append hprefix tailTrace_2152534
  have hstable : (prefixWord ++ tailWord_2152534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152534).length < 2 ^ (prefixWord ++ tailWord_2152534).sum := by decide
  have hdescent : baseEnd_2152534 < baseStart_2152534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152545 : List Nat := [1, 2, 3, 1, 1, 2, 1, 6, 5]
def baseStart_2152545 : Nat := 118140960795 + 2152545 * 2 ^ 59
def prefixEnd_2152545 : Nat := 4983230072969 + 3 ^ 40 * 2152545 * 2
def baseEnd_2152545 : Nat := 245620047873863531441807

theorem tailTrace_2152545 : CollatzResearch.WordTrace tailWord_2152545 prefixEnd_2152545 245620047873863531441807 := by
  unfold tailWord_2152545
  simp only [CollatzResearch.WordTrace]
  refine ⟨78509765986704565262955089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52339843991136376841970059 78509765986704565262955089)
  ·
    refine ⟨58882324490028423947216317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78509765986704565262955089 58882324490028423947216317)
    ·
      refine ⟨22080871683760658980206119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58882324490028423947216317 22080871683760658980206119)
      ·
        refine ⟨33121307525640988470309179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22080871683760658980206119 33121307525640988470309179)
        ·
          refine ⟨49681961288461482705463769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33121307525640988470309179 49681961288461482705463769)
          ·
            refine ⟨37261470966346112029097827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49681961288461482705463769 37261470966346112029097827)
            ·
              refine ⟨55892206449519168043646741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37261470966346112029097827 55892206449519168043646741)
              ·
                refine ⟨2619947177321211002045941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55892206449519168043646741 2619947177321211002045941)
                ·
                  refine ⟨245620047873863531441807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2619947177321211002045941 245620047873863531441807)
                  ·
                    rfl

theorem cell22_2152545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 5].length) (baseStart_2152545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2152545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2152545 prefixEnd_2152545 := by exact prefixLift 2152545
  have htrace : WordTrace (prefixWord ++ tailWord_2152545) baseStart_2152545 baseEnd_2152545 := by
    simpa [prefixWord, tailWord_2152545, baseEnd_2152545] using wordTrace_append hprefix tailTrace_2152545
  have hstable : (prefixWord ++ tailWord_2152545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152545).length < 2 ^ (prefixWord ++ tailWord_2152545).sum := by decide
  have hdescent : baseEnd_2152545 < baseStart_2152545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152549 : List Nat := [1, 3, 1, 3, 2, 4, 1, 1, 3, 3]
def baseStart_2152549 : Nat := 118140960795 + 2152549 * 2 ^ 59
def prefixEnd_2152549 : Nat := 4983230072969 + 3 ^ 40 * 2152549 * 2
def baseEnd_2152549 : Nat := 736861512903335917225409

theorem tailTrace_2152549 : CollatzResearch.WordTrace tailWord_2152549 prefixEnd_2152549 736861512903335917225409 := by
  unfold tailWord_2152549
  simp only [CollatzResearch.WordTrace]
  refine ⟨78509911878690073946100701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52339941252460049297400467 78509911878690073946100701)
  ·
    refine ⟨29441216954508777729787763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78509911878690073946100701 29441216954508777729787763)
    ·
      refine ⟨44161825431763166594681645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29441216954508777729787763 44161825431763166594681645)
      ·
        refine ⟨16560684536911187473005617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44161825431763166594681645 16560684536911187473005617)
        ·
          refine ⟨12420513402683390604754213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16560684536911187473005617 12420513402683390604754213)
          ·
            refine ⟨2328846263003135738391415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12420513402683390604754213 2328846263003135738391415)
            ·
              refine ⟨3493269394504703607587123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2328846263003135738391415 3493269394504703607587123)
              ·
                refine ⟨5239904091757055411380685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3493269394504703607587123 5239904091757055411380685)
                ·
                  refine ⟨1964964034408895779267757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5239904091757055411380685 1964964034408895779267757)
                  ·
                    refine ⟨736861512903335917225409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1964964034408895779267757 736861512903335917225409)
                    ·
                      rfl

theorem cell22_2152549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 3, 3].length) (baseStart_2152549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2152549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2152549 prefixEnd_2152549 := by exact prefixLift 2152549
  have htrace : WordTrace (prefixWord ++ tailWord_2152549) baseStart_2152549 baseEnd_2152549 := by
    simpa [prefixWord, tailWord_2152549, baseEnd_2152549] using wordTrace_append hprefix tailTrace_2152549
  have hstable : (prefixWord ++ tailWord_2152549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152549).length < 2 ^ (prefixWord ++ tailWord_2152549).sum := by decide
  have hdescent : baseEnd_2152549 < baseStart_2152549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152562 : List Nat := [3, 2, 1, 2, 2, 3, 1, 3, 5]
def baseStart_2152562 : Nat := 118140960795 + 2152562 * 2 ^ 59
def prefixEnd_2152562 : Nat := 4983230072969 + 3 ^ 40 * 2152562 * 2
def baseEnd_2152562 : Nat := 245621987689669405550123

theorem tailTrace_2152562 : CollatzResearch.WordTrace tailWord_2152562 prefixEnd_2152562 245621987689669405550123 := by
  unfold tailWord_2152562
  simp only [CollatzResearch.WordTrace]
  refine ⟨19627596506910744291580985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52340257351761984777549293 19627596506910744291580985)
  ·
    refine ⟨14720697380183058218685739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19627596506910744291580985 14720697380183058218685739)
    ·
      refine ⟨22081046070274587328028609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14720697380183058218685739 22081046070274587328028609)
      ·
        refine ⟨16560784552705940496021457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22081046070274587328028609 16560784552705940496021457)
        ·
          refine ⟨12420588414529455372016093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16560784552705940496021457 12420588414529455372016093)
          ·
            refine ⟨4657720655448545764506035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12420588414529455372016093 4657720655448545764506035)
            ·
              refine ⟨6986580983172818646759053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4657720655448545764506035 6986580983172818646759053)
              ·
                refine ⟨2619967868689806992534645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6986580983172818646759053 2619967868689806992534645)
                ·
                  refine ⟨245621987689669405550123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2619967868689806992534645 245621987689669405550123)
                  ·
                    rfl

theorem cell22_2152562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_2152562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2152562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2152562 prefixEnd_2152562 := by exact prefixLift 2152562
  have htrace : WordTrace (prefixWord ++ tailWord_2152562) baseStart_2152562 baseEnd_2152562 := by
    simpa [prefixWord, tailWord_2152562, baseEnd_2152562] using wordTrace_append hprefix tailTrace_2152562
  have hstable : (prefixWord ++ tailWord_2152562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152562).length < 2 ^ (prefixWord ++ tailWord_2152562).sum := by decide
  have hdescent : baseEnd_2152562 < baseStart_2152562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152596 : List Nat := [2, 4, 2, 3, 1, 1, 2, 2, 5]
def baseStart_2152596 : Nat := 118140960795 + 2152596 * 2 ^ 59
def prefixEnd_2152596 : Nat := 4983230072969 + 3 ^ 40 * 2152596 * 2
def baseEnd_2152596 : Nat := 245625867321281153766755

theorem tailTrace_2152596 : CollatzResearch.WordTrace tailWord_2152596 prefixEnd_2152596 245625867321281153766755 := by
  unfold tailWord_2152596
  simp only [CollatzResearch.WordTrace]
  refine ⟨39255813054759900486530821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52341084073013200648707761 39255813054759900486530821)
  ·
    refine ⟨7360464947767481341224529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39255813054759900486530821 7360464947767481341224529)
    ·
      refine ⟨5520348710825611005918397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7360464947767481341224529 5520348710825611005918397)
      ·
        refine ⟨2070130766559604127219399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5520348710825611005918397 2070130766559604127219399)
        ·
          refine ⟨3105196149839406190829099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2070130766559604127219399 3105196149839406190829099)
          ·
            refine ⟨4657794224759109286243649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3105196149839406190829099 4657794224759109286243649)
            ·
              refine ⟨3493345668569331964682737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4657794224759109286243649 3493345668569331964682737)
              ·
                refine ⟨2620009251426998973512053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3493345668569331964682737 2620009251426998973512053)
                ·
                  refine ⟨245625867321281153766755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2620009251426998973512053 245625867321281153766755)
                  ·
                    rfl

theorem cell22_2152596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_2152596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2152596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2152596 prefixEnd_2152596 := by exact prefixLift 2152596
  have htrace : WordTrace (prefixWord ++ tailWord_2152596) baseStart_2152596 baseEnd_2152596 := by
    simpa [prefixWord, tailWord_2152596, baseEnd_2152596] using wordTrace_append hprefix tailTrace_2152596
  have hstable : (prefixWord ++ tailWord_2152596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152596).length < 2 ^ (prefixWord ++ tailWord_2152596).sum := by decide
  have hdescent : baseEnd_2152596 < baseStart_2152596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152600 : List Nat := [2, 1, 2, 4, 4, 1, 2, 2, 1, 3]
def baseStart_2152600 : Nat := 118140960795 + 2152600 * 2 ^ 59
def prefixEnd_2152600 : Nat := 4983230072969 + 3 ^ 40 * 2152600 * 2
def baseEnd_2152600 : Nat := 736878971245588784200253

theorem tailTrace_2152600 : CollatzResearch.WordTrace tailWord_2152600 prefixEnd_2152600 736878971245588784200253 := by
  unfold tailWord_2152600
  simp only [CollatzResearch.WordTrace]
  refine ⟨39255886000752654828103627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52341181334336873104138169 39255886000752654828103627)
  ·
    refine ⟨58883829001128982242155441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39255886000752654828103627 58883829001128982242155441)
    ·
      refine ⟨44162871750846736681616581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58883829001128982242155441 44162871750846736681616581)
      ·
        refine ⟨8280538453283763127803109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44162871750846736681616581 8280538453283763127803109)
        ·
          refine ⟨1552600959990705586463083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8280538453283763127803109 1552600959990705586463083)
          ·
            refine ⟨2328901439986058379694625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1552600959990705586463083 2328901439986058379694625)
            ·
              refine ⟨1746676079989543784770969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2328901439986058379694625 1746676079989543784770969)
              ·
                refine ⟨1310007059992157838578227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1746676079989543784770969 1310007059992157838578227)
                ·
                  refine ⟨1965010589988236757867341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1310007059992157838578227 1965010589988236757867341)
                  ·
                    refine ⟨736878971245588784200253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1965010589988236757867341 736878971245588784200253)
                    ·
                      rfl

theorem cell22_2152600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 2, 1, 3].length) (baseStart_2152600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2152600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2152600 prefixEnd_2152600 := by exact prefixLift 2152600
  have htrace : WordTrace (prefixWord ++ tailWord_2152600) baseStart_2152600 baseEnd_2152600 := by
    simpa [prefixWord, tailWord_2152600, baseEnd_2152600] using wordTrace_append hprefix tailTrace_2152600
  have hstable : (prefixWord ++ tailWord_2152600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152600).length < 2 ^ (prefixWord ++ tailWord_2152600).sum := by decide
  have hdescent : baseEnd_2152600 < baseStart_2152600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152665 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 1, 8]
def baseStart_2152665 : Nat := 118140960795 + 2152665 * 2 ^ 59
def prefixEnd_2152665 : Nat := 4983230072969 + 3 ^ 40 * 2152665 * 2
def baseEnd_2152665 : Nat := 736901222073950281325053

theorem tailTrace_2152665 : CollatzResearch.WordTrace tailWord_2152665 prefixEnd_2152665 736901222073950281325053 := by
  unfold tailWord_2152665
  simp only [CollatzResearch.WordTrace]
  refine ⟨78514142746269825757323449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52342761830846550504882299 78514142746269825757323449)
  ·
    refine ⟨58885607059702369317992587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78514142746269825757323449 58885607059702369317992587)
    ·
      refine ⟨88328410589553553976988881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58885607059702369317992587 88328410589553553976988881)
      ·
        refine ⟨66246307942165165482741661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88328410589553553976988881 66246307942165165482741661)
        ·
          refine ⟨24842365478311937056028123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66246307942165165482741661 24842365478311937056028123)
          ·
            refine ⟨37263548217467905584042185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24842365478311937056028123 37263548217467905584042185)
            ·
              refine ⟨27947661163100929188031639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37263548217467905584042185 27947661163100929188031639)
              ·
                refine ⟨41921491744651393782047459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27947661163100929188031639 41921491744651393782047459)
                ·
                  refine ⟨62882237616977090673071189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41921491744651393782047459 62882237616977090673071189)
                  ·
                    refine ⟨736901222073950281325053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62882237616977090673071189 736901222073950281325053)
                    ·
                      rfl

theorem cell22_2152665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 8].length) (baseStart_2152665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2152665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2152665 prefixEnd_2152665 := by exact prefixLift 2152665
  have htrace : WordTrace (prefixWord ++ tailWord_2152665) baseStart_2152665 baseEnd_2152665 := by
    simpa [prefixWord, tailWord_2152665, baseEnd_2152665] using wordTrace_append hprefix tailTrace_2152665
  have hstable : (prefixWord ++ tailWord_2152665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152665).length < 2 ^ (prefixWord ++ tailWord_2152665).sum := by decide
  have hdescent : baseEnd_2152665 < baseStart_2152665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152667 : List Nat := [1, 1, 1, 1, 1, 1, 1, 9, 3, 3]
def baseStart_2152667 : Nat := 118140960795 + 2152667 * 2 ^ 59
def prefixEnd_2152667 : Nat := 4983230072969 + 3 ^ 40 * 2152667 * 2
def baseEnd_2152667 : Nat := 736901906714822942775047

theorem tailTrace_2152667 : CollatzResearch.WordTrace tailWord_2152667 prefixEnd_2152667 736901906714822942775047 := by
  unfold tailWord_2152667
  simp only [CollatzResearch.WordTrace]
  refine ⟨78514215692262580098896255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52342810461508386732597503 78514215692262580098896255)
  ·
    refine ⟨117771323538393870148344383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78514215692262580098896255 117771323538393870148344383)
    ·
      refine ⟨176656985307590805222516575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117771323538393870148344383 176656985307590805222516575)
      ·
        refine ⟨264985477961386207833774863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176656985307590805222516575 264985477961386207833774863)
        ·
          refine ⟨397478216942079311750662295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264985477961386207833774863 397478216942079311750662295)
          ·
            refine ⟨596217325413118967625993443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 397478216942079311750662295 596217325413118967625993443)
            ·
              refine ⟨894325988119678451438990165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 596217325413118967625993443 894325988119678451438990165)
              ·
                refine ⟨5240191336638740926400333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 894325988119678451438990165 5240191336638740926400333)
                ·
                  refine ⟨1965071751239527847400125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5240191336638740926400333 1965071751239527847400125)
                  ·
                    refine ⟨736901906714822942775047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1965071751239527847400125 736901906714822942775047)
                    ·
                      rfl

theorem cell22_2152667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 3, 3].length) (baseStart_2152667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2152667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2152667 prefixEnd_2152667 := by exact prefixLift 2152667
  have htrace : WordTrace (prefixWord ++ tailWord_2152667) baseStart_2152667 baseEnd_2152667 := by
    simpa [prefixWord, tailWord_2152667, baseEnd_2152667] using wordTrace_append hprefix tailTrace_2152667
  have hstable : (prefixWord ++ tailWord_2152667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152667).length < 2 ^ (prefixWord ++ tailWord_2152667).sum := by decide
  have hdescent : baseEnd_2152667 < baseStart_2152667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152718 : List Nat := [4, 1, 1, 2, 1, 2, 5, 2, 1, 3]
def baseStart_2152718 : Nat := 118140960795 + 2152718 * 2 ^ 59
def prefixEnd_2152718 : Nat := 4983230072969 + 3 ^ 40 * 2152718 * 2
def baseEnd_2152718 : Nat := 736919365057075809749891

theorem tailTrace_2152718 : CollatzResearch.WordTrace tailWord_2152718 prefixEnd_2152718 736919365057075809749891 := by
  unfold tailWord_2152718
  simp only [CollatzResearch.WordTrace]
  refine ⟨9814509476884726976125351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52344050543385210539335205 9814509476884726976125351)
  ·
    refine ⟨14721764215327090464188027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9814509476884726976125351 14721764215327090464188027)
    ·
      refine ⟨22082646322990635696282041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14721764215327090464188027 22082646322990635696282041)
      ·
        refine ⟨16561984742242976772211531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22082646322990635696282041 16561984742242976772211531)
        ·
          refine ⟨24842977113364465158317297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16561984742242976772211531 24842977113364465158317297)
          ·
            refine ⟨18632232835023348868737973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24842977113364465158317297 18632232835023348868737973)
            ·
              refine ⟨1746771828283438956444185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18632232835023348868737973 1746771828283438956444185)
              ·
                refine ⟨1310078871212579217333139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1746771828283438956444185 1310078871212579217333139)
                ·
                  refine ⟨1965118306818868825999709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1310078871212579217333139 1965118306818868825999709)
                  ·
                    refine ⟨736919365057075809749891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1965118306818868825999709 736919365057075809749891)
                    ·
                      rfl

theorem cell22_2152718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 2, 1, 3].length) (baseStart_2152718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2152718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2152718 prefixEnd_2152718 := by exact prefixLift 2152718
  have htrace : WordTrace (prefixWord ++ tailWord_2152718) baseStart_2152718 baseEnd_2152718 := by
    simpa [prefixWord, tailWord_2152718, baseEnd_2152718] using wordTrace_append hprefix tailTrace_2152718
  have hstable : (prefixWord ++ tailWord_2152718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152718).length < 2 ^ (prefixWord ++ tailWord_2152718).sum := by decide
  have hdescent : baseEnd_2152718 < baseStart_2152718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152776 : List Nat := [2, 1, 3, 1, 1, 2, 6, 2, 4]
def baseStart_2152776 : Nat := 118140960795 + 2152776 * 2 ^ 59
def prefixEnd_2152776 : Nat := 4983230072969 + 3 ^ 40 * 2152776 * 2
def baseEnd_2152776 : Nat := 245646406547460997266571

theorem tailTrace_2152776 : CollatzResearch.WordTrace tailWord_2152776 prefixEnd_2152776 245646406547460997266571 := by
  unfold tailWord_2152776
  simp only [CollatzResearch.WordTrace]
  refine ⟨39259095624433845857307091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52345460832578461143076121 39259095624433845857307091)
  ·
    refine ⟨58888643436650768785960637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39259095624433845857307091 58888643436650768785960637)
    ·
      refine ⟨22083241288744038294735239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58888643436650768785960637 22083241288744038294735239)
      ·
        refine ⟨33124861933116057442102859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22083241288744038294735239 33124861933116057442102859)
        ·
          refine ⟨49687292899674086163154289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33124861933116057442102859 49687292899674086163154289)
          ·
            refine ⟨37265469674755564622365717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49687292899674086163154289 37265469674755564622365717)
            ·
              refine ⟨1746818891004167091673393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37265469674755564622365717 1746818891004167091673393)
              ·
                refine ⟨1310114168253125318755045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1746818891004167091673393 1310114168253125318755045)
                ·
                  refine ⟨245646406547460997266571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1310114168253125318755045 245646406547460997266571)
                  ·
                    rfl

theorem cell22_2152776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 2, 4].length) (baseStart_2152776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2152776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2152776 prefixEnd_2152776 := by exact prefixLift 2152776
  have htrace : WordTrace (prefixWord ++ tailWord_2152776) baseStart_2152776 baseEnd_2152776 := by
    simpa [prefixWord, tailWord_2152776, baseEnd_2152776] using wordTrace_append hprefix tailTrace_2152776
  have hstable : (prefixWord ++ tailWord_2152776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152776).length < 2 ^ (prefixWord ++ tailWord_2152776).sum := by decide
  have hdescent : baseEnd_2152776 < baseStart_2152776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152804 : List Nat := [2, 3, 1, 1, 3, 1, 5, 6]
def baseStart_2152804 : Nat := 118140960795 + 2152804 * 2 ^ 59
def prefixEnd_2152804 : Nat := 4983230072969 + 3 ^ 40 * 2152804 * 2
def baseEnd_2152804 : Nat := 81883200512733361344403

theorem tailTrace_2152804 : CollatzResearch.WordTrace tailWord_2152804 prefixEnd_2152804 81883200512733361344403 := by
  unfold tailWord_2152804
  simp only [CollatzResearch.WordTrace]
  refine ⟨39259606246383126248316733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52346141661844168331088977 39259606246383126248316733)
  ·
    refine ⟨14722352342393672343118775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39259606246383126248316733 14722352342393672343118775)
    ·
      refine ⟨22083528513590508514678163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14722352342393672343118775 22083528513590508514678163)
      ·
        refine ⟨33125292770385762772017245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22083528513590508514678163 33125292770385762772017245)
        ·
          refine ⟨12421984788894661039506467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33125292770385762772017245 12421984788894661039506467)
          ·
            refine ⟨18632977183341991559259701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12421984788894661039506467 18632977183341991559259701)
            ·
              refine ⟨1746841610938311708680597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18632977183341991559259701 1746841610938311708680597)
              ·
                refine ⟨81883200512733361344403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1746841610938311708680597 81883200512733361344403)
                ·
                  rfl

theorem cell22_2152804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 6].length) (baseStart_2152804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2152804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2152804 prefixEnd_2152804 := by exact prefixLift 2152804
  have htrace : WordTrace (prefixWord ++ tailWord_2152804) baseStart_2152804 baseEnd_2152804 := by
    simpa [prefixWord, tailWord_2152804, baseEnd_2152804] using wordTrace_append hprefix tailTrace_2152804
  have hstable : (prefixWord ++ tailWord_2152804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152804).length < 2 ^ (prefixWord ++ tailWord_2152804).sum := by decide
  have hdescent : baseEnd_2152804 < baseStart_2152804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152836 : List Nat := [2, 3, 2, 1, 1, 2, 4, 1, 3, 3]
def baseStart_2152836 : Nat := 118140960795 + 2152836 * 2 ^ 59
def prefixEnd_2152836 : Nat := 4983230072969 + 3 ^ 40 * 2152836 * 2
def baseEnd_2152836 : Nat := 736959758868562835299529

theorem tailTrace_2152836 : CollatzResearch.WordTrace tailWord_2152836 prefixEnd_2152836 736959758868562835299529 := by
  unfold tailWord_2152836
  simp only [CollatzResearch.WordTrace]
  refine ⟨39260189814325160980899181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52346919752433547974532241 39260189814325160980899181)
  ·
    refine ⟨14722571180371935367837193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39260189814325160980899181 14722571180371935367837193)
    ·
      refine ⟨11041928385278951525877895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14722571180371935367837193 11041928385278951525877895)
      ·
        refine ⟨16562892577918427288816843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11041928385278951525877895 16562892577918427288816843)
        ·
          refine ⟨24844338866877640933225265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16562892577918427288816843 24844338866877640933225265)
          ·
            refine ⟨18633254150158230699918949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24844338866877640933225265 18633254150158230699918949)
            ·
              refine ⟨3493735153154668256234803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18633254150158230699918949 3493735153154668256234803)
              ·
                refine ⟨5240602729732002384352205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3493735153154668256234803 5240602729732002384352205)
                ·
                  refine ⟨1965226023649500894132077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5240602729732002384352205 1965226023649500894132077)
                  ·
                    refine ⟨736959758868562835299529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1965226023649500894132077 736959758868562835299529)
                    ·
                      rfl

theorem cell22_2152836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_2152836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2152836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2152836 prefixEnd_2152836 := by exact prefixLift 2152836
  have htrace : WordTrace (prefixWord ++ tailWord_2152836) baseStart_2152836 baseEnd_2152836 := by
    simpa [prefixWord, tailWord_2152836, baseEnd_2152836] using wordTrace_append hprefix tailTrace_2152836
  have hstable : (prefixWord ++ tailWord_2152836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152836).length < 2 ^ (prefixWord ++ tailWord_2152836).sum := by decide
  have hdescent : baseEnd_2152836 < baseStart_2152836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152900 : List Nat := [2, 3, 3, 2, 2, 2, 2, 1, 5]
def baseStart_2152900 : Nat := 118140960795 + 2152900 * 2 ^ 59
def prefixEnd_2152900 : Nat := 4983230072969 + 3 ^ 40 * 2152900 * 2
def baseEnd_2152900 : Nat := 245660555792162667233111

theorem tailTrace_2152900 : CollatzResearch.WordTrace tailWord_2152900 prefixEnd_2152900 245660555792162667233111 := by
  unfold tailWord_2152900
  simp only [CollatzResearch.WordTrace]
  refine ⟨39261356950209230446064077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52348475933612307261418769 39261356950209230446064077)
  ·
    refine ⟨14723008856328461417274029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39261356950209230446064077 14723008856328461417274029)
    ·
      refine ⟨5521128321123173031477761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14723008856328461417274029 5521128321123173031477761)
      ·
        refine ⟨4140846240842379773608321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5521128321123173031477761 4140846240842379773608321)
        ·
          refine ⟨3105634680631784830206241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4140846240842379773608321 3105634680631784830206241)
          ·
            refine ⟨2329226010473838622654681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3105634680631784830206241 2329226010473838622654681)
            ·
              refine ⟨1746919507855378966991011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2329226010473838622654681 1746919507855378966991011)
              ·
                refine ⟨2620379261783068450486517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1746919507855378966991011 2620379261783068450486517)
                ·
                  refine ⟨245660555792162667233111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2620379261783068450486517 245660555792162667233111)
                  ·
                    rfl

theorem cell22_2152900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_2152900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2152900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2152900 prefixEnd_2152900 := by exact prefixLift 2152900
  have htrace : WordTrace (prefixWord ++ tailWord_2152900) baseStart_2152900 baseEnd_2152900 := by
    simpa [prefixWord, tailWord_2152900, baseEnd_2152900] using wordTrace_append hprefix tailTrace_2152900
  have hstable : (prefixWord ++ tailWord_2152900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152900).length < 2 ^ (prefixWord ++ tailWord_2152900).sum := by decide
  have hdescent : baseEnd_2152900 < baseStart_2152900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152971 : List Nat := [1, 1, 1, 1, 7, 1, 1, 1, 5, 3]
def baseStart_2152971 : Nat := 118140960795 + 2152971 * 2 ^ 59
def prefixEnd_2152971 : Nat := 4983230072969 + 3 ^ 40 * 2152971 * 2
def baseEnd_2152971 : Nat := 737005972127467483174115

theorem tailTrace_2152971 : CollatzResearch.WordTrace tailWord_2152971 prefixEnd_2152971 737005972127467483174115 := by
  unfold tailWord_2152971
  simp only [CollatzResearch.WordTrace]
  refine ⟨78525303483161240017962767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52350202322107493345308511 78525303483161240017962767)
  ·
    refine ⟨117787955224741860026944151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78525303483161240017962767 117787955224741860026944151)
    ·
      refine ⟨176681932837112790040416227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117787955224741860026944151 176681932837112790040416227)
      ·
        refine ⟨265022899255669185060624341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176681932837112790040416227 265022899255669185060624341)
        ·
          refine ⟨6211474201304746524858383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 265022899255669185060624341 6211474201304746524858383)
          ·
            refine ⟨9317211301957119787287575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6211474201304746524858383 9317211301957119787287575)
            ·
              refine ⟨13975816952935679680931363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9317211301957119787287575 13975816952935679680931363)
              ·
                refine ⟨20963725429403519521397045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13975816952935679680931363 20963725429403519521397045)
                ·
                  refine ⟨1965349259006579955130973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20963725429403519521397045 1965349259006579955130973)
                  ·
                    refine ⟨737005972127467483174115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1965349259006579955130973 737005972127467483174115)
                    ·
                      rfl

theorem cell22_2152971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 5, 3].length) (baseStart_2152971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2152971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2152971 prefixEnd_2152971 := by exact prefixLift 2152971
  have htrace : WordTrace (prefixWord ++ tailWord_2152971) baseStart_2152971 baseEnd_2152971 := by
    simpa [prefixWord, tailWord_2152971, baseEnd_2152971] using wordTrace_append hprefix tailTrace_2152971
  have hstable : (prefixWord ++ tailWord_2152971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152971).length < 2 ^ (prefixWord ++ tailWord_2152971).sum := by decide
  have hdescent : baseEnd_2152971 < baseStart_2152971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153018 : List Nat := [3, 1, 1, 1, 3, 4, 3, 1, 5]
def baseStart_2153018 : Nat := 118140960795 + 2153018 * 2 ^ 59
def prefixEnd_2153018 : Nat := 4983230072969 + 3 ^ 40 * 2153018 * 2
def baseEnd_2153018 : Nat := 245674020395991675749657

theorem tailTrace_2153018 : CollatzResearch.WordTrace tailWord_2153018 prefixEnd_2153018 245674020395991675749657 := by
  unfold tailWord_2153018
  simp only [CollatzResearch.WordTrace]
  refine ⟨19631754428497741761230927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52351345142660644696615805 19631754428497741761230927)
  ·
    refine ⟨29447631642746612641846391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19631754428497741761230927 29447631642746612641846391)
    ·
      refine ⟨44171447464119918962769587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29447631642746612641846391 44171447464119918962769587)
      ·
        refine ⟨66257171196179878444154381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44171447464119918962769587 66257171196179878444154381)
        ·
          refine ⟨24846439198567454416557893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66257171196179878444154381 24846439198567454416557893)
          ·
            refine ⟨4658707349731397703104605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24846439198567454416557893 4658707349731397703104605)
            ·
              refine ⟨1747015256149274138664227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4658707349731397703104605 1747015256149274138664227)
              ·
                refine ⟨2620522884223911207996341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1747015256149274138664227 2620522884223911207996341)
                ·
                  refine ⟨245674020395991675749657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2620522884223911207996341 245674020395991675749657)
                  ·
                    rfl

theorem cell22_2153018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 5].length) (baseStart_2153018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2153018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2153018 prefixEnd_2153018 := by exact prefixLift 2153018
  have htrace : WordTrace (prefixWord ++ tailWord_2153018) baseStart_2153018 baseEnd_2153018 := by
    simpa [prefixWord, tailWord_2153018, baseEnd_2153018] using wordTrace_append hprefix tailTrace_2153018
  have hstable : (prefixWord ++ tailWord_2153018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153018).length < 2 ^ (prefixWord ++ tailWord_2153018).sum := by decide
  have hdescent : baseEnd_2153018 < baseStart_2153018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153093 : List Nat := [1, 3, 1, 1, 4, 3, 2, 1, 2, 4]
def baseStart_2153093 : Nat := 118140960795 + 2153093 * 2 ^ 59
def prefixEnd_2153093 : Nat := 4983230072969 + 3 ^ 40 * 2153093 * 2
def baseEnd_2153093 : Nat := 737047735220699831623741

theorem tailTrace_2153093 : CollatzResearch.WordTrace tailWord_2153093 prefixEnd_2153093 737047735220699831623741 := by
  unfold tailWord_2153093
  simp only [CollatzResearch.WordTrace]
  refine ⟨78529753188719254853903933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52353168792479503235935955 78529753188719254853903933)
  ·
    refine ⟨29448657445769720570213975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78529753188719254853903933 29448657445769720570213975)
    ·
      refine ⟨44172986168654580855320963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29448657445769720570213975 44172986168654580855320963)
      ·
        refine ⟨66259479252981871282981445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44172986168654580855320963 66259479252981871282981445)
        ·
          refine ⟨12423652359934100865559021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66259479252981871282981445 12423652359934100865559021)
          ·
            refine ⟨4658869634975287824584633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12423652359934100865559021 4658869634975287824584633)
            ·
              refine ⟨3494152226231465868438475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4658869634975287824584633 3494152226231465868438475)
              ·
                refine ⟨5241228339347198802657713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3494152226231465868438475 5241228339347198802657713)
                ·
                  refine ⟨3930921254510399101993285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5241228339347198802657713 3930921254510399101993285)
                  ·
                    refine ⟨737047735220699831623741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3930921254510399101993285 737047735220699831623741)
                    ·
                      rfl

theorem cell22_2153093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 4].length) (baseStart_2153093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2153093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2153093 prefixEnd_2153093 := by exact prefixLift 2153093
  have htrace : WordTrace (prefixWord ++ tailWord_2153093) baseStart_2153093 baseEnd_2153093 := by
    simpa [prefixWord, tailWord_2153093, baseEnd_2153093] using wordTrace_append hprefix tailTrace_2153093
  have hstable : (prefixWord ++ tailWord_2153093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153093).length < 2 ^ (prefixWord ++ tailWord_2153093).sum := by decide
  have hdescent : baseEnd_2153093 < baseStart_2153093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153114 : List Nat := [3, 1, 1, 6, 1, 2, 2, 2, 4]
def baseStart_2153114 : Nat := 118140960795 + 2153114 * 2 ^ 59
def prefixEnd_2153114 : Nat := 4983230072969 + 3 ^ 40 * 2153114 * 2
def baseEnd_2153114 : Nat := 245684974649954258949559

theorem tailTrace_2153114 : CollatzResearch.WordTrace tailWord_2153114 prefixEnd_2153114 245684974649954258949559 := by
  unfold tailWord_2153114
  simp only [CollatzResearch.WordTrace]
  refine ⟨19632629780410793860104599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52353679414428783626945597 19632629780410793860104599)
  ·
    refine ⟨29448944670616190790156899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19632629780410793860104599 29448944670616190790156899)
    ·
      refine ⟨44173417005924286185235349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29448944670616190790156899 44173417005924286185235349)
      ·
        refine ⟨2070628922152700914932907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 44173417005924286185235349 2070628922152700914932907)
        ·
          refine ⟨3105943383229051372399361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2070628922152700914932907 3105943383229051372399361)
          ·
            refine ⟨2329457537421788529299521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3105943383229051372399361 2329457537421788529299521)
            ·
              refine ⟨1747093153066341396974641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2329457537421788529299521 1747093153066341396974641)
              ·
                refine ⟨1310319864799756047730981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1747093153066341396974641 1310319864799756047730981)
                ·
                  refine ⟨245684974649954258949559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1310319864799756047730981 245684974649954258949559)
                  ·
                    rfl

theorem cell22_2153114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 2, 4].length) (baseStart_2153114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2153114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2153114 prefixEnd_2153114 := by exact prefixLift 2153114
  have htrace : WordTrace (prefixWord ++ tailWord_2153114) baseStart_2153114 baseEnd_2153114 := by
    simpa [prefixWord, tailWord_2153114, baseEnd_2153114] using wordTrace_append hprefix tailTrace_2153114
  have hstable : (prefixWord ++ tailWord_2153114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153114).length < 2 ^ (prefixWord ++ tailWord_2153114).sum := by decide
  have hdescent : baseEnd_2153114 < baseStart_2153114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153142 : List Nat := [5, 1, 3, 1, 2, 1, 3, 6]
def baseStart_2153142 : Nat := 118140960795 + 2153142 * 2 ^ 59
def prefixEnd_2153142 : Nat := 4983230072969 + 3 ^ 40 * 2153142 * 2
def baseEnd_2153142 : Nat := 81896056546897781905399

theorem tailTrace_2153142 : CollatzResearch.WordTrace tailWord_2153142 prefixEnd_2153142 81896056546897781905399 := by
  unfold tailWord_2153142
  simp only [CollatzResearch.WordTrace]
  refine ⟨4908221272846358513902355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52354360243694490814958453 4908221272846358513902355)
  ·
    refine ⟨7362331909269537770853533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4908221272846358513902355 7362331909269537770853533)
    ·
      refine ⟨2760874465976076664070075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7362331909269537770853533 2760874465976076664070075)
      ·
        refine ⟨4141311698964114996105113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2760874465976076664070075 4141311698964114996105113)
        ·
          refine ⟨3105983774223086247078835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4141311698964114996105113 3105983774223086247078835)
          ·
            refine ⟨4658975661334629370618253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3105983774223086247078835 4658975661334629370618253)
            ·
              refine ⟨1747115873000486013981845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4658975661334629370618253 1747115873000486013981845)
              ·
                refine ⟨81896056546897781905399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1747115873000486013981845 81896056546897781905399)
                ·
                  rfl

theorem cell22_2153142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_2153142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2153142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2153142 prefixEnd_2153142 := by exact prefixLift 2153142
  have htrace : WordTrace (prefixWord ++ tailWord_2153142) baseStart_2153142 baseEnd_2153142 := by
    simpa [prefixWord, tailWord_2153142, baseEnd_2153142] using wordTrace_append hprefix tailTrace_2153142
  have hstable : (prefixWord ++ tailWord_2153142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153142).length < 2 ^ (prefixWord ++ tailWord_2153142).sum := by decide
  have hdescent : baseEnd_2153142 < baseStart_2153142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153198 : List Nat := [4, 1, 2, 1, 1, 3, 2, 2, 6]
def baseStart_2153198 : Nat := 118140960795 + 2153198 * 2 ^ 59
def prefixEnd_2153198 : Nat := 4983230072969 + 3 ^ 40 * 2153198 * 2
def baseEnd_2153198 : Nat := 245694559622171519249473

theorem tailTrace_2153198 : CollatzResearch.WordTrace tailWord_2153198 prefixEnd_2153198 245694559622171519249473 := by
  unfold tailWord_2153198
  simp only [CollatzResearch.WordTrace]
  refine ⟨9816697856667357223309531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52355721902225905190984165 9816697856667357223309531)
  ·
    refine ⟨14725046785001035834964297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9816697856667357223309531 14725046785001035834964297)
    ·
      refine ⟨11043785088750776876223223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14725046785001035834964297 11043785088750776876223223)
      ·
        refine ⟨16565677633126165314334835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11043785088750776876223223 16565677633126165314334835)
        ·
          refine ⟨24848516449689247971502253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16565677633126165314334835 24848516449689247971502253)
          ·
            refine ⟨9318193668633467989313345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24848516449689247971502253 9318193668633467989313345)
            ·
              refine ⟨6988645251475100991985009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9318193668633467989313345 6988645251475100991985009)
              ·
                refine ⟨5241483938606325743988757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6988645251475100991985009 5241483938606325743988757)
                ·
                  refine ⟨245694559622171519249473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5241483938606325743988757 245694559622171519249473)
                  ·
                    rfl

theorem cell22_2153198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_2153198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2153198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2153198 prefixEnd_2153198 := by exact prefixLift 2153198
  have htrace : WordTrace (prefixWord ++ tailWord_2153198) baseStart_2153198 baseEnd_2153198 := by
    simpa [prefixWord, tailWord_2153198, baseEnd_2153198] using wordTrace_append hprefix tailTrace_2153198
  have hstable : (prefixWord ++ tailWord_2153198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153198).length < 2 ^ (prefixWord ++ tailWord_2153198).sum := by decide
  have hdescent : baseEnd_2153198 < baseStart_2153198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153213 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 6, 3]
def baseStart_2153213 : Nat := 118140960795 + 2153213 * 2 ^ 59
def prefixEnd_2153213 : Nat := 4983230072969 + 3 ^ 40 * 2153213 * 2
def baseEnd_2153213 : Nat := 737088813673059518623373

theorem tailTrace_2153213 : CollatzResearch.WordTrace tailWord_2153213 prefixEnd_2153213 737088813673059518623373 := by
  unfold tailWord_2153213
  simp only [CollatzResearch.WordTrace]
  refine ⟨78534129948284515348272293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52356086632189676898848195 78534129948284515348272293)
  ·
    refine ⟨14725149365303346627801055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78534129948284515348272293 14725149365303346627801055)
    ·
      refine ⟨22087724047955019941701583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14725149365303346627801055 22087724047955019941701583)
      ·
        refine ⟨33131586071932529912552375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22087724047955019941701583 33131586071932529912552375)
        ·
          refine ⟨49697379107898794868828563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33131586071932529912552375 49697379107898794868828563)
          ·
            refine ⟨74546068661848192303242845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49697379107898794868828563 74546068661848192303242845)
            ·
              refine ⟨27954775748193072113716067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74546068661848192303242845 27954775748193072113716067)
              ·
                refine ⟨41932163622289608170574101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27954775748193072113716067 41932163622289608170574101)
                ·
                  refine ⟨1965570169794825382995661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 41932163622289608170574101 1965570169794825382995661)
                  ·
                    refine ⟨737088813673059518623373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1965570169794825382995661 737088813673059518623373)
                    ·
                      rfl

theorem cell22_2153213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_2153213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2153213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2153213 prefixEnd_2153213 := by exact prefixLift 2153213
  have htrace : WordTrace (prefixWord ++ tailWord_2153213) baseStart_2153213 baseEnd_2153213 := by
    simpa [prefixWord, tailWord_2153213, baseEnd_2153213] using wordTrace_append hprefix tailTrace_2153213
  have hstable : (prefixWord ++ tailWord_2153213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153213).length < 2 ^ (prefixWord ++ tailWord_2153213).sum := by decide
  have hdescent : baseEnd_2153213 < baseStart_2153213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153230 : List Nat := [4, 1, 1, 2, 1, 1, 1, 6, 2, 3]
def baseStart_2153230 : Nat := 118140960795 + 2153230 * 2 ^ 59
def prefixEnd_2153230 : Nat := 4983230072969 + 3 ^ 40 * 2153230 * 2
def baseEnd_2153230 : Nat := 737094633120477140948321

theorem tailTrace_2153230 : CollatzResearch.WordTrace tailWord_2153230 prefixEnd_2153230 737094633120477140948321 := by
  unfold tailWord_2153230
  simp only [CollatzResearch.WordTrace]
  refine ⟨9816843748652865906455143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52356499992815284834427429 9816843748652865906455143)
  ·
    refine ⟨14725265622979298859682715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9816843748652865906455143 14725265622979298859682715)
    ·
      refine ⟨22087898434468948289524073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14725265622979298859682715 22087898434468948289524073)
      ·
        refine ⟨16565923825851711217143055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22087898434468948289524073 16565923825851711217143055)
        ·
          refine ⟨24848885738777566825714583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16565923825851711217143055 24848885738777566825714583)
          ·
            refine ⟨37273328608166350238571875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24848885738777566825714583 37273328608166350238571875)
            ·
              refine ⟨55909992912249525357857813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37273328608166350238571875 55909992912249525357857813)
              ·
                refine ⟨2620780917761696501149585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55909992912249525357857813 2620780917761696501149585)
                ·
                  refine ⟨1965585688321272375862189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2620780917761696501149585 1965585688321272375862189)
                  ·
                    refine ⟨737094633120477140948321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1965585688321272375862189 737094633120477140948321)
                    ·
                      rfl

theorem cell22_2153230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_2153230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2153230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2153230 prefixEnd_2153230 := by exact prefixLift 2153230
  have htrace : WordTrace (prefixWord ++ tailWord_2153230) baseStart_2153230 baseEnd_2153230 := by
    simpa [prefixWord, tailWord_2153230, baseEnd_2153230] using wordTrace_append hprefix tailTrace_2153230
  have hstable : (prefixWord ++ tailWord_2153230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153230).length < 2 ^ (prefixWord ++ tailWord_2153230).sum := by decide
  have hdescent : baseEnd_2153230 < baseStart_2153230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153241 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 2, 7]
def baseStart_2153241 : Nat := 118140960795 + 2153241 * 2 ^ 59
def prefixEnd_2153241 : Nat := 4983230072969 + 3 ^ 40 * 2153241 * 2
def baseEnd_2153241 : Nat := 737098398645276778923287

theorem tailTrace_2153241 : CollatzResearch.WordTrace tailWord_2153241 prefixEnd_2153241 737098398645276778923287 := by
  unfold tailWord_2153241
  simp only [CollatzResearch.WordTrace]
  refine ⟨78535151192183076130291577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52356767461455384086861051 78535151192183076130291577)
  ·
    refine ⟨58901363394137307097718683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78535151192183076130291577 58901363394137307097718683)
    ·
      refine ⟨88352045091205960646578025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58901363394137307097718683 88352045091205960646578025)
      ·
        refine ⟨66264033818404470484933519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88352045091205960646578025 66264033818404470484933519)
        ·
          refine ⟨99396050727606705727400279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66264033818404470484933519 99396050727606705727400279)
          ·
            refine ⟨149094076091410058591100419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99396050727606705727400279 149094076091410058591100419)
            ·
              refine ⟨223641114137115087886650629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149094076091410058591100419 223641114137115087886650629)
              ·
                refine ⟨41932708900709078978746993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 223641114137115087886650629 41932708900709078978746993)
                ·
                  refine ⟨31449531675531809234060245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41932708900709078978746993 31449531675531809234060245)
                  ·
                    refine ⟨737098398645276778923287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31449531675531809234060245 737098398645276778923287)
                    ·
                      rfl

theorem cell22_2153241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 7].length) (baseStart_2153241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2153241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2153241 prefixEnd_2153241 := by exact prefixLift 2153241
  have htrace : WordTrace (prefixWord ++ tailWord_2153241) baseStart_2153241 baseEnd_2153241 := by
    simpa [prefixWord, tailWord_2153241, baseEnd_2153241] using wordTrace_append hprefix tailTrace_2153241
  have hstable : (prefixWord ++ tailWord_2153241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153241).length < 2 ^ (prefixWord ++ tailWord_2153241).sum := by decide
  have hdescent : baseEnd_2153241 < baseStart_2153241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153247 : List Nat := [1, 1, 2, 4, 2, 2, 4, 1, 2, 3]
def baseStart_2153247 : Nat := 118140960795 + 2153247 * 2 ^ 59
def prefixEnd_2153247 : Nat := 4983230072969 + 3 ^ 40 * 2153247 * 2
def baseEnd_2153247 : Nat := 737100452567894763273269

theorem tailTrace_2153247 : CollatzResearch.WordTrace tailWord_2153247 prefixEnd_2153247 737100452567894763273269 := by
  unfold tailWord_2153247
  simp only [CollatzResearch.WordTrace]
  refine ⟨78535370030161339155009995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52356913353440892770006663 78535370030161339155009995)
  ·
    refine ⟨117803055045242008732514993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78535370030161339155009995 117803055045242008732514993)
    ·
      refine ⟨88352291283931506549386245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117803055045242008732514993 88352291283931506549386245)
      ·
        refine ⟨16566054615737157478009921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88352291283931506549386245 16566054615737157478009921)
        ·
          refine ⟨12424540961802868108507441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16566054615737157478009921 12424540961802868108507441)
          ·
            refine ⟨9318405721352151081380581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12424540961802868108507441 9318405721352151081380581)
            ·
              refine ⟨1747201072753528327758859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9318405721352151081380581 1747201072753528327758859)
              ·
                refine ⟨2620801609130292491638289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1747201072753528327758859 2620801609130292491638289)
                ·
                  refine ⟨1965601206847719368728717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2620801609130292491638289 1965601206847719368728717)
                  ·
                    refine ⟨737100452567894763273269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1965601206847719368728717 737100452567894763273269)
                    ·
                      rfl

theorem cell22_2153247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 2, 3].length) (baseStart_2153247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2153247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2153247 prefixEnd_2153247 := by exact prefixLift 2153247
  have htrace : WordTrace (prefixWord ++ tailWord_2153247) baseStart_2153247 baseEnd_2153247 := by
    simpa [prefixWord, tailWord_2153247, baseEnd_2153247] using wordTrace_append hprefix tailTrace_2153247
  have hstable : (prefixWord ++ tailWord_2153247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153247).length < 2 ^ (prefixWord ++ tailWord_2153247).sum := by decide
  have hdescent : baseEnd_2153247 < baseStart_2153247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153262 : List Nat := [4, 1, 3, 2, 1, 2, 2, 1, 2, 4]
def baseStart_2153262 : Nat := 118140960795 + 2153262 * 2 ^ 59
def prefixEnd_2153262 : Nat := 4983230072969 + 3 ^ 40 * 2153262 * 2
def baseEnd_2153262 : Nat := 737105587374439724148223

theorem tailTrace_2153262 : CollatzResearch.WordTrace tailWord_2153262 prefixEnd_2153262 737105587374439724148223 := by
  unfold tailWord_2153262
  simp only [CollatzResearch.WordTrace]
  refine ⟨9816989640638374589600755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52357278083404664477870693 9816989640638374589600755)
  ·
    refine ⟨14725484460957561884401133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9816989640638374589600755 14725484460957561884401133)
    ·
      refine ⟨5522056672859085706650425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14725484460957561884401133 5522056672859085706650425)
      ·
        refine ⟨4141542504644314279987819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5522056672859085706650425 4141542504644314279987819)
        ·
          refine ⟨6212313756966471419981729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4141542504644314279987819 6212313756966471419981729)
          ·
            refine ⟨4659235317724853564986297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6212313756966471419981729 4659235317724853564986297)
            ·
              refine ⟨3494426488293640173739723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4659235317724853564986297 3494426488293640173739723)
              ·
                refine ⟨5241639732440460260609585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3494426488293640173739723 5241639732440460260609585)
                ·
                  refine ⟨3931229799330345195457189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5241639732440460260609585 3931229799330345195457189)
                  ·
                    refine ⟨737105587374439724148223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3931229799330345195457189 737105587374439724148223)
                    ·
                      rfl

theorem cell22_2153262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_2153262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2153262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2153262 prefixEnd_2153262 := by exact prefixLift 2153262
  have htrace : WordTrace (prefixWord ++ tailWord_2153262) baseStart_2153262 baseEnd_2153262 := by
    simpa [prefixWord, tailWord_2153262, baseEnd_2153262] using wordTrace_append hprefix tailTrace_2153262
  have hstable : (prefixWord ++ tailWord_2153262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153262).length < 2 ^ (prefixWord ++ tailWord_2153262).sum := by decide
  have hdescent : baseEnd_2153262 < baseStart_2153262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153303 : List Nat := [1, 1, 3, 2, 4, 1, 1, 1, 1, 7]
def baseStart_2153303 : Nat := 118140960795 + 2153303 * 2 ^ 59
def prefixEnd_2153303 : Nat := 4983230072969 + 3 ^ 40 * 2153303 * 2
def baseEnd_2153303 : Nat := 737119622512329283873097

theorem tailTrace_2153303 : CollatzResearch.WordTrace tailWord_2153303 prefixEnd_2153303 737119622512329283873097 := by
  unfold tailWord_2153303
  simp only [CollatzResearch.WordTrace]
  refine ⟨78537412517958460719048563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52358275011972307146032375 78537412517958460719048563)
  ·
    refine ⟨117806118776937691078572845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78537412517958460719048563 117806118776937691078572845)
    ·
      refine ⟨44177294541351634154464817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117806118776937691078572845 44177294541351634154464817)
      ·
        refine ⟨33132970906013725615848613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44177294541351634154464817 33132970906013725615848613)
        ·
          refine ⟨6212432044877573552971615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33132970906013725615848613 6212432044877573552971615)
          ·
            refine ⟨9318648067316360329457423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6212432044877573552971615 9318648067316360329457423)
            ·
              refine ⟨13977972100974540494186135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9318648067316360329457423 13977972100974540494186135)
              ·
                refine ⟨20966958151461810741279203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13977972100974540494186135 20966958151461810741279203)
                ·
                  refine ⟨31450437227192716111918805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20966958151461810741279203 31450437227192716111918805)
                  ·
                    refine ⟨737119622512329283873097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31450437227192716111918805 737119622512329283873097)
                    ·
                      rfl

theorem cell22_2153303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_2153303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2153303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2153303 prefixEnd_2153303 := by exact prefixLift 2153303
  have htrace : WordTrace (prefixWord ++ tailWord_2153303) baseStart_2153303 baseEnd_2153303 := by
    simpa [prefixWord, tailWord_2153303, baseEnd_2153303] using wordTrace_append hprefix tailTrace_2153303
  have hstable : (prefixWord ++ tailWord_2153303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153303).length < 2 ^ (prefixWord ++ tailWord_2153303).sum := by decide
  have hdescent : baseEnd_2153303 < baseStart_2153303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153326 : List Nat := [4, 1, 2, 3, 2, 1, 2, 3, 1, 3]
def baseStart_2153326 : Nat := 118140960795 + 2153326 * 2 ^ 59
def prefixEnd_2153326 : Nat := 4983230072969 + 3 ^ 40 * 2153326 * 2
def baseEnd_2153326 : Nat := 737127495882364890548027

theorem tailTrace_2153326 : CollatzResearch.WordTrace tailWord_2153326 prefixEnd_2153326 737127495882364890548027 := by
  unfold tailWord_2153326
  simp only [CollatzResearch.WordTrace]
  refine ⟨9817281424609391955891979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52358834264583423764757221 9817281424609391955891979)
  ·
    refine ⟨14725922136914087933837969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9817281424609391955891979 14725922136914087933837969)
    ·
      refine ⟨11044441602685565950378477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14725922136914087933837969 11044441602685565950378477)
      ·
        refine ⟨4141665601007087231391929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11044441602685565950378477 4141665601007087231391929)
        ·
          refine ⟨3106249200755315423543947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4141665601007087231391929 3106249200755315423543947)
          ·
            refine ⟨4659373801132973135315921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3106249200755315423543947 4659373801132973135315921)
            ·
              refine ⟨3494530350849729851486941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4659373801132973135315921 3494530350849729851486941)
              ·
                refine ⟨1310448881568648694307603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3494530350849729851486941 1310448881568648694307603)
                ·
                  refine ⟨1965673322352973041461405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1310448881568648694307603 1965673322352973041461405)
                  ·
                    refine ⟨737127495882364890548027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1965673322352973041461405 737127495882364890548027)
                    ·
                      rfl

theorem cell22_2153326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_2153326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2153326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2153326 prefixEnd_2153326 := by exact prefixLift 2153326
  have htrace : WordTrace (prefixWord ++ tailWord_2153326) baseStart_2153326 baseEnd_2153326 := by
    simpa [prefixWord, tailWord_2153326, baseEnd_2153326] using wordTrace_append hprefix tailTrace_2153326
  have hstable : (prefixWord ++ tailWord_2153326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153326).length < 2 ^ (prefixWord ++ tailWord_2153326).sum := by decide
  have hdescent : baseEnd_2153326 < baseStart_2153326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153363 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 6, 4]
def baseStart_2153363 : Nat := 118140960795 + 2153363 * 2 ^ 59
def prefixEnd_2153363 : Nat := 4983230072969 + 3 ^ 40 * 2153363 * 2
def baseEnd_2153363 : Nat := 737140161738509127372913

theorem tailTrace_2153363 : CollatzResearch.WordTrace tailWord_2153363 prefixEnd_2153363 737140161738509127372913 := by
  unfold tailWord_2153363
  simp only [CollatzResearch.WordTrace]
  refine ⟨78539600897741090966232743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52359733931827393977488495 78539600897741090966232743)
  ·
    refine ⟨117809401346611636449349115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78539600897741090966232743 117809401346611636449349115)
    ·
      refine ⟨176714102019917454674023673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117809401346611636449349115 176714102019917454674023673)
      ·
        refine ⟨132535576514938091005517755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176714102019917454674023673 132535576514938091005517755)
        ·
          refine ⟨198803364772407136508276633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132535576514938091005517755 198803364772407136508276633)
          ·
            refine ⟨149102523579305352381207475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198803364772407136508276633 149102523579305352381207475)
            ·
              refine ⟨223653785368958028571811213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149102523579305352381207475 223653785368958028571811213)
              ·
                refine ⟨83870169513359260714429205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 223653785368958028571811213 83870169513359260714429205)
                ·
                  refine ⟨3931414195938715345988869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 83870169513359260714429205 3931414195938715345988869)
                  ·
                    refine ⟨737140161738509127372913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3931414195938715345988869 737140161738509127372913)
                    ·
                      rfl

theorem cell22_2153363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 4].length) (baseStart_2153363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2153363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2153363 prefixEnd_2153363 := by exact prefixLift 2153363
  have htrace : WordTrace (prefixWord ++ tailWord_2153363) baseStart_2153363 baseEnd_2153363 := by
    simpa [prefixWord, tailWord_2153363, baseEnd_2153363] using wordTrace_append hprefix tailTrace_2153363
  have hstable : (prefixWord ++ tailWord_2153363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153363).length < 2 ^ (prefixWord ++ tailWord_2153363).sum := by decide
  have hdescent : baseEnd_2153363 < baseStart_2153363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153365 : List Nat := [1, 3, 2, 1, 1, 4, 3, 1, 1, 5]
def baseStart_2153365 : Nat := 118140960795 + 2153365 * 2 ^ 59
def prefixEnd_2153365 : Nat := 4983230072969 + 3 ^ 40 * 2153365 * 2
def baseEnd_2153365 : Nat := 737140846379381788822907

theorem tailTrace_2153365 : CollatzResearch.WordTrace tailWord_2153365 prefixEnd_2153365 737140846379381788822907 := by
  unfold tailWord_2153365
  simp only [CollatzResearch.WordTrace]
  refine ⟨78539673843733845307805549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52359782562489230205203699 78539673843733845307805549)
  ·
    refine ⟨29452377691400191990427081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78539673843733845307805549 29452377691400191990427081)
    ·
      refine ⟨22089283268550143992820311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29452377691400191990427081 22089283268550143992820311)
      ·
        refine ⟨33133924902825215989230467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22089283268550143992820311 33133924902825215989230467)
        ·
          refine ⟨49700887354237823983845701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33133924902825215989230467 49700887354237823983845701)
          ·
            refine ⟨9318916378919591996971069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49700887354237823983845701 9318916378919591996971069)
            ·
              refine ⟨3494593642094846998864151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9318916378919591996971069 3494593642094846998864151)
              ·
                refine ⟨5241890463142270498296227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3494593642094846998864151 5241890463142270498296227)
                ·
                  refine ⟨7862835694713405747444341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5241890463142270498296227 7862835694713405747444341)
                  ·
                    refine ⟨737140846379381788822907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7862835694713405747444341 737140846379381788822907)
                    ·
                      rfl

theorem cell22_2153365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_2153365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2153365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2153365 prefixEnd_2153365 := by exact prefixLift 2153365
  have htrace : WordTrace (prefixWord ++ tailWord_2153365) baseStart_2153365 baseEnd_2153365 := by
    simpa [prefixWord, tailWord_2153365, baseEnd_2153365] using wordTrace_append hprefix tailTrace_2153365
  have hstable : (prefixWord ++ tailWord_2153365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153365).length < 2 ^ (prefixWord ++ tailWord_2153365).sum := by decide
  have hdescent : baseEnd_2153365 < baseStart_2153365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153380 : List Nat := [2, 3, 1, 2, 1, 2, 2, 3, 2, 4]
def baseStart_2153380 : Nat := 118140960795 + 2153380 * 2 ^ 59
def prefixEnd_2153380 : Nat := 4983230072969 + 3 ^ 40 * 2153380 * 2
def baseEnd_2153380 : Nat := 737145981185926749697861

theorem tailTrace_2153380 : CollatzResearch.WordTrace tailWord_2153380 prefixEnd_2153380 737145981185926749697861 := by
  unfold tailWord_2153380
  simp only [CollatzResearch.WordTrace]
  refine ⟨39270110469339751434800797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52360147292453001913067729 39270110469339751434800797)
  ·
    refine ⟨14726291426002406788050299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39270110469339751434800797 14726291426002406788050299)
    ·
      refine ⟨22089437139003610182075449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14726291426002406788050299 22089437139003610182075449)
      ·
        refine ⟨16567077854252707636556587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22089437139003610182075449 16567077854252707636556587)
        ·
          refine ⟨24850616781379061454834881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16567077854252707636556587 24850616781379061454834881)
          ·
            refine ⟨18637962586034296091126161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24850616781379061454834881 18637962586034296091126161)
            ·
              refine ⟨13978471939525722068344621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18637962586034296091126161 13978471939525722068344621)
              ·
                refine ⟨5241926977322145775629233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13978471939525722068344621 5241926977322145775629233)
                ·
                  refine ⟨3931445232991609331721925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5241926977322145775629233 3931445232991609331721925)
                  ·
                    refine ⟨737145981185926749697861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3931445232991609331721925 737145981185926749697861)
                    ·
                      rfl

theorem cell22_2153380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_2153380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2153380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2153380 prefixEnd_2153380 := by exact prefixLift 2153380
  have htrace : WordTrace (prefixWord ++ tailWord_2153380) baseStart_2153380 baseEnd_2153380 := by
    simpa [prefixWord, tailWord_2153380, baseEnd_2153380] using wordTrace_append hprefix tailTrace_2153380
  have hstable : (prefixWord ++ tailWord_2153380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153380).length < 2 ^ (prefixWord ++ tailWord_2153380).sum := by decide
  have hdescent : baseEnd_2153380 < baseStart_2153380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153416 : List Nat := [2, 1, 3, 1, 5, 2, 2, 1, 2, 3]
def baseStart_2153416 : Nat := 118140960795 + 2153416 * 2 ^ 59
def prefixEnd_2153416 : Nat := 4983230072969 + 3 ^ 40 * 2153416 * 2
def baseEnd_2153416 : Nat := 737158304721634655797751

theorem tailTrace_2153416 : CollatzResearch.WordTrace tailWord_2153416 prefixEnd_2153416 737158304721634655797751 := by
  unfold tailWord_2153416
  simp only [CollatzResearch.WordTrace]
  refine ⟨39270766983274540508956051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52361022644366054011941401 39270766983274540508956051)
  ·
    refine ⟨58906150474911810763434077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39270766983274540508956051 58906150474911810763434077)
    ·
      refine ⟨22089806428091929036287779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58906150474911810763434077 22089806428091929036287779)
      ·
        refine ⟨33134709642137893554431669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22089806428091929036287779 33134709642137893554431669)
        ·
          refine ⟨3106379028950427520727969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33134709642137893554431669 3106379028950427520727969)
          ·
            refine ⟨2329784271712820640545977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3106379028950427520727969 2329784271712820640545977)
            ·
              refine ⟨1747338203784615480409483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2329784271712820640545977 1747338203784615480409483)
              ·
                refine ⟨2621007305676923220614225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1747338203784615480409483 2621007305676923220614225)
                ·
                  refine ⟨1965755479257692415460669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2621007305676923220614225 1965755479257692415460669)
                  ·
                    refine ⟨737158304721634655797751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1965755479257692415460669 737158304721634655797751)
                    ·
                      rfl

theorem cell22_2153416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 2, 3].length) (baseStart_2153416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2153416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2153416 prefixEnd_2153416 := by exact prefixLift 2153416
  have htrace : WordTrace (prefixWord ++ tailWord_2153416) baseStart_2153416 baseEnd_2153416 := by
    simpa [prefixWord, tailWord_2153416, baseEnd_2153416] using wordTrace_append hprefix tailTrace_2153416
  have hstable : (prefixWord ++ tailWord_2153416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153416).length < 2 ^ (prefixWord ++ tailWord_2153416).sum := by decide
  have hdescent : baseEnd_2153416 < baseStart_2153416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153457 : List Nat := [1, 2, 2, 2, 4, 2, 2, 2, 5]
def baseStart_2153457 : Nat := 118140960795 + 2153457 * 2 ^ 59
def prefixEnd_2153457 : Nat := 4983230072969 + 3 ^ 40 * 2153457 * 2
def baseEnd_2153457 : Nat := 245724113286508071840875

theorem tailTrace_2153457 : CollatzResearch.WordTrace tailWord_2153457 prefixEnd_2153457 245724113286508071840875 := by
  unfold tailWord_2153457
  simp only [CollatzResearch.WordTrace]
  refine ⟨78543029359400545020154625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52362019572933696680103083 78543029359400545020154625)
  ·
    refine ⟨58907272019550408765115969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78543029359400545020154625 58907272019550408765115969)
    ·
      refine ⟨44180454014662806573836977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58907272019550408765115969 44180454014662806573836977)
      ·
        refine ⟨33135340510997104930377733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44180454014662806573836977 33135340510997104930377733)
        ·
          refine ⟨6212876345811957174445825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33135340510997104930377733 6212876345811957174445825)
          ·
            refine ⟨4659657259358967880834369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6212876345811957174445825 4659657259358967880834369)
            ·
              refine ⟨3494742944519225910625777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4659657259358967880834369 3494742944519225910625777)
              ·
                refine ⟨2621057208389419432969333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3494742944519225910625777 2621057208389419432969333)
                ·
                  refine ⟨245724113286508071840875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2621057208389419432969333 245724113286508071840875)
                  ·
                    rfl

theorem cell22_2153457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 5].length) (baseStart_2153457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2153457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2153457 prefixEnd_2153457 := by exact prefixLift 2153457
  have htrace : WordTrace (prefixWord ++ tailWord_2153457) baseStart_2153457 baseEnd_2153457 := by
    simpa [prefixWord, tailWord_2153457, baseEnd_2153457] using wordTrace_append hprefix tailTrace_2153457
  have hstable : (prefixWord ++ tailWord_2153457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153457).length < 2 ^ (prefixWord ++ tailWord_2153457).sum := by decide
  have hdescent : baseEnd_2153457 < baseStart_2153457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153515 : List Nat := [1, 1, 1, 1, 2, 1, 6, 1, 4, 4]
def baseStart_2153515 : Nat := 118140960795 + 2153515 * 2 ^ 59
def prefixEnd_2153515 : Nat := 4983230072969 + 3 ^ 40 * 2153515 * 2
def baseEnd_2153515 : Nat := 737192194444831397572447

theorem tailTrace_2153515 : CollatzResearch.WordTrace tailWord_2153515 prefixEnd_2153515 737192194444831397572447 := by
  unfold tailWord_2153515
  simp only [CollatzResearch.WordTrace]
  refine ⟨78545144793190420925765999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52363429862126947283843999 78545144793190420925765999)
  ·
    refine ⟨117817717189785631388648999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78545144793190420925765999 117817717189785631388648999)
    ·
      refine ⟨176726575784678447082973499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117817717189785631388648999 176726575784678447082973499)
      ·
        refine ⟨265089863677017670624460249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176726575784678447082973499 265089863677017670624460249)
        ·
          refine ⟨198817397757763252968345187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 265089863677017670624460249 198817397757763252968345187)
          ·
            refine ⟨298226096636644879452517781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198817397757763252968345187 298226096636644879452517781)
            ·
              refine ⟨13979348279842728724336771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 298226096636644879452517781 13979348279842728724336771)
              ·
                refine ⟨20969022419764093086505157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13979348279842728724336771 20969022419764093086505157)
                ·
                  refine ⟨3931691703705767453719717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20969022419764093086505157 3931691703705767453719717)
                  ·
                    refine ⟨737192194444831397572447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3931691703705767453719717 737192194444831397572447)
                    ·
                      rfl

theorem cell22_2153515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 4].length) (baseStart_2153515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2153515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2153515 prefixEnd_2153515 := by exact prefixLift 2153515
  have htrace : WordTrace (prefixWord ++ tailWord_2153515) baseStart_2153515 baseEnd_2153515 := by
    simpa [prefixWord, tailWord_2153515, baseEnd_2153515] using wordTrace_append hprefix tailTrace_2153515
  have hstable : (prefixWord ++ tailWord_2153515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153515).length < 2 ^ (prefixWord ++ tailWord_2153515).sum := by decide
  have hdescent : baseEnd_2153515 < baseStart_2153515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153534 : List Nat := [4, 2, 1, 3, 1, 1, 3, 1, 1, 5]
def baseStart_2153534 : Nat := 118140960795 + 2153534 * 2 ^ 59
def prefixEnd_2153534 : Nat := 4983230072969 + 3 ^ 40 * 2153534 * 2
def baseEnd_2153534 : Nat := 737198698533121681347389

theorem tailTrace_2153534 : CollatzResearch.WordTrace tailWord_2153534 prefixEnd_2153534 737198698533121681347389 := by
  unfold tailWord_2153534
  simp only [CollatzResearch.WordTrace]
  refine ⟨9818229722515198396338457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52363891853414391447138437 9818229722515198396338457)
  ·
    refine ⟨7363672291886398797253843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9818229722515198396338457 7363672291886398797253843)
    ·
      refine ⟨11045508437829598195880765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7363672291886398797253843 11045508437829598195880765)
      ·
        refine ⟨4142065664186099323455287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11045508437829598195880765 4142065664186099323455287)
        ·
          refine ⟨6213098496279148985182931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4142065664186099323455287 6213098496279148985182931)
          ·
            refine ⟨9319647744418723477774397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6213098496279148985182931 9319647744418723477774397)
            ·
              refine ⟨3494867904157021304165399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9319647744418723477774397 3494867904157021304165399)
              ·
                refine ⟨5242301856235531956248099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3494867904157021304165399 5242301856235531956248099)
                ·
                  refine ⟨7863452784353297934372149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5242301856235531956248099 7863452784353297934372149)
                  ·
                    refine ⟨737198698533121681347389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7863452784353297934372149 737198698533121681347389)
                    ·
                      rfl

theorem cell22_2153534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_2153534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2153534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2153534 prefixEnd_2153534 := by exact prefixLift 2153534
  have htrace : WordTrace (prefixWord ++ tailWord_2153534) baseStart_2153534 baseEnd_2153534 := by
    simpa [prefixWord, tailWord_2153534, baseEnd_2153534] using wordTrace_append hprefix tailTrace_2153534
  have hstable : (prefixWord ++ tailWord_2153534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153534).length < 2 ^ (prefixWord ++ tailWord_2153534).sum := by decide
  have hdescent : baseEnd_2153534 < baseStart_2153534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153566 : List Nat := [4, 4, 1, 1, 1, 1, 1, 1, 4, 4]
def baseStart_2153566 : Nat := 118140960795 + 2153566 * 2 ^ 59
def prefixEnd_2153566 : Nat := 4983230072969 + 3 ^ 40 * 2153566 * 2
def baseEnd_2153566 : Nat := 737209652787084264547291

theorem tailTrace_2153566 : CollatzResearch.WordTrace tailWord_2153566 prefixEnd_2153566 737209652787084264547291 := by
  unfold tailWord_2153566
  simp only [CollatzResearch.WordTrace]
  refine ⟨9818375614500707079484069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52364669944003771090581701 9818375614500707079484069)
  ·
    refine ⟨1840945427718882577403263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9818375614500707079484069 1840945427718882577403263)
    ·
      refine ⟨2761418141578323866104895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1840945427718882577403263 2761418141578323866104895)
      ·
        refine ⟨4142127212367485799157343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2761418141578323866104895 4142127212367485799157343)
        ·
          refine ⟨6213190818551228698736015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4142127212367485799157343 6213190818551228698736015)
          ·
            refine ⟨9319786227826843048104023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6213190818551228698736015 9319786227826843048104023)
            ·
              refine ⟨13979679341740264572156035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9319786227826843048104023 13979679341740264572156035)
              ·
                refine ⟨20969519012610396858234053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13979679341740264572156035 20969519012610396858234053)
                ·
                  refine ⟨3931784814864449410918885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20969519012610396858234053 3931784814864449410918885)
                  ·
                    refine ⟨737209652787084264547291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3931784814864449410918885 737209652787084264547291)
                    ·
                      rfl

theorem cell22_2153566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_2153566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2153566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2153566 prefixEnd_2153566 := by exact prefixLift 2153566
  have htrace : WordTrace (prefixWord ++ tailWord_2153566) baseStart_2153566 baseEnd_2153566 := by
    simpa [prefixWord, tailWord_2153566, baseEnd_2153566] using wordTrace_append hprefix tailTrace_2153566
  have hstable : (prefixWord ++ tailWord_2153566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153566).length < 2 ^ (prefixWord ++ tailWord_2153566).sum := by decide
  have hdescent : baseEnd_2153566 < baseStart_2153566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153630 : List Nat := [4, 3, 1, 1, 2, 1, 4, 2, 1, 3]
def baseStart_2153630 : Nat := 118140960795 + 2153630 * 2 ^ 59
def prefixEnd_2153630 : Nat := 4983230072969 + 3 ^ 40 * 2153630 * 2
def baseEnd_2153630 : Nat := 737231561295009430947095

theorem tailTrace_2153630 : CollatzResearch.WordTrace tailWord_2153630 prefixEnd_2153630 737231561295009430947095 := by
  unfold tailWord_2153630
  simp only [CollatzResearch.WordTrace]
  refine ⟨9818667398471724445775293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52366226125182530377468229 9818667398471724445775293)
  ·
    refine ⟨3682000274426896667165735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9818667398471724445775293 3682000274426896667165735)
    ·
      refine ⟨5523000411640345000748603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3682000274426896667165735 5523000411640345000748603)
      ·
        refine ⟨8284500617460517501122905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5523000411640345000748603 8284500617460517501122905)
        ·
          refine ⟨6213375463095388125842179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8284500617460517501122905 6213375463095388125842179)
          ·
            refine ⟨9320063194643082188763269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6213375463095388125842179 9320063194643082188763269)
            ·
              refine ⟨1747511848995577910393113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9320063194643082188763269 1747511848995577910393113)
              ·
                refine ⟨1310633886746683432794835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1747511848995577910393113 1310633886746683432794835)
                ·
                  refine ⟨1965950830120025149192253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1310633886746683432794835 1965950830120025149192253)
                  ·
                    refine ⟨737231561295009430947095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1965950830120025149192253 737231561295009430947095)
                    ·
                      rfl

theorem cell22_2153630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_2153630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2153630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2153630 prefixEnd_2153630 := by exact prefixLift 2153630
  have htrace : WordTrace (prefixWord ++ tailWord_2153630) baseStart_2153630 baseEnd_2153630 := by
    simpa [prefixWord, tailWord_2153630, baseEnd_2153630] using wordTrace_append hprefix tailTrace_2153630
  have hstable : (prefixWord ++ tailWord_2153630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153630).length < 2 ^ (prefixWord ++ tailWord_2153630).sum := by decide
  have hdescent : baseEnd_2153630 < baseStart_2153630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153639 : List Nat := [1, 1, 6, 2, 1, 1, 1, 2, 3, 4]
def baseStart_2153639 : Nat := 118140960795 + 2153639 * 2 ^ 59
def prefixEnd_2153639 : Nat := 4983230072969 + 3 ^ 40 * 2153639 * 2
def baseEnd_2153639 : Nat := 737234642178936407472067

theorem tailTrace_2153639 : CollatzResearch.WordTrace tailWord_2153639 prefixEnd_2153639 737234642178936407472067 := by
  unfold tailWord_2153639
  simp only [CollatzResearch.WordTrace]
  refine ⟨78549667444741190103279971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52366444963160793402186647 78549667444741190103279971)
  ·
    refine ⟨117824501167111785154919957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78549667444741190103279971 117824501167111785154919957)
    ·
      refine ⟨5523023492208364929136873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 117824501167111785154919957 5523023492208364929136873)
      ·
        refine ⟨4142267619156273696852655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5523023492208364929136873 4142267619156273696852655)
        ·
          refine ⟨6213401428734410545278983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4142267619156273696852655 6213401428734410545278983)
          ·
            refine ⟨9320102143101615817918475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6213401428734410545278983 9320102143101615817918475)
            ·
              refine ⟨13980153214652423726877713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9320102143101615817918475 13980153214652423726877713)
              ·
                refine ⟨10485114910989317795158285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13980153214652423726877713 10485114910989317795158285)
                ·
                  refine ⟨3931918091620994173184357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10485114910989317795158285 3931918091620994173184357)
                  ·
                    refine ⟨737234642178936407472067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3931918091620994173184357 737234642178936407472067)
                    ·
                      rfl

theorem cell22_2153639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_2153639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2153639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2153639 prefixEnd_2153639 := by exact prefixLift 2153639
  have htrace : WordTrace (prefixWord ++ tailWord_2153639) baseStart_2153639 baseEnd_2153639 := by
    simpa [prefixWord, tailWord_2153639, baseEnd_2153639] using wordTrace_append hprefix tailTrace_2153639
  have hstable : (prefixWord ++ tailWord_2153639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153639).length < 2 ^ (prefixWord ++ tailWord_2153639).sum := by decide
  have hdescent : baseEnd_2153639 < baseStart_2153639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153667 : List Nat := [1, 1, 1, 3, 1, 1, 1, 7, 2, 4]
def baseStart_2153667 : Nat := 118140960795 + 2153667 * 2 ^ 59
def prefixEnd_2153667 : Nat := 4983230072969 + 3 ^ 40 * 2153667 * 2
def baseEnd_2153667 : Nat := 737244227151153667771981

theorem tailTrace_2153667 : CollatzResearch.WordTrace tailWord_2153667 prefixEnd_2153667 737244227151153667771981 := by
  unfold tailWord_2153667
  simp only [CollatzResearch.WordTrace]
  refine ⟨78550688688639750885299255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52367125792426500590199503 78550688688639750885299255)
  ·
    refine ⟨117826033032959626327948883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78550688688639750885299255 117826033032959626327948883)
    ·
      refine ⟨176739049549439439491923325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117826033032959626327948883 176739049549439439491923325)
      ·
        refine ⟨66277143581039789809471247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176739049549439439491923325 66277143581039789809471247)
        ·
          refine ⟨99415715371559684714206871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66277143581039789809471247 99415715371559684714206871)
          ·
            refine ⟨149123573057339527071310307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99415715371559684714206871 149123573057339527071310307)
            ·
              refine ⟨223685359586009290606965461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149123573057339527071310307 223685359586009290606965461)
              ·
                refine ⟨5242625615297092748600753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 223685359586009290606965461 5242625615297092748600753)
                ·
                  refine ⟨3931969211472819561450565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5242625615297092748600753 3931969211472819561450565)
                  ·
                    refine ⟨737244227151153667771981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3931969211472819561450565 737244227151153667771981)
                    ·
                      rfl

theorem cell22_2153667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 4].length) (baseStart_2153667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2153667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2153667 prefixEnd_2153667 := by exact prefixLift 2153667
  have htrace : WordTrace (prefixWord ++ tailWord_2153667) baseStart_2153667 baseEnd_2153667 := by
    simpa [prefixWord, tailWord_2153667, baseEnd_2153667] using wordTrace_append hprefix tailTrace_2153667
  have hstable : (prefixWord ++ tailWord_2153667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153667).length < 2 ^ (prefixWord ++ tailWord_2153667).sum := by decide
  have hdescent : baseEnd_2153667 < baseStart_2153667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153682 : List Nat := [3, 2, 2, 2, 1, 1, 11]
def baseStart_2153682 : Nat := 118140960795 + 2153682 * 2 ^ 59
def prefixEnd_2153682 : Nat := 4983230072969 + 3 ^ 40 * 2153682 * 2
def baseEnd_2153682 : Nat := 27305531924359208468405

theorem tailTrace_2153682 : CollatzResearch.WordTrace tailWord_2153682 prefixEnd_2153682 27305531924359208468405 := by
  unfold tailWord_2153682
  simp only [CollatzResearch.WordTrace]
  refine ⟨19637808945896352111773825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52367490522390272298063533 19637808945896352111773825)
  ·
    refine ⟨14728356709422264083830369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19637808945896352111773825 14728356709422264083830369)
    ·
      refine ⟨11046267532066698062872777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14728356709422264083830369 11046267532066698062872777)
      ·
        refine ⟨8284700649050023547154583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11046267532066698062872777 8284700649050023547154583)
        ·
          refine ⟨12427050973575035320731875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8284700649050023547154583 12427050973575035320731875)
          ·
            refine ⟨18640576460362552981097813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12427050973575035320731875 18640576460362552981097813)
            ·
              refine ⟨27305531924359208468405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 18640576460362552981097813 27305531924359208468405)
              ·
                rfl

theorem cell22_2153682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 11].length) (baseStart_2153682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2153682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2153682 prefixEnd_2153682 := by exact prefixLift 2153682
  have htrace : WordTrace (prefixWord ++ tailWord_2153682) baseStart_2153682 baseEnd_2153682 := by
    simpa [prefixWord, tailWord_2153682, baseEnd_2153682] using wordTrace_append hprefix tailTrace_2153682
  have hstable : (prefixWord ++ tailWord_2153682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153682).length < 2 ^ (prefixWord ++ tailWord_2153682).sum := by decide
  have hdescent : baseEnd_2153682 < baseStart_2153682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153703 : List Nat := [1, 1, 5, 3, 3, 1, 1, 1, 1, 5]
def baseStart_2153703 : Nat := 118140960795 + 2153703 * 2 ^ 59
def prefixEnd_2153703 : Nat := 4983230072969 + 3 ^ 40 * 2153703 * 2
def baseEnd_2153703 : Nat := 737256550686861573871871

theorem tailTrace_2153703 : CollatzResearch.WordTrace tailWord_2153703 prefixEnd_2153703 737256550686861573871871 := by
  unfold tailWord_2153703
  simp only [CollatzResearch.WordTrace]
  refine ⟨78552001716509329033609763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52368001144339552689073175 78552001716509329033609763)
  ·
    refine ⟨117828002574763993550414645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78552001716509329033609763 117828002574763993550414645)
    ·
      refine ⟨11046375241384124395351373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 117828002574763993550414645 11046375241384124395351373)
      ·
        refine ⟨4142390715519046648256765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11046375241384124395351373 4142390715519046648256765)
        ·
          refine ⟨1553396518319642493096287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4142390715519046648256765 1553396518319642493096287)
          ·
            refine ⟨2330094777479463739644431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1553396518319642493096287 2330094777479463739644431)
            ·
              refine ⟨3495142166219195609466647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2330094777479463739644431 3495142166219195609466647)
              ·
                refine ⟨5242713249328793414199971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3495142166219195609466647 5242713249328793414199971)
                ·
                  refine ⟨7864069873993190121299957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5242713249328793414199971 7864069873993190121299957)
                  ·
                    refine ⟨737256550686861573871871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7864069873993190121299957 737256550686861573871871)
                    ·
                      rfl

theorem cell22_2153703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_2153703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2153703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2153703 prefixEnd_2153703 := by exact prefixLift 2153703
  have htrace : WordTrace (prefixWord ++ tailWord_2153703) baseStart_2153703 baseEnd_2153703 := by
    simpa [prefixWord, tailWord_2153703, baseEnd_2153703] using wordTrace_append hprefix tailTrace_2153703
  have hstable : (prefixWord ++ tailWord_2153703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153703).length < 2 ^ (prefixWord ++ tailWord_2153703).sum := by decide
  have hdescent : baseEnd_2153703 < baseStart_2153703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153727 : List Nat := [1, 1, 2, 2, 1, 5, 1, 2, 7]
def baseStart_2153727 : Nat := 118140960795 + 2153727 * 2 ^ 59
def prefixEnd_2153727 : Nat := 4983230072969 + 3 ^ 40 * 2153727 * 2
def baseEnd_2153727 : Nat := 245754922125777837090599

theorem tailTrace_2153727 : CollatzResearch.WordTrace tailWord_2153727 prefixEnd_2153727 245754922125777837090599 := by
  unfold tailWord_2153727
  simp only [CollatzResearch.WordTrace]
  refine ⟨78552877068422381132483435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52368584712281587421655623 78552877068422381132483435)
  ·
    refine ⟨117829315602633571698725153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78552877068422381132483435 117829315602633571698725153)
    ·
      refine ⟨88371986701975178774043865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117829315602633571698725153 88371986701975178774043865)
      ·
        refine ⟨66278990026481384080532899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88371986701975178774043865 66278990026481384080532899)
        ·
          refine ⟨99418485039722076120799349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66278990026481384080532899 99418485039722076120799349)
          ·
            refine ⟨9320482972473944636324939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 99418485039722076120799349 9320482972473944636324939)
            ·
              refine ⟨13980724458710916954487409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9320482972473944636324939 13980724458710916954487409)
              ·
                refine ⟨10485543344033187715865557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13980724458710916954487409 10485543344033187715865557)
                ·
                  refine ⟨245754922125777837090599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10485543344033187715865557 245754922125777837090599)
                  ·
                    rfl

theorem cell22_2153727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 7].length) (baseStart_2153727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2153727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2153727 prefixEnd_2153727 := by exact prefixLift 2153727
  have htrace : WordTrace (prefixWord ++ tailWord_2153727) baseStart_2153727 baseEnd_2153727 := by
    simpa [prefixWord, tailWord_2153727, baseEnd_2153727] using wordTrace_append hprefix tailTrace_2153727
  have hstable : (prefixWord ++ tailWord_2153727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153727).length < 2 ^ (prefixWord ++ tailWord_2153727).sum := by decide
  have hdescent : baseEnd_2153727 < baseStart_2153727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153772 : List Nat := [2, 2, 1, 1, 1, 3, 1, 3, 8]
def baseStart_2153772 : Nat := 118140960795 + 2153772 * 2 ^ 59
def prefixEnd_2153772 : Nat := 4983230072969 + 3 ^ 40 * 2153772 * 2
def baseEnd_2153772 : Nat := 245760056932322797965553

theorem tailTrace_2153772 : CollatzResearch.WordTrace tailWord_2153772 prefixEnd_2153772 245760056932322797965553 := by
  unfold tailWord_2153772
  simp only [CollatzResearch.WordTrace]
  refine ⟨39277259176629676908935785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52369678902172902545247713 39277259176629676908935785)
  ·
    refine ⟨29457944382472257681701839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39277259176629676908935785 29457944382472257681701839)
    ·
      refine ⟨44186916573708386522552759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29457944382472257681701839 44186916573708386522552759)
      ·
        refine ⟨66280374860562579783829139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44186916573708386522552759 66280374860562579783829139)
        ·
          refine ⟨99420562290843869675743709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66280374860562579783829139 99420562290843869675743709)
          ·
            refine ⟨37282710859066451128403891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99420562290843869675743709 37282710859066451128403891)
            ·
              refine ⟨55924066288599676692605837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37282710859066451128403891 55924066288599676692605837)
              ·
                refine ⟨20971524858224878759727189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55924066288599676692605837 20971524858224878759727189)
                ·
                  refine ⟨245760056932322797965553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20971524858224878759727189 245760056932322797965553)
                  ·
                    rfl

theorem cell22_2153772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 8].length) (baseStart_2153772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2153772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2153772 prefixEnd_2153772 := by exact prefixLift 2153772
  have htrace : WordTrace (prefixWord ++ tailWord_2153772) baseStart_2153772 baseEnd_2153772 := by
    simpa [prefixWord, tailWord_2153772, baseEnd_2153772] using wordTrace_append hprefix tailTrace_2153772
  have hstable : (prefixWord ++ tailWord_2153772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153772).length < 2 ^ (prefixWord ++ tailWord_2153772).sum := by decide
  have hdescent : baseEnd_2153772 < baseStart_2153772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153806 : List Nat := [4, 1, 1, 1, 1, 1, 5, 4, 4]
def baseStart_2153806 : Nat := 118140960795 + 2153806 * 2 ^ 59
def prefixEnd_2153806 : Nat := 4983230072969 + 3 ^ 40 * 2153806 * 2
def baseEnd_2153806 : Nat := 245763936563934546182185

theorem tailTrace_2153806 : CollatzResearch.WordTrace tailWord_2153806 prefixEnd_2153806 245763936563934546182185 := by
  unfold tailWord_2153806
  simp only [CollatzResearch.WordTrace]
  refine ⟨9819469804392022203076159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52370505623424118416406181 9819469804392022203076159)
  ·
    refine ⟨14729204706588033304614239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9819469804392022203076159 14729204706588033304614239)
    ·
      refine ⟨22093807059882049956921359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14729204706588033304614239 22093807059882049956921359)
      ·
        refine ⟨33140710589823074935382039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22093807059882049956921359 33140710589823074935382039)
        ·
          refine ⟨49711065884734612403073059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33140710589823074935382039 49711065884734612403073059)
          ·
            refine ⟨74566598827101918604609589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49711065884734612403073059 74566598827101918604609589)
            ·
              refine ⟨6990618640040804869182149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74566598827101918604609589 6990618640040804869182149)
              ·
                refine ⟨1310740995007650912971653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6990618640040804869182149 1310740995007650912971653)
                ·
                  refine ⟨245763936563934546182185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1310740995007650912971653 245763936563934546182185)
                  ·
                    rfl

theorem cell22_2153806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_2153806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2153806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2153806 prefixEnd_2153806 := by exact prefixLift 2153806
  have htrace : WordTrace (prefixWord ++ tailWord_2153806) baseStart_2153806 baseEnd_2153806 := by
    simpa [prefixWord, tailWord_2153806, baseEnd_2153806] using wordTrace_append hprefix tailTrace_2153806
  have hstable : (prefixWord ++ tailWord_2153806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153806).length < 2 ^ (prefixWord ++ tailWord_2153806).sum := by decide
  have hdescent : baseEnd_2153806 < baseStart_2153806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153836 : List Nat := [2, 2, 1, 1, 5, 1, 3, 1, 2, 4]
def baseStart_2153836 : Nat := 118140960795 + 2153836 * 2 ^ 59
def prefixEnd_2153836 : Nat := 4983230072969 + 3 ^ 40 * 2153836 * 2
def baseEnd_2153836 : Nat := 737302079304893560296463

theorem tailTrace_2153836 : CollatzResearch.WordTrace tailWord_2153836 prefixEnd_2153836 737302079304893560296463 := by
  unfold tailWord_2153836
  simp only [CollatzResearch.WordTrace]
  refine ⟨39278426312513746374100681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52371235083351661832134241 39278426312513746374100681)
  ·
    refine ⟨29458819734385309780575511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39278426312513746374100681 29458819734385309780575511)
    ·
      refine ⟨44188229601577964670863267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29458819734385309780575511 44188229601577964670863267)
      ·
        refine ⟨66282344402366947006294901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44188229601577964670863267 66282344402366947006294901)
        ·
          refine ⟨6213969787721901281840147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66282344402366947006294901 6213969787721901281840147)
          ·
            refine ⟨9320954681582851922760221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6213969787721901281840147 9320954681582851922760221)
            ·
              refine ⟨3495358005593569471035083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9320954681582851922760221 3495358005593569471035083)
              ·
                refine ⟨5243037008390354206552625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3495358005593569471035083 5243037008390354206552625)
                ·
                  refine ⟨3932277756292765654914469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5243037008390354206552625 3932277756292765654914469)
                  ·
                    refine ⟨737302079304893560296463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3932277756292765654914469 737302079304893560296463)
                    ·
                      rfl

theorem cell22_2153836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 4].length) (baseStart_2153836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2153836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2153836 prefixEnd_2153836 := by exact prefixLift 2153836
  have htrace : WordTrace (prefixWord ++ tailWord_2153836) baseStart_2153836 baseEnd_2153836 := by
    simpa [prefixWord, tailWord_2153836, baseEnd_2153836] using wordTrace_append hprefix tailTrace_2153836
  have hstable : (prefixWord ++ tailWord_2153836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153836).length < 2 ^ (prefixWord ++ tailWord_2153836).sum := by decide
  have hdescent : baseEnd_2153836 < baseStart_2153836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153956 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 6, 3]
def baseStart_2153956 : Nat := 118140960795 + 2153956 * 2 ^ 59
def prefixEnd_2153956 : Nat := 4983230072969 + 3 ^ 40 * 2153956 * 2
def baseEnd_2153956 : Nat := 737343157757253247296095

theorem tailTrace_2153956 : CollatzResearch.WordTrace tailWord_2153956 prefixEnd_2153956 737343157757253247296095 := by
  unfold tailWord_2153956
  simp only [CollatzResearch.WordTrace]
  refine ⟨39280614692296376621284861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52374152923061835495046481 39280614692296376621284861)
  ·
    refine ⟨14730230509611141232981823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39280614692296376621284861 14730230509611141232981823)
    ·
      refine ⟨22095345764416711849472735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14730230509611141232981823 22095345764416711849472735)
      ·
        refine ⟨33143018646625067774209103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22095345764416711849472735 33143018646625067774209103)
        ·
          refine ⟨49714527969937601661313655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33143018646625067774209103 49714527969937601661313655)
          ·
            refine ⟨74571791954906402491970483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49714527969937601661313655 74571791954906402491970483)
            ·
              refine ⟨111857687932359603737955725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74571791954906402491970483 111857687932359603737955725)
              ·
                refine ⟨41946632974634851401733397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111857687932359603737955725 41946632974634851401733397)
                ·
                  refine ⟨1966248420686008659456253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 41946632974634851401733397 1966248420686008659456253)
                  ·
                    refine ⟨737343157757253247296095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1966248420686008659456253 737343157757253247296095)
                    ·
                      rfl

theorem cell22_2153956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_2153956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2153956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2153956 prefixEnd_2153956 := by exact prefixLift 2153956
  have htrace : WordTrace (prefixWord ++ tailWord_2153956) baseStart_2153956 baseEnd_2153956 := by
    simpa [prefixWord, tailWord_2153956, baseEnd_2153956] using wordTrace_append hprefix tailTrace_2153956
  have hstable : (prefixWord ++ tailWord_2153956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153956).length < 2 ^ (prefixWord ++ tailWord_2153956).sum := by decide
  have hdescent : baseEnd_2153956 < baseStart_2153956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153969 : List Nat := [1, 2, 2, 2, 3, 12]
def baseStart_2153969 : Nat := 118140960795 + 2153969 * 2 ^ 59
def prefixEnd_2153969 : Nat := 4983230072969 + 3 ^ 40 * 2153969 * 2
def baseEnd_2153969 : Nat := 9103056887937352428655

theorem tailTrace_2153969 : CollatzResearch.WordTrace tailWord_2153969 prefixEnd_2153969 9103056887937352428655 := by
  unfold tailWord_2153969
  simp only [CollatzResearch.WordTrace]
  refine ⟨78561703533545656462792961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52374469022363770975195307 78561703533545656462792961)
  ·
    refine ⟨58921277650159242347094721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78561703533545656462792961 58921277650159242347094721)
    ·
      refine ⟨44190958237619431760321041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58921277650159242347094721 44190958237619431760321041)
      ·
        refine ⟨33143218678214573820240781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44190958237619431760321041 33143218678214573820240781)
        ·
          refine ⟨12428707004330465182590293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33143218678214573820240781 12428707004330465182590293)
          ·
            refine ⟨9103056887937352428655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 12428707004330465182590293 9103056887937352428655)
            ·
              rfl

theorem cell22_2153969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 12].length) (baseStart_2153969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2153969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2153969 prefixEnd_2153969 := by exact prefixLift 2153969
  have htrace : WordTrace (prefixWord ++ tailWord_2153969) baseStart_2153969 baseEnd_2153969 := by
    simpa [prefixWord, tailWord_2153969, baseEnd_2153969] using wordTrace_append hprefix tailTrace_2153969
  have hstable : (prefixWord ++ tailWord_2153969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153969).length < 2 ^ (prefixWord ++ tailWord_2153969).sum := by decide
  have hdescent : baseEnd_2153969 < baseStart_2153969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153999 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 3, 8]
def baseStart_2153999 : Nat := 118140960795 + 2153999 * 2 ^ 59
def prefixEnd_2153999 : Nat := 4983230072969 + 3 ^ 40 * 2153999 * 2
def baseEnd_2153999 : Nat := 737357877536015468470963

theorem tailTrace_2153999 : CollatzResearch.WordTrace tailWord_2153999 prefixEnd_2153999 737357877536015468470963 := by
  unfold tailWord_2153999
  simp only [CollatzResearch.WordTrace]
  refine ⟨78562797723436971586385051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52375198482291314390923367 78562797723436971586385051)
  ·
    refine ⟨117844196585155457379577577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78562797723436971586385051 117844196585155457379577577)
    ·
      refine ⟨88383147438866593034683183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117844196585155457379577577 88383147438866593034683183)
      ·
        refine ⟨132574721158299889552024775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88383147438866593034683183 132574721158299889552024775)
        ·
          refine ⟨198862081737449834328037163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132574721158299889552024775 198862081737449834328037163)
          ·
            refine ⟨298293122606174751492055745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198862081737449834328037163 298293122606174751492055745)
            ·
              refine ⟨223719841954631063619041809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 298293122606174751492055745 223719841954631063619041809)
              ·
                refine ⟨167789881465973297714281357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 223719841954631063619041809 167789881465973297714281357)
                ·
                  refine ⟨62921205549739986642855509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 167789881465973297714281357 62921205549739986642855509)
                  ·
                    refine ⟨737357877536015468470963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62921205549739986642855509 737357877536015468470963)
                    ·
                      rfl

theorem cell22_2153999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 8].length) (baseStart_2153999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2153999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2153999 prefixEnd_2153999 := by exact prefixLift 2153999
  have htrace : WordTrace (prefixWord ++ tailWord_2153999) baseStart_2153999 baseEnd_2153999 := by
    simpa [prefixWord, tailWord_2153999, baseEnd_2153999] using wordTrace_append hprefix tailTrace_2153999
  have hstable : (prefixWord ++ tailWord_2153999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153999).length < 2 ^ (prefixWord ++ tailWord_2153999).sum := by decide
  have hdescent : baseEnd_2153999 < baseStart_2153999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154024 : List Nat := [2, 1, 5, 2, 3, 1, 1, 2, 2, 3]
def baseStart_2154024 : Nat := 118140960795 + 2154024 * 2 ^ 59
def prefixEnd_2154024 : Nat := 4983230072969 + 3 ^ 40 * 2154024 * 2
def baseEnd_2154024 : Nat := 737366435546923736595887

theorem tailTrace_2154024 : CollatzResearch.WordTrace tailWord_2154024 prefixEnd_2154024 737366435546923736595887 := by
  unfold tailWord_2154024
  simp only [CollatzResearch.WordTrace]
  refine ⟨39281854774173200428022563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52375806365564267237363417 39281854774173200428022563)
  ·
    refine ⟨58922782161259800642033845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39281854774173200428022563 58922782161259800642033845)
    ·
      refine ⟨5524010827618106310190673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58922782161259800642033845 5524010827618106310190673)
      ·
        refine ⟨4143008120713579732643005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5524010827618106310190673 4143008120713579732643005)
        ·
          refine ⟨1553628045267592399741127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4143008120713579732643005 1553628045267592399741127)
          ·
            refine ⟨2330442067901388599611691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1553628045267592399741127 2330442067901388599611691)
            ·
              refine ⟨3495663101852082899417537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2330442067901388599611691 3495663101852082899417537)
              ·
                refine ⟨2621747326389062174563153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3495663101852082899417537 2621747326389062174563153)
                ·
                  refine ⟨1966310494791796630922365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2621747326389062174563153 1966310494791796630922365)
                  ·
                    refine ⟨737366435546923736595887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1966310494791796630922365 737366435546923736595887)
                    ·
                      rfl

theorem cell22_2154024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_2154024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2154024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2154024 prefixEnd_2154024 := by exact prefixLift 2154024
  have htrace : WordTrace (prefixWord ++ tailWord_2154024) baseStart_2154024 baseEnd_2154024 := by
    simpa [prefixWord, tailWord_2154024, baseEnd_2154024] using wordTrace_append hprefix tailTrace_2154024
  have hstable : (prefixWord ++ tailWord_2154024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154024).length < 2 ^ (prefixWord ++ tailWord_2154024).sum := by decide
  have hdescent : baseEnd_2154024 < baseStart_2154024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154035 : List Nat := [1, 1, 1, 2, 4, 3, 2, 4, 1, 3]
def baseStart_2154035 : Nat := 118140960795 + 2154035 * 2 ^ 59
def prefixEnd_2154035 : Nat := 4983230072969 + 3 ^ 40 * 2154035 * 2
def baseEnd_2154035 : Nat := 737370201071723374570853

theorem tailTrace_2154035 : CollatzResearch.WordTrace tailWord_2154035 prefixEnd_2154035 737370201071723374570853 := by
  unfold tailWord_2154035
  simp only [CollatzResearch.WordTrace]
  refine ⟨78564110751306549734695559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52376073834204366489797039 78564110751306549734695559)
  ·
    refine ⟨117846166126959824602043339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78564110751306549734695559 117846166126959824602043339)
    ·
      refine ⟨176769249190439736903065009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117846166126959824602043339 176769249190439736903065009)
      ·
        refine ⟨132576936892829802677298757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176769249190439736903065009 132576936892829802677298757)
        ·
          refine ⟨24858175667405588001993517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132576936892829802677298757 24858175667405588001993517)
          ·
            refine ⟨9321815875277095500747569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24858175667405588001993517 9321815875277095500747569)
            ·
              refine ⟨6991361906457821625560677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9321815875277095500747569 6991361906457821625560677)
              ·
                refine ⟨1310880357460841554792627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6991361906457821625560677 1310880357460841554792627)
                ·
                  refine ⟨1966320536191262332188941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1310880357460841554792627 1966320536191262332188941)
                  ·
                    refine ⟨737370201071723374570853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1966320536191262332188941 737370201071723374570853)
                    ·
                      rfl

theorem cell22_2154035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 4, 1, 3].length) (baseStart_2154035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2154035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2154035 prefixEnd_2154035 := by exact prefixLift 2154035
  have htrace : WordTrace (prefixWord ++ tailWord_2154035) baseStart_2154035 baseEnd_2154035 := by
    simpa [prefixWord, tailWord_2154035, baseEnd_2154035] using wordTrace_append hprefix tailTrace_2154035
  have hstable : (prefixWord ++ tailWord_2154035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154035).length < 2 ^ (prefixWord ++ tailWord_2154035).sum := by decide
  have hdescent : baseEnd_2154035 < baseStart_2154035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154054 : List Nat := [6, 1, 1, 1, 4, 1, 2, 6]
def baseStart_2154054 : Nat := 118140960795 + 2154054 * 2 ^ 59
def prefixEnd_2154054 : Nat := 4983230072969 + 3 ^ 40 * 2154054 * 2
def baseEnd_2154054 : Nat := 81930745017779295371755

theorem tailTrace_2154054 : CollatzResearch.WordTrace tailWord_2154054 prefixEnd_2154054 81930745017779295371755 := by
  unfold tailWord_2154054
  simp only [CollatzResearch.WordTrace]
  refine ⟨2455150116819928624363663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 52376535825491810653091477 2455150116819928624363663)
  ·
    refine ⟨3682725175229892936545495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2455150116819928624363663 3682725175229892936545495)
    ·
      refine ⟨5524087762844839404818243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3682725175229892936545495 5524087762844839404818243)
      ·
        refine ⟨8286131644267259107227365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5524087762844839404818243 8286131644267259107227365)
        ·
          refine ⟨1553649683300111082605131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8286131644267259107227365 1553649683300111082605131)
          ·
            refine ⟨2330474524950166623907697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1553649683300111082605131 2330474524950166623907697)
            ·
              refine ⟨1747855893712624967930773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2330474524950166623907697 1747855893712624967930773)
              ·
                refine ⟨81930745017779295371755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1747855893712624967930773 81930745017779295371755)
                ·
                  rfl

theorem cell22_2154054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_2154054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2154054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2154054 prefixEnd_2154054 := by exact prefixLift 2154054
  have htrace : WordTrace (prefixWord ++ tailWord_2154054) baseStart_2154054 baseEnd_2154054 := by
    simpa [prefixWord, tailWord_2154054, baseEnd_2154054] using wordTrace_append hprefix tailTrace_2154054
  have hstable : (prefixWord ++ tailWord_2154054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154054).length < 2 ^ (prefixWord ++ tailWord_2154054).sum := by decide
  have hdescent : baseEnd_2154054 < baseStart_2154054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154106 : List Nat := [3, 1, 1, 1, 1, 1, 1, 6, 1, 6]
def baseStart_2154106 : Nat := 118140960795 + 2154106 * 2 ^ 59
def prefixEnd_2154106 : Nat := 4983230072969 + 3 ^ 40 * 2154106 * 2
def baseEnd_2154106 : Nat := 737394505822702856045635

theorem tailTrace_2154106 : CollatzResearch.WordTrace tailWord_2154106 prefixEnd_2154106 737394505822702856045635 := by
  unfold tailWord_2154106
  simp only [CollatzResearch.WordTrace]
  refine ⟨19641675083512332215132543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52377800222699552573686781 19641675083512332215132543)
  ·
    refine ⟨29462512625268498322698815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19641675083512332215132543 29462512625268498322698815)
    ·
      refine ⟨44193768937902747484048223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29462512625268498322698815 44193768937902747484048223)
      ·
        refine ⟨66290653406854121226072335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44193768937902747484048223 66290653406854121226072335)
        ·
          refine ⟨99435980110281181839108503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66290653406854121226072335 99435980110281181839108503)
          ·
            refine ⟨149153970165421772758662755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99435980110281181839108503 149153970165421772758662755)
            ·
              refine ⟨223730955248132659137994133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149153970165421772758662755 223730955248132659137994133)
              ·
                refine ⟨10487388527256218397093475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 223730955248132659137994133 10487388527256218397093475)
                ·
                  refine ⟨15731082790884327595640213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10487388527256218397093475 15731082790884327595640213)
                  ·
                    refine ⟨737394505822702856045635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15731082790884327595640213 737394505822702856045635)
                    ·
                      rfl

theorem cell22_2154106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_2154106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2154106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2154106 prefixEnd_2154106 := by exact prefixLift 2154106
  have htrace : WordTrace (prefixWord ++ tailWord_2154106) baseStart_2154106 baseEnd_2154106 := by
    simpa [prefixWord, tailWord_2154106, baseEnd_2154106] using wordTrace_append hprefix tailTrace_2154106
  have hstable : (prefixWord ++ tailWord_2154106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154106).length < 2 ^ (prefixWord ++ tailWord_2154106).sum := by decide
  have hdescent : baseEnd_2154106 < baseStart_2154106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154121 : List Nat := [1, 2, 1, 1, 4, 1, 4, 8]
def baseStart_2154121 : Nat := 118140960795 + 2154121 * 2 ^ 59
def prefixEnd_2154121 : Nat := 4983230072969 + 3 ^ 40 * 2154121 * 2
def baseEnd_2154121 : Nat := 81933293403249757435621

theorem tailTrace_2154121 : CollatzResearch.WordTrace tailWord_2154121 prefixEnd_2154121 81933293403249757435621 := by
  unfold tailWord_2154121
  simp only [CollatzResearch.WordTrace]
  refine ⟨78567247428994986422326217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52378164952663324281550811 78567247428994986422326217)
  ·
    refine ⟨58925435571746239816744663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78567247428994986422326217 58925435571746239816744663)
    ·
      refine ⟨88388153357619359725116995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58925435571746239816744663 88388153357619359725116995)
      ·
        refine ⟨132582230036429039587675493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88388153357619359725116995 132582230036429039587675493)
        ·
          refine ⟨24859168131830444922689155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132582230036429039587675493 24859168131830444922689155)
          ·
            refine ⟨37288752197745667384033733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24859168131830444922689155 37288752197745667384033733)
            ·
              refine ⟨6991641037077312634506325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37288752197745667384033733 6991641037077312634506325)
              ·
                refine ⟨81933293403249757435621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6991641037077312634506325 81933293403249757435621)
                ·
                  rfl

theorem cell22_2154121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 8].length) (baseStart_2154121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2154121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2154121 prefixEnd_2154121 := by exact prefixLift 2154121
  have htrace : WordTrace (prefixWord ++ tailWord_2154121) baseStart_2154121 baseEnd_2154121 := by
    simpa [prefixWord, tailWord_2154121, baseEnd_2154121] using wordTrace_append hprefix tailTrace_2154121
  have hstable : (prefixWord ++ tailWord_2154121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154121).length < 2 ^ (prefixWord ++ tailWord_2154121).sum := by decide
  have hdescent : baseEnd_2154121 < baseStart_2154121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154123 : List Nat := [1, 1, 1, 1, 4, 1, 6, 1, 2, 4]
def baseStart_2154123 : Nat := 118140960795 + 2154123 * 2 ^ 59
def prefixEnd_2154123 : Nat := 4983230072969 + 3 ^ 40 * 2154123 * 2
def baseEnd_2154123 : Nat := 737400325270120478370583

theorem tailTrace_2154123 : CollatzResearch.WordTrace tailWord_2154123 prefixEnd_2154123 737400325270120478370583 := by
  unfold tailWord_2154123
  simp only [CollatzResearch.WordTrace]
  refine ⟨78567320374987740763899023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52378213583325160509266015 78567320374987740763899023)
  ·
    refine ⟨117850980562481611145848535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78567320374987740763899023 117850980562481611145848535)
    ·
      refine ⟨176776470843722416718772803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117850980562481611145848535 176776470843722416718772803)
      ·
        refine ⟨265164706265583625078159205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176776470843722416718772803 265164706265583625078159205)
        ·
          refine ⟨49718382424796929702154851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 265164706265583625078159205 49718382424796929702154851)
          ·
            refine ⟨74577573637195394553232277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49718382424796929702154851 74577573637195394553232277)
            ·
              refine ⟨3495823764243534119682763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 74577573637195394553232277 3495823764243534119682763)
              ·
                refine ⟨5243735646365301179524145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3495823764243534119682763 5243735646365301179524145)
                ·
                  refine ⟨3932801734773975884643109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5243735646365301179524145 3932801734773975884643109)
                  ·
                    refine ⟨737400325270120478370583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3932801734773975884643109 737400325270120478370583)
                    ·
                      rfl

theorem cell22_2154123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 4].length) (baseStart_2154123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2154123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2154123 prefixEnd_2154123 := by exact prefixLift 2154123
  have htrace : WordTrace (prefixWord ++ tailWord_2154123) baseStart_2154123 baseEnd_2154123 := by
    simpa [prefixWord, tailWord_2154123, baseEnd_2154123] using wordTrace_append hprefix tailTrace_2154123
  have hstable : (prefixWord ++ tailWord_2154123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154123).length < 2 ^ (prefixWord ++ tailWord_2154123).sum := by decide
  have hdescent : baseEnd_2154123 < baseStart_2154123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154142 : List Nat := [4, 3, 1, 1, 1, 2, 1, 4, 2, 3]
def baseStart_2154142 : Nat := 118140960795 + 2154142 * 2 ^ 59
def prefixEnd_2154142 : Nat := 4983230072969 + 3 ^ 40 * 2154142 * 2
def baseEnd_2154142 : Nat := 737406829358410762145525

theorem tailTrace_2154142 : CollatzResearch.WordTrace tailWord_2154142 prefixEnd_2154142 737406829358410762145525 := by
  unfold tailWord_2154142
  simp only [CollatzResearch.WordTrace]
  refine ⟨9821001670239863376105085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52378675574612604672560453 9821001670239863376105085)
  ·
    refine ⟨3682875626339948766039407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9821001670239863376105085 3682875626339948766039407)
    ·
      refine ⟨5524313439509923149059111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3682875626339948766039407 5524313439509923149059111)
      ·
        refine ⟨8286470159264884723588667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5524313439509923149059111 8286470159264884723588667)
        ·
          refine ⟨12429705238897327085383001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8286470159264884723588667 12429705238897327085383001)
          ·
            refine ⟨9322278929172995314037251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12429705238897327085383001 9322278929172995314037251)
            ·
              refine ⟨13983418393759492971055877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9322278929172995314037251 13983418393759492971055877)
              ·
                refine ⟨2621890948829904932072977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13983418393759492971055877 2621890948829904932072977)
                ·
                  refine ⟨1966418211622428699054733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2621890948829904932072977 1966418211622428699054733)
                  ·
                    refine ⟨737406829358410762145525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1966418211622428699054733 737406829358410762145525)
                    ·
                      rfl

theorem cell22_2154142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_2154142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2154142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2154142 prefixEnd_2154142 := by exact prefixLift 2154142
  have htrace : WordTrace (prefixWord ++ tailWord_2154142) baseStart_2154142 baseEnd_2154142 := by
    simpa [prefixWord, tailWord_2154142, baseEnd_2154142] using wordTrace_append hprefix tailTrace_2154142
  have hstable : (prefixWord ++ tailWord_2154142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154142).length < 2 ^ (prefixWord ++ tailWord_2154142).sum := by decide
  have hdescent : baseEnd_2154142 < baseStart_2154142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154170 : List Nat := [3, 1, 1, 1, 2, 5, 1, 2, 3, 3]
def baseStart_2154170 : Nat := 118140960795 + 2154170 * 2 ^ 59
def prefixEnd_2154170 : Nat := 4983230072969 + 3 ^ 40 * 2154170 * 2
def baseEnd_2154170 : Nat := 737416414330628022445439

theorem tailTrace_2154170 : CollatzResearch.WordTrace tailWord_2154170 prefixEnd_2154170 737416414330628022445439 := by
  unfold tailWord_2154170
  simp only [CollatzResearch.WordTrace]
  refine ⟨19642258651454366947714991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52379356403878311860573309 19642258651454366947714991)
  ·
    refine ⟨29463387977181550421572487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19642258651454366947714991 29463387977181550421572487)
    ·
      refine ⟨44195081965772325632358731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29463387977181550421572487 44195081965772325632358731)
      ·
        refine ⟨66292622948658488448538097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44195081965772325632358731 66292622948658488448538097)
        ·
          refine ⟨49719467211493866336403573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66292622948658488448538097 49719467211493866336403573)
          ·
            refine ⟨4661200051077549969037835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49719467211493866336403573 4661200051077549969037835)
            ·
              refine ⟨6991800076616324953556753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4661200051077549969037835 6991800076616324953556753)
              ·
                refine ⟨5243850057462243715167565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6991800076616324953556753 5243850057462243715167565)
                ·
                  refine ⟨1966443771548341393187837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5243850057462243715167565 1966443771548341393187837)
                  ·
                    refine ⟨737416414330628022445439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1966443771548341393187837 737416414330628022445439)
                    ·
                      rfl

theorem cell22_2154170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 3, 3].length) (baseStart_2154170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2154170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2154170 prefixEnd_2154170 := by exact prefixLift 2154170
  have htrace : WordTrace (prefixWord ++ tailWord_2154170) baseStart_2154170 baseEnd_2154170 := by
    simpa [prefixWord, tailWord_2154170, baseEnd_2154170] using wordTrace_append hprefix tailTrace_2154170
  have hstable : (prefixWord ++ tailWord_2154170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154170).length < 2 ^ (prefixWord ++ tailWord_2154170).sum := by decide
  have hdescent : baseEnd_2154170 < baseStart_2154170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154204 : List Nat := [2, 2, 5, 1, 2, 1, 2, 1, 3, 3]
def baseStart_2154204 : Nat := 118140960795 + 2154204 * 2 ^ 59
def prefixEnd_2154204 : Nat := 4983230072969 + 3 ^ 40 * 2154204 * 2
def baseEnd_2154204 : Nat := 737428053225463267095335

theorem tailTrace_2154204 : CollatzResearch.WordTrace tailWord_2154204 prefixEnd_2154204 737428053225463267095335 := by
  unfold tailWord_2154204
  simp only [CollatzResearch.WordTrace]
  refine ⟨39285137343847145798798833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52380183125129527731731777 39285137343847145798798833)
  ·
    refine ⟨29463853007885359349099125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39285137343847145798798833 29463853007885359349099125)
    ·
      refine ⟨2762236219489252438978043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29463853007885359349099125 2762236219489252438978043)
      ·
        refine ⟨4143354329233878658467065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2762236219489252438978043 4143354329233878658467065)
        ·
          refine ⟨3107515746925408993850299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4143354329233878658467065 3107515746925408993850299)
          ·
            refine ⟨4661273620388113490775449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3107515746925408993850299 4661273620388113490775449)
            ·
              refine ⟨3495955215291085118081587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4661273620388113490775449 3495955215291085118081587)
              ·
                refine ⟨5243932822936627677122381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3495955215291085118081587 5243932822936627677122381)
                ·
                  refine ⟨1966474808601235378920893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5243932822936627677122381 1966474808601235378920893)
                  ·
                    refine ⟨737428053225463267095335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1966474808601235378920893 737428053225463267095335)
                    ·
                      rfl

theorem cell22_2154204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_2154204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2154204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2154204 prefixEnd_2154204 := by exact prefixLift 2154204
  have htrace : WordTrace (prefixWord ++ tailWord_2154204) baseStart_2154204 baseEnd_2154204 := by
    simpa [prefixWord, tailWord_2154204, baseEnd_2154204] using wordTrace_append hprefix tailTrace_2154204
  have hstable : (prefixWord ++ tailWord_2154204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154204).length < 2 ^ (prefixWord ++ tailWord_2154204).sum := by decide
  have hdescent : baseEnd_2154204 < baseStart_2154204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154238 : List Nat := [4, 2, 2, 1, 4, 1, 1, 3, 1, 3]
def baseStart_2154238 : Nat := 118140960795 + 2154238 * 2 ^ 59
def prefixEnd_2154238 : Nat := 4983230072969 + 3 ^ 40 * 2154238 * 2
def baseEnd_2154238 : Nat := 737439692120298511745231

theorem tailTrace_2154238 : CollatzResearch.WordTrace tailWord_2154238 prefixEnd_2154238 737439692120298511745231 := by
  unfold tailWord_2154238
  simp only [CollatzResearch.WordTrace]
  refine ⟨9821439346196389425541921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52381009846380743602890245 9821439346196389425541921)
  ·
    refine ⟨7366079509647292069156441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9821439346196389425541921 7366079509647292069156441)
    ·
      refine ⟨5524559632235469051867331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7366079509647292069156441 5524559632235469051867331)
      ·
        refine ⟨8286839448353203577800997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5524559632235469051867331 8286839448353203577800997)
        ·
          refine ⟨1553782396566225670837687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8286839448353203577800997 1553782396566225670837687)
          ·
            refine ⟨2330673594849338506256531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1553782396566225670837687 2330673594849338506256531)
            ·
              refine ⟨3496010392274007759384797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2330673594849338506256531 3496010392274007759384797)
              ·
                refine ⟨1311003897102752909769299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3496010392274007759384797 1311003897102752909769299)
                ·
                  refine ⟨1966505845654129364653949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1311003897102752909769299 1966505845654129364653949)
                  ·
                    refine ⟨737439692120298511745231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1966505845654129364653949 737439692120298511745231)
                    ·
                      rfl

theorem cell22_2154238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_2154238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2154238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2154238 prefixEnd_2154238 := by exact prefixLift 2154238
  have htrace : WordTrace (prefixWord ++ tailWord_2154238) baseStart_2154238 baseEnd_2154238 := by
    simpa [prefixWord, tailWord_2154238, baseEnd_2154238] using wordTrace_append hprefix tailTrace_2154238
  have hstable : (prefixWord ++ tailWord_2154238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154238).length < 2 ^ (prefixWord ++ tailWord_2154238).sum := by decide
  have hdescent : baseEnd_2154238 < baseStart_2154238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154243 : List Nat := [1, 1, 1, 3, 2, 2, 2, 4, 1, 5]
def baseStart_2154243 : Nat := 118140960795 + 2154243 * 2 ^ 59
def prefixEnd_2154243 : Nat := 4983230072969 + 3 ^ 40 * 2154243 * 2
def baseEnd_2154243 : Nat := 737441403722480165370215

theorem tailTrace_2154243 : CollatzResearch.WordTrace tailWord_2154243 prefixEnd_2154243 737441403722480165370215 := by
  unfold tailWord_2154243
  simp only [CollatzResearch.WordTrace]
  refine ⟨78571697134553001258267383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52381131423035334172178255 78571697134553001258267383)
  ·
    refine ⟨117857545701829501887401075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78571697134553001258267383 117857545701829501887401075)
    ·
      refine ⟨176786318552744252831101613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117857545701829501887401075 176786318552744252831101613)
      ·
        refine ⟨66294869457279094811663105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176786318552744252831101613 66294869457279094811663105)
        ·
          refine ⟨49721152092959321108747329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66294869457279094811663105 49721152092959321108747329)
          ·
            refine ⟨37290864069719490831560497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49721152092959321108747329 37290864069719490831560497)
            ·
              refine ⟨27968148052289618123670373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37290864069719490831560497 27968148052289618123670373)
              ·
                refine ⟨5244027759804303398188195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27968148052289618123670373 5244027759804303398188195)
                ·
                  refine ⟨7866041639706455097282293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5244027759804303398188195 7866041639706455097282293)
                  ·
                    refine ⟨737441403722480165370215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7866041639706455097282293 737441403722480165370215)
                    ·
                      rfl

theorem cell22_2154243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 5].length) (baseStart_2154243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2154243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2154243 prefixEnd_2154243 := by exact prefixLift 2154243
  have htrace : WordTrace (prefixWord ++ tailWord_2154243) baseStart_2154243 baseEnd_2154243 := by
    simpa [prefixWord, tailWord_2154243, baseEnd_2154243] using wordTrace_append hprefix tailTrace_2154243
  have hstable : (prefixWord ++ tailWord_2154243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154243).length < 2 ^ (prefixWord ++ tailWord_2154243).sum := by decide
  have hdescent : baseEnd_2154243 < baseStart_2154243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154273 : List Nat := [1, 2, 3, 2, 1, 3, 1, 9]
def baseStart_2154273 : Nat := 118140960795 + 2154273 * 2 ^ 59
def prefixEnd_2154273 : Nat := 4983230072969 + 3 ^ 40 * 2154273 * 2
def baseEnd_2154273 : Nat := 81939074815063343013347

theorem tailTrace_2154273 : CollatzResearch.WordTrace tailWord_2154273 prefixEnd_2154273 81939074815063343013347 := by
  unfold tailWord_2154273
  simp only [CollatzResearch.WordTrace]
  refine ⟨78572791324444316381859473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52381860882962877587906315 78572791324444316381859473)
  ·
    refine ⟨58929593493333237286394605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78572791324444316381859473 58929593493333237286394605)
    ·
      refine ⟨22098597559999963982397977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58929593493333237286394605 22098597559999963982397977)
      ·
        refine ⟨16573948169999972986798483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22098597559999963982397977 16573948169999972986798483)
        ·
          refine ⟨24860922254999959480197725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16573948169999972986798483 24860922254999959480197725)
          ·
            refine ⟨9322845845624984805074147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24860922254999959480197725 9322845845624984805074147)
            ·
              refine ⟨13984268768437477207611221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9322845845624984805074147 13984268768437477207611221)
              ·
                refine ⟨81939074815063343013347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13984268768437477207611221 81939074815063343013347)
                ·
                  rfl

theorem cell22_2154273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 9].length) (baseStart_2154273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2154273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2154273 prefixEnd_2154273 := by exact prefixLift 2154273
  have htrace : WordTrace (prefixWord ++ tailWord_2154273) baseStart_2154273 baseEnd_2154273 := by
    simpa [prefixWord, tailWord_2154273, baseEnd_2154273] using wordTrace_append hprefix tailTrace_2154273
  have hstable : (prefixWord ++ tailWord_2154273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154273).length < 2 ^ (prefixWord ++ tailWord_2154273).sum := by decide
  have hdescent : baseEnd_2154273 < baseStart_2154273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154277 : List Nat := [1, 3, 1, 2, 3, 3, 1, 3, 2, 3]
def baseStart_2154277 : Nat := 118140960795 + 2154277 * 2 ^ 59
def prefixEnd_2154277 : Nat := 4983230072969 + 3 ^ 40 * 2154277 * 2
def baseEnd_2154277 : Nat := 737453042617315410020111

theorem tailTrace_2154277 : CollatzResearch.WordTrace tailWord_2154277 prefixEnd_2154277 737453042617315410020111 := by
  unfold tailWord_2154277
  simp only [CollatzResearch.WordTrace]
  refine ⟨78572937216429825065005085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52381958144286550043336723 78572937216429825065005085)
  ·
    refine ⟨29464851456161184399376907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78572937216429825065005085 29464851456161184399376907)
    ·
      refine ⟨44197277184241776599065361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29464851456161184399376907 44197277184241776599065361)
      ·
        refine ⟨33147957888181332449299021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44197277184241776599065361 33147957888181332449299021)
        ·
          refine ⟨12430484208067999668487133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33147957888181332449299021 12430484208067999668487133)
          ·
            refine ⟨4661431578025499875682675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12430484208067999668487133 4661431578025499875682675)
            ·
              refine ⟨6992147367038249813524013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4661431578025499875682675 6992147367038249813524013)
              ·
                refine ⟨2622055262639343680071505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6992147367038249813524013 2622055262639343680071505)
                ·
                  refine ⟨1966541446979507760053629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2622055262639343680071505 1966541446979507760053629)
                  ·
                    refine ⟨737453042617315410020111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1966541446979507760053629 737453042617315410020111)
                    ·
                      rfl

theorem cell22_2154277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 2, 3].length) (baseStart_2154277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2154277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2154277 prefixEnd_2154277 := by exact prefixLift 2154277
  have htrace : WordTrace (prefixWord ++ tailWord_2154277) baseStart_2154277 baseEnd_2154277 := by
    simpa [prefixWord, tailWord_2154277, baseEnd_2154277] using wordTrace_append hprefix tailTrace_2154277
  have hstable : (prefixWord ++ tailWord_2154277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154277).length < 2 ^ (prefixWord ++ tailWord_2154277).sum := by decide
  have hdescent : baseEnd_2154277 < baseStart_2154277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154292 : List Nat := [2, 5, 1, 1, 2, 1, 1, 3, 2, 4]
def baseStart_2154292 : Nat := 118140960795 + 2154292 * 2 ^ 59
def prefixEnd_2154292 : Nat := 4983230072969 + 3 ^ 40 * 2154292 * 2
def baseEnd_2154292 : Nat := 737458177423860370895065

theorem tailTrace_2154292 : CollatzResearch.WordTrace tailWord_2154292 prefixEnd_2154292 737458177423860370895065 := by
  unfold tailWord_2154292
  simp only [CollatzResearch.WordTrace]
  refine ⟨39286742155687741313400565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52382322874250321751200753 39286742155687741313400565)
  ·
    refine ⟨3683132077095725748131303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39286742155687741313400565 3683132077095725748131303)
    ·
      refine ⟨5524698115643588622196955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3683132077095725748131303 5524698115643588622196955)
      ·
        refine ⟨8287047173465382933295433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5524698115643588622196955 8287047173465382933295433)
        ·
          refine ⟨6215285380099037199971575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8287047173465382933295433 6215285380099037199971575)
          ·
            refine ⟨9322928070148555799957363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6215285380099037199971575 9322928070148555799957363)
            ·
              refine ⟨13984392105222833699936045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9322928070148555799957363 13984392105222833699936045)
              ·
                refine ⟨5244147039458562637476017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13984392105222833699936045 5244147039458562637476017)
                ·
                  refine ⟨3933110279593921978107013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5244147039458562637476017 3933110279593921978107013)
                  ·
                    refine ⟨737458177423860370895065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3933110279593921978107013 737458177423860370895065)
                    ·
                      rfl

theorem cell22_2154292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_2154292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2154292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2154292 prefixEnd_2154292 := by exact prefixLift 2154292
  have htrace : WordTrace (prefixWord ++ tailWord_2154292) baseStart_2154292 baseEnd_2154292 := by
    simpa [prefixWord, tailWord_2154292, baseEnd_2154292] using wordTrace_append hprefix tailTrace_2154292
  have hstable : (prefixWord ++ tailWord_2154292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154292).length < 2 ^ (prefixWord ++ tailWord_2154292).sum := by decide
  have hdescent : baseEnd_2154292 < baseStart_2154292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154335 : List Nat := [1, 1, 2, 3, 1, 4, 2, 3, 5]
def baseStart_2154335 : Nat := 118140960795 + 2154335 * 2 ^ 59
def prefixEnd_2154335 : Nat := 4983230072969 + 3 ^ 40 * 2154335 * 2
def baseEnd_2154335 : Nat := 245824299067540864023311

theorem tailTrace_2154335 : CollatzResearch.WordTrace tailWord_2154335 prefixEnd_2154335 245824299067540864023311 := by
  unfold tailWord_2154335
  simp only [CollatzResearch.WordTrace]
  refine ⟨78575052650219700970616459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52383368433479800647077639 78575052650219700970616459)
  ·
    refine ⟨117862578975329551455924689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78575052650219700970616459 117862578975329551455924689)
    ·
      refine ⟨88396934231497163591943517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117862578975329551455924689 88396934231497163591943517)
      ·
        refine ⟨33148850336811436346978819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88396934231497163591943517 33148850336811436346978819)
        ·
          refine ⟨49723275505217154520468229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33148850336811436346978819 49723275505217154520468229)
          ·
            refine ⟨9323114157228216472587793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49723275505217154520468229 9323114157228216472587793)
            ·
              refine ⟨6992335617921162354440845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9323114157228216472587793 6992335617921162354440845)
              ·
                refine ⟨2622125856720435882915317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6992335617921162354440845 2622125856720435882915317)
                ·
                  refine ⟨245824299067540864023311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2622125856720435882915317 245824299067540864023311)
                  ·
                    rfl

theorem cell22_2154335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 5].length) (baseStart_2154335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2154335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2154335 prefixEnd_2154335 := by exact prefixLift 2154335
  have htrace : WordTrace (prefixWord ++ tailWord_2154335) baseStart_2154335 baseEnd_2154335 := by
    simpa [prefixWord, tailWord_2154335, baseEnd_2154335] using wordTrace_append hprefix tailTrace_2154335
  have hstable : (prefixWord ++ tailWord_2154335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154335).length < 2 ^ (prefixWord ++ tailWord_2154335).sum := by decide
  have hdescent : baseEnd_2154335 < baseStart_2154335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154363 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 10]
def baseStart_2154363 : Nat := 118140960795 + 2154363 * 2 ^ 59
def prefixEnd_2154363 : Nat := 4983230072969 + 3 ^ 40 * 2154363 * 2
def baseEnd_2154363 : Nat := 245827494058279950789949

theorem tailTrace_2154363 : CollatzResearch.WordTrace tailWord_2154363 prefixEnd_2154363 245827494058279950789949 := by
  unfold tailWord_2154363
  simp only [CollatzResearch.WordTrace]
  refine ⟨78576073894118261752635743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52384049262745507835090495 78576073894118261752635743)
  ·
    refine ⟨117864110841177392628953615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78576073894118261752635743 117864110841177392628953615)
    ·
      refine ⟨176796166261766088943430423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117864110841177392628953615 176796166261766088943430423)
      ·
        refine ⟨265194249392649133415145635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176796166261766088943430423 265194249392649133415145635)
        ·
          refine ⟨397791374088973700122718453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265194249392649133415145635 397791374088973700122718453)
          ·
            refine ⟨37292941320841284386504855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 397791374088973700122718453 37292941320841284386504855)
            ·
              refine ⟨55939411981261926579757283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37292941320841284386504855 55939411981261926579757283)
              ·
                refine ⟨83909117971892889869635925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55939411981261926579757283 83909117971892889869635925)
                ·
                  refine ⟨245827494058279950789949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 83909117971892889869635925 245827494058279950789949)
                  ·
                    rfl

theorem cell22_2154363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 10].length) (baseStart_2154363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2154363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2154363 prefixEnd_2154363 := by exact prefixLift 2154363
  have htrace : WordTrace (prefixWord ++ tailWord_2154363) baseStart_2154363 baseEnd_2154363 := by
    simpa [prefixWord, tailWord_2154363, baseEnd_2154363] using wordTrace_append hprefix tailTrace_2154363
  have hstable : (prefixWord ++ tailWord_2154363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154363).length < 2 ^ (prefixWord ++ tailWord_2154363).sum := by decide
  have hdescent : baseEnd_2154363 < baseStart_2154363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154399 : List Nat := [1, 1, 2, 5, 3, 1, 2, 2, 1, 4]
def baseStart_2154399 : Nat := 118140960795 + 2154399 * 2 ^ 59
def prefixEnd_2154399 : Nat := 4983230072969 + 3 ^ 40 * 2154399 * 2
def baseEnd_2154399 : Nat := 737494805710547758469737

theorem tailTrace_2154399 : CollatzResearch.WordTrace tailWord_2154399 prefixEnd_2154399 737494805710547758469737 := by
  unfold tailWord_2154399
  simp only [CollatzResearch.WordTrace]
  refine ⟨78577386921987839900946251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52384924614658559933964167 78577386921987839900946251)
  ·
    refine ⟨117866080382981759851419377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78577386921987839900946251 117866080382981759851419377)
    ·
      refine ⟨88399560287236319888564533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117866080382981759851419377 88399560287236319888564533)
      ·
        refine ⟨8287458776928404989552925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88399560287236319888564533 8287458776928404989552925)
        ·
          refine ⟨3107797041348151871082347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8287458776928404989552925 3107797041348151871082347)
          ·
            refine ⟨4661695562022227806623521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3107797041348151871082347 4661695562022227806623521)
            ·
              refine ⟨3496271671516670854967641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4661695562022227806623521 3496271671516670854967641)
              ·
                refine ⟨2622203753637503141225731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3496271671516670854967641 2622203753637503141225731)
                ·
                  refine ⟨3933305630456254711838597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2622203753637503141225731 3933305630456254711838597)
                  ·
                    refine ⟨737494805710547758469737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3933305630456254711838597 737494805710547758469737)
                    ·
                      rfl

theorem cell22_2154399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 4].length) (baseStart_2154399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2154399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2154399 prefixEnd_2154399 := by exact prefixLift 2154399
  have htrace : WordTrace (prefixWord ++ tailWord_2154399) baseStart_2154399 baseEnd_2154399 := by
    simpa [prefixWord, tailWord_2154399, baseEnd_2154399] using wordTrace_append hprefix tailTrace_2154399
  have hstable : (prefixWord ++ tailWord_2154399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154399).length < 2 ^ (prefixWord ++ tailWord_2154399).sum := by decide
  have hdescent : baseEnd_2154399 < baseStart_2154399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154491 : List Nat := [1, 1, 1, 1, 1, 3, 8, 2, 1, 3]
def baseStart_2154491 : Nat := 118140960795 + 2154491 * 2 ^ 59
def prefixEnd_2154491 : Nat := 4983230072969 + 3 ^ 40 * 2154491 * 2
def baseEnd_2154491 : Nat := 737526299190690185169455

theorem tailTrace_2154491 : CollatzResearch.WordTrace tailWord_2154491 prefixEnd_2154491 737526299190690185169455 := by
  unfold tailWord_2154491
  simp only [CollatzResearch.WordTrace]
  refine ⟨78580742437654539613295327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52387161625103026408863551 78580742437654539613295327)
  ·
    refine ⟨117871113656481809419942991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78580742437654539613295327 117871113656481809419942991)
    ·
      refine ⟨176806670484722714129914487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117871113656481809419942991 176806670484722714129914487)
      ·
        refine ⟨265210005727084071194871731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176806670484722714129914487 265210005727084071194871731)
        ·
          refine ⟨397815008590626106792307597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265210005727084071194871731 397815008590626106792307597)
          ·
            refine ⟨149180628221484790047115349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 397815008590626106792307597 149180628221484790047115349)
            ·
              refine ⟨1748210486970524883364633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 149180628221484790047115349 1748210486970524883364633)
              ·
                refine ⟨1311157865227893662523475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1748210486970524883364633 1311157865227893662523475)
                ·
                  refine ⟨1966736797841840493785213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1311157865227893662523475 1966736797841840493785213)
                  ·
                    refine ⟨737526299190690185169455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1966736797841840493785213 737526299190690185169455)
                    ·
                      rfl

theorem cell22_2154491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 2, 1, 3].length) (baseStart_2154491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2154491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2154491 prefixEnd_2154491 := by exact prefixLift 2154491
  have htrace : WordTrace (prefixWord ++ tailWord_2154491) baseStart_2154491 baseEnd_2154491 := by
    simpa [prefixWord, tailWord_2154491, baseEnd_2154491] using wordTrace_append hprefix tailTrace_2154491
  have hstable : (prefixWord ++ tailWord_2154491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154491).length < 2 ^ (prefixWord ++ tailWord_2154491).sum := by decide
  have hdescent : baseEnd_2154491 < baseStart_2154491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154515 : List Nat := [1, 1, 1, 2, 1, 4, 3, 1, 8]
def baseStart_2154515 : Nat := 118140960795 + 2154515 * 2 ^ 59
def prefixEnd_2154515 : Nat := 4983230072969 + 3 ^ 40 * 2154515 * 2
def baseEnd_2154515 : Nat := 245844838293720707523127

theorem tailTrace_2154515 : CollatzResearch.WordTrace tailWord_2154515 prefixEnd_2154515 245844838293720707523127 := by
  unfold tailWord_2154515
  simp only [CollatzResearch.WordTrace]
  refine ⟨78581617789567591712168999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52387745193045061141445999 78581617789567591712168999)
  ·
    refine ⟨117872426684351387568253499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78581617789567591712168999 117872426684351387568253499)
    ·
      refine ⟨176808640026527081352380249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117872426684351387568253499 176808640026527081352380249)
      ·
        refine ⟨132606480019895311014285187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176808640026527081352380249 132606480019895311014285187)
        ·
          refine ⟨198909720029842966521427781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132606480019895311014285187 198909720029842966521427781)
          ·
            refine ⟨37295572505595556222767709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 198909720029842966521427781 37295572505595556222767709)
            ·
              refine ⟨13985839689598333583537891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37295572505595556222767709 13985839689598333583537891)
              ·
                refine ⟨20978759534397500375306837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13985839689598333583537891 20978759534397500375306837)
                ·
                  refine ⟨245844838293720707523127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20978759534397500375306837 245844838293720707523127)
                  ·
                    rfl

theorem cell22_2154515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 8].length) (baseStart_2154515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2154515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2154515 prefixEnd_2154515 := by exact prefixLift 2154515
  have htrace : WordTrace (prefixWord ++ tailWord_2154515) baseStart_2154515 baseEnd_2154515 := by
    simpa [prefixWord, tailWord_2154515, baseEnd_2154515] using wordTrace_append hprefix tailTrace_2154515
  have hstable : (prefixWord ++ tailWord_2154515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154515).length < 2 ^ (prefixWord ++ tailWord_2154515).sum := by decide
  have hdescent : baseEnd_2154515 < baseStart_2154515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154549 : List Nat := [1, 3, 3, 1, 1, 1, 4, 4, 4]
def baseStart_2154549 : Nat := 118140960795 + 2154549 * 2 ^ 59
def prefixEnd_2154549 : Nat := 4983230072969 + 3 ^ 40 * 2154549 * 2
def baseEnd_2154549 : Nat := 245848717925332455739759

theorem tailTrace_2154549 : CollatzResearch.WordTrace tailWord_2154549 prefixEnd_2154549 245848717925332455739759 := by
  unfold tailWord_2154549
  simp only [CollatzResearch.WordTrace]
  refine ⟨78582857871444415518906701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52388571914296277012604467 78582857871444415518906701)
  ·
    refine ⟨29468571701791655819590013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78582857871444415518906701 29468571701791655819590013)
    ·
      refine ⟨11050714388171870932346255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29468571701791655819590013 11050714388171870932346255)
      ·
        refine ⟨16576071582257806398519383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11050714388171870932346255 16576071582257806398519383)
        ·
          refine ⟨24864107373386709597779075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16576071582257806398519383 24864107373386709597779075)
          ·
            refine ⟨37296161060080064396668613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24864107373386709597779075 37296161060080064396668613)
            ·
              refine ⟨6993030198765012074375365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37296161060080064396668613 6993030198765012074375365)
              ·
                refine ⟨1311193162268439763945381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6993030198765012074375365 1311193162268439763945381)
                ·
                  refine ⟨245848717925332455739759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1311193162268439763945381 245848717925332455739759)
                  ·
                    rfl

theorem cell22_2154549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 4, 4].length) (baseStart_2154549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2154549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2154549 prefixEnd_2154549 := by exact prefixLift 2154549
  have htrace : WordTrace (prefixWord ++ tailWord_2154549) baseStart_2154549 baseEnd_2154549 := by
    simpa [prefixWord, tailWord_2154549, baseEnd_2154549] using wordTrace_append hprefix tailTrace_2154549
  have hstable : (prefixWord ++ tailWord_2154549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154549).length < 2 ^ (prefixWord ++ tailWord_2154549).sum := by decide
  have hdescent : baseEnd_2154549 < baseStart_2154549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154699 : List Nat := [1, 1, 1, 1, 3, 2, 4, 2, 4, 3]
def baseStart_2154699 : Nat := 118140960795 + 2154699 * 2 ^ 59
def prefixEnd_2154699 : Nat := 4983230072969 + 3 ^ 40 * 2154699 * 2
def baseEnd_2154699 : Nat := 737597501841446975968817

theorem tailTrace_2154699 : CollatzResearch.WordTrace tailWord_2154699 prefixEnd_2154699 737597501841446975968817 := by
  unfold tailWord_2154699
  simp only [CollatzResearch.WordTrace]
  refine ⟨78588328820900991136867151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52392219213933994091244767 78588328820900991136867151)
  ·
    refine ⟨117882493231351486705300727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78588328820900991136867151 117882493231351486705300727)
    ·
      refine ⟨176823739847027230057951091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117882493231351486705300727 176823739847027230057951091)
      ·
        refine ⟨265235609770540845086926637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176823739847027230057951091 265235609770540845086926637)
        ·
          refine ⟨99463353663952816907597489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 265235609770540845086926637 99463353663952816907597489)
          ·
            refine ⟨74597515247964612680698117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99463353663952816907597489 74597515247964612680698117)
            ·
              refine ⟨13987034108993364877630897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74597515247964612680698117 13987034108993364877630897)
              ·
                refine ⟨10490275581745023658223173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13987034108993364877630897 10490275581745023658223173)
                ·
                  refine ⟨1966926671577191935916845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10490275581745023658223173 1966926671577191935916845)
                  ·
                    refine ⟨737597501841446975968817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1966926671577191935916845 737597501841446975968817)
                    ·
                      rfl

theorem cell22_2154699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 4, 3].length) (baseStart_2154699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2154699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2154699 prefixEnd_2154699 := by exact prefixLift 2154699
  have htrace : WordTrace (prefixWord ++ tailWord_2154699) baseStart_2154699 baseEnd_2154699 := by
    simpa [prefixWord, tailWord_2154699, baseEnd_2154699] using wordTrace_append hprefix tailTrace_2154699
  have hstable : (prefixWord ++ tailWord_2154699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154699).length < 2 ^ (prefixWord ++ tailWord_2154699).sum := by decide
  have hdescent : baseEnd_2154699 < baseStart_2154699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154714 : List Nat := [3, 1, 1, 2, 2, 1, 2, 4, 2, 4]
def baseStart_2154714 : Nat := 118140960795 + 2154714 * 2 ^ 59
def prefixEnd_2154714 : Nat := 4983230072969 + 3 ^ 40 * 2154714 * 2
def baseEnd_2154714 : Nat := 737602636647991936843771

theorem tailTrace_2154714 : CollatzResearch.WordTrace tailWord_2154714 prefixEnd_2154714 737602636647991936843771 := by
  unfold tailWord_2154714
  simp only [CollatzResearch.WordTrace]
  refine ⟨19647218978961662174665799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52392583943897765799108797 19647218978961662174665799)
  ·
    refine ⟨29470828468442493261998699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19647218978961662174665799 29470828468442493261998699)
    ·
      refine ⟨44206242702663739892998049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29470828468442493261998699 44206242702663739892998049)
      ·
        refine ⟨33154682026997804919748537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44206242702663739892998049 33154682026997804919748537)
        ·
          refine ⟨24866011520248353689811403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33154682026997804919748537 24866011520248353689811403)
          ·
            refine ⟨37299017280372530534717105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24866011520248353689811403 37299017280372530534717105)
            ·
              refine ⟨27974262960279397901037829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37299017280372530534717105 27974262960279397901037829)
              ·
                refine ⟨5245174305052387106444593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27974262960279397901037829 5245174305052387106444593)
                ·
                  refine ⟨3933880728789290329833445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5245174305052387106444593 3933880728789290329833445)
                  ·
                    refine ⟨737602636647991936843771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3933880728789290329833445 737602636647991936843771)
                    ·
                      rfl

theorem cell22_2154714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_2154714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2154714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2154714 prefixEnd_2154714 := by exact prefixLift 2154714
  have htrace : WordTrace (prefixWord ++ tailWord_2154714) baseStart_2154714 baseEnd_2154714 := by
    simpa [prefixWord, tailWord_2154714, baseEnd_2154714] using wordTrace_append hprefix tailTrace_2154714
  have hstable : (prefixWord ++ tailWord_2154714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154714).length < 2 ^ (prefixWord ++ tailWord_2154714).sum := by decide
  have hdescent : baseEnd_2154714 < baseStart_2154714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154733 : List Nat := [1, 5, 1, 2, 3, 2, 1, 1, 1, 5]
def baseStart_2154733 : Nat := 118140960795 + 2154733 * 2 ^ 59
def prefixEnd_2154733 : Nat := 4983230072969 + 3 ^ 40 * 2154733 * 2
def baseEnd_2154733 : Nat := 737609140736282220618713

theorem tailTrace_2154733 : CollatzResearch.WordTrace tailWord_2154733 prefixEnd_2154733 737609140736282220618713 := by
  unfold tailWord_2154733
  simp only [CollatzResearch.WordTrace]
  refine ⟨78589568902777814943604853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52393045935185209962403235 78589568902777814943604853)
  ·
    refine ⟨7367772084635420150962955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78589568902777814943604853 7367772084635420150962955)
    ·
      refine ⟨11051658126953130226444433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7367772084635420150962955 11051658126953130226444433)
      ·
        refine ⟨8288743595214847669833325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11051658126953130226444433 8288743595214847669833325)
        ·
          refine ⟨3108278848205567876187497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8288743595214847669833325 3108278848205567876187497)
          ·
            refine ⟨2331209136154175907140623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3108278848205567876187497 2331209136154175907140623)
            ·
              refine ⟨3496813704231263860710935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2331209136154175907140623 3496813704231263860710935)
              ·
                refine ⟨5245220556346895791066403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3496813704231263860710935 5245220556346895791066403)
                ·
                  refine ⟨7867830834520343686599605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5245220556346895791066403 7867830834520343686599605)
                  ·
                    refine ⟨737609140736282220618713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7867830834520343686599605 737609140736282220618713)
                    ·
                      rfl

theorem cell22_2154733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_2154733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2154733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2154733 prefixEnd_2154733 := by exact prefixLift 2154733
  have htrace : WordTrace (prefixWord ++ tailWord_2154733) baseStart_2154733 baseEnd_2154733 := by
    simpa [prefixWord, tailWord_2154733, baseEnd_2154733] using wordTrace_append hprefix tailTrace_2154733
  have hstable : (prefixWord ++ tailWord_2154733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154733).length < 2 ^ (prefixWord ++ tailWord_2154733).sum := by decide
  have hdescent : baseEnd_2154733 < baseStart_2154733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154746 : List Nat := [3, 1, 1, 1, 1, 7, 2, 6]
def baseStart_2154746 : Nat := 118140960795 + 2154746 * 2 ^ 59
def prefixEnd_2154746 : Nat := 4983230072969 + 3 ^ 40 * 2154746 * 2
def baseEnd_2154746 : Nat := 81957065655772724449297

theorem tailTrace_2154746 : CollatzResearch.WordTrace tailWord_2154746 prefixEnd_2154746 81957065655772724449297 := by
  unfold tailWord_2154746
  simp only [CollatzResearch.WordTrace]
  refine ⟨19647510762932679540957023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52393362034487145442552061 19647510762932679540957023)
  ·
    refine ⟨29471266144399019311435535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19647510762932679540957023 29471266144399019311435535)
    ·
      refine ⟨44206899216598528967153303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29471266144399019311435535 44206899216598528967153303)
      ·
        refine ⟨66310348824897793450729955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44206899216598528967153303 66310348824897793450729955)
        ·
          refine ⟨99465523237346690176094933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66310348824897793450729955 99465523237346690176094933)
          ·
            refine ⟨2331223200875313051002225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 99465523237346690176094933 2331223200875313051002225)
            ·
              refine ⟨1748417400656484788251669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2331223200875313051002225 1748417400656484788251669)
              ·
                refine ⟨81957065655772724449297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1748417400656484788251669 81957065655772724449297)
                ·
                  rfl

theorem cell22_2154746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 6].length) (baseStart_2154746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2154746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2154746 prefixEnd_2154746 := by exact prefixLift 2154746
  have htrace : WordTrace (prefixWord ++ tailWord_2154746) baseStart_2154746 baseEnd_2154746 := by
    simpa [prefixWord, tailWord_2154746, baseEnd_2154746] using wordTrace_append hprefix tailTrace_2154746
  have hstable : (prefixWord ++ tailWord_2154746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154746).length < 2 ^ (prefixWord ++ tailWord_2154746).sum := by decide
  have hdescent : baseEnd_2154746 < baseStart_2154746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154851 : List Nat := [1, 1, 1, 5, 2, 1, 4, 1, 1, 5]
def baseStart_2154851 : Nat := 118140960795 + 2154851 * 2 ^ 59
def prefixEnd_2154851 : Nat := 4983230072969 + 3 ^ 40 * 2154851 * 2
def baseEnd_2154851 : Nat := 737649534547769246168351

theorem tailTrace_2154851 : CollatzResearch.WordTrace tailWord_2154851 prefixEnd_2154851 737649534547769246168351 := by
  unfold tailWord_2154851
  simp only [CollatzResearch.WordTrace]
  refine ⟨78593872716350321096400407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52395915144233547397600271 78593872716350321096400407)
  ·
    refine ⟨117890809074525481644600611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78593872716350321096400407 117890809074525481644600611)
    ·
      refine ⟨176836213611788222466900917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117890809074525481644600611 176836213611788222466900917)
      ·
        refine ⟨16578395026105145856271961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 176836213611788222466900917 16578395026105145856271961)
        ·
          refine ⟨12433796269578859392203971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16578395026105145856271961 12433796269578859392203971)
          ·
            refine ⟨18650694404368289088305957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12433796269578859392203971 18650694404368289088305957)
            ·
              refine ⟨3497005200819054204057367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18650694404368289088305957 3497005200819054204057367)
              ·
                refine ⟨5245507801228581306086051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3497005200819054204057367 5245507801228581306086051)
                ·
                  refine ⟨7868261701842871959129077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5245507801228581306086051 7868261701842871959129077)
                  ·
                    refine ⟨737649534547769246168351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7868261701842871959129077 737649534547769246168351)
                    ·
                      rfl

theorem cell22_2154851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 5].length) (baseStart_2154851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2154851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2154851 prefixEnd_2154851 := by exact prefixLift 2154851
  have htrace : WordTrace (prefixWord ++ tailWord_2154851) baseStart_2154851 baseEnd_2154851 := by
    simpa [prefixWord, tailWord_2154851, baseEnd_2154851] using wordTrace_append hprefix tailTrace_2154851
  have hstable : (prefixWord ++ tailWord_2154851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154851).length < 2 ^ (prefixWord ++ tailWord_2154851).sum := by decide
  have hdescent : baseEnd_2154851 < baseStart_2154851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154866 : List Nat := [3, 2, 1, 2, 1, 4, 1, 1, 1, 6]
def baseStart_2154866 : Nat := 118140960795 + 2154866 * 2 ^ 59
def prefixEnd_2154866 : Nat := 4983230072969 + 3 ^ 40 * 2154866 * 2
def baseEnd_2154866 : Nat := 737654669354314207043305

theorem tailTrace_2154866 : CollatzResearch.WordTrace tailWord_2154866 prefixEnd_2154866 737654669354314207043305 := by
  unfold tailWord_2154866
  simp only [CollatzResearch.WordTrace]
  refine ⟨19648604952823994664549113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52396279874197319105464301 19648604952823994664549113)
  ·
    refine ⟨14736453714617995998411835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19648604952823994664549113 14736453714617995998411835)
    ·
      refine ⟨22104680571926993997617753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14736453714617995998411835 22104680571926993997617753)
      ·
        refine ⟨16578510428945245498213315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22104680571926993997617753 16578510428945245498213315)
        ·
          refine ⟨24867765643417868247319973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16578510428945245498213315 24867765643417868247319973)
          ·
            refine ⟨4662706058140850296372495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24867765643417868247319973 4662706058140850296372495)
            ·
              refine ⟨6994059087211275444558743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4662706058140850296372495 6994059087211275444558743)
              ·
                refine ⟨10491088630816913166838115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6994059087211275444558743 10491088630816913166838115)
                ·
                  refine ⟨15736632946225369750257173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10491088630816913166838115 15736632946225369750257173)
                  ·
                    refine ⟨737654669354314207043305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15736632946225369750257173 737654669354314207043305)
                    ·
                      rfl

theorem cell22_2154866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_2154866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2154866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2154866 prefixEnd_2154866 := by exact prefixLift 2154866
  have htrace : WordTrace (prefixWord ++ tailWord_2154866) baseStart_2154866 baseEnd_2154866 := by
    simpa [prefixWord, tailWord_2154866, baseEnd_2154866] using wordTrace_append hprefix tailTrace_2154866
  have hstable : (prefixWord ++ tailWord_2154866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154866).length < 2 ^ (prefixWord ++ tailWord_2154866).sum := by decide
  have hdescent : baseEnd_2154866 < baseStart_2154866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154881 : List Nat := [1, 2, 4, 3, 1, 2, 9]
def baseStart_2154881 : Nat := 118140960795 + 2154881 * 2 ^ 59
def prefixEnd_2154881 : Nat := 4983230072969 + 3 ^ 40 * 2154881 * 2
def baseEnd_2154881 : Nat := 27320733487439228441417

theorem tailTrace_2154881 : CollatzResearch.WordTrace tailWord_2154881 prefixEnd_2154881 27320733487439228441417 := by
  unfold tailWord_2154881
  simp only [CollatzResearch.WordTrace]
  refine ⟨78594966906241636219992497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52396644604161090813328331 78594966906241636219992497)
  ·
    refine ⟨58946225179681227164994373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78594966906241636219992497 58946225179681227164994373)
    ·
      refine ⟨11052417221190230093436445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58946225179681227164994373 11052417221190230093436445)
      ·
        refine ⟨4144656457946336285038667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11052417221190230093436445 4144656457946336285038667)
        ·
          refine ⟨6216984686919504427558001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4144656457946336285038667 6216984686919504427558001)
          ·
            refine ⟨4662738515189628320668501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6216984686919504427558001 4662738515189628320668501)
            ·
              refine ⟨27320733487439228441417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4662738515189628320668501 27320733487439228441417)
              ·
                rfl

theorem cell22_2154881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 9].length) (baseStart_2154881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2154881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2154881 prefixEnd_2154881 := by exact prefixLift 2154881
  have htrace : WordTrace (prefixWord ++ tailWord_2154881) baseStart_2154881 baseEnd_2154881 := by
    simpa [prefixWord, tailWord_2154881, baseEnd_2154881] using wordTrace_append hprefix tailTrace_2154881
  have hstable : (prefixWord ++ tailWord_2154881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154881).length < 2 ^ (prefixWord ++ tailWord_2154881).sum := by decide
  have hdescent : baseEnd_2154881 < baseStart_2154881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154932 : List Nat := [2, 5, 2, 2, 2, 1, 8]
def baseStart_2154932 : Nat := 118140960795 + 2154932 * 2 ^ 59
def prefixEnd_2154932 : Nat := 4983230072969 + 3 ^ 40 * 2154932 * 2
def baseEnd_2154932 : Nat := 27321380092707853144189

theorem tailTrace_2154932 : CollatzResearch.WordTrace tailWord_2154932 prefixEnd_2154932 27321380092707853144189 := by
  unfold tailWord_2154932
  simp only [CollatzResearch.WordTrace]
  refine ⟨39298413514528435965049525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52397884686037914620066033 39298413514528435965049525)
  ·
    refine ⟨3684226266987040871723393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39298413514528435965049525 3684226266987040871723393)
    ·
      refine ⟨2763169700240280653792545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3684226266987040871723393 2763169700240280653792545)
      ·
        refine ⟨2072377275180210490344409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2763169700240280653792545 2072377275180210490344409)
        ·
          refine ⟨1554282956385157867758307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2072377275180210490344409 1554282956385157867758307)
          ·
            refine ⟨2331424434577736801637461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1554282956385157867758307 2331424434577736801637461)
            ·
              refine ⟨27321380092707853144189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2331424434577736801637461 27321380092707853144189)
              ·
                rfl

theorem cell22_2154932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 8].length) (baseStart_2154932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2154932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2154932 prefixEnd_2154932 := by exact prefixLift 2154932
  have htrace : WordTrace (prefixWord ++ tailWord_2154932) baseStart_2154932 baseEnd_2154932 := by
    simpa [prefixWord, tailWord_2154932, baseEnd_2154932] using wordTrace_append hprefix tailTrace_2154932
  have hstable : (prefixWord ++ tailWord_2154932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154932).length < 2 ^ (prefixWord ++ tailWord_2154932).sum := by decide
  have hdescent : baseEnd_2154932 < baseStart_2154932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154973 : List Nat := [1, 4, 3, 1, 1, 1, 3, 1, 3, 4]
def baseStart_2154973 : Nat := 118140960795 + 2154973 * 2 ^ 59
def prefixEnd_2154973 : Nat := 4983230072969 + 3 ^ 40 * 2154973 * 2
def baseEnd_2154973 : Nat := 737691297641001594617977

theorem tailTrace_2154973 : CollatzResearch.WordTrace tailWord_2154973 prefixEnd_2154973 737691297641001594617977 := by
  unfold tailWord_2154973
  simp only [CollatzResearch.WordTrace]
  refine ⟨78598322421908335932341573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52398881614605557288227715 78598322421908335932341573)
  ·
    refine ⟨14737185454107812987314045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78598322421908335932341573 14737185454107812987314045)
    ·
      refine ⟨5526444545290429870242767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14737185454107812987314045 5526444545290429870242767)
      ·
        refine ⟨8289666817935644805364151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5526444545290429870242767 8289666817935644805364151)
        ·
          refine ⟨12434500226903467208046227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8289666817935644805364151 12434500226903467208046227)
          ·
            refine ⟨18651750340355200812069341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12434500226903467208046227 18651750340355200812069341)
            ·
              refine ⟨6994406377633200304526003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18651750340355200812069341 6994406377633200304526003)
              ·
                refine ⟨10491609566449800456789005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6994406377633200304526003 10491609566449800456789005)
                ·
                  refine ⟨3934353587418675171295877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10491609566449800456789005 3934353587418675171295877)
                  ·
                    refine ⟨737691297641001594617977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3934353587418675171295877 737691297641001594617977)
                    ·
                      rfl

theorem cell22_2154973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_2154973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2154973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2154973 prefixEnd_2154973 := by exact prefixLift 2154973
  have htrace : WordTrace (prefixWord ++ tailWord_2154973) baseStart_2154973 baseEnd_2154973 := by
    simpa [prefixWord, tailWord_2154973, baseEnd_2154973] using wordTrace_append hprefix tailTrace_2154973
  have hstable : (prefixWord ++ tailWord_2154973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154973).length < 2 ^ (prefixWord ++ tailWord_2154973).sum := by decide
  have hdescent : baseEnd_2154973 < baseStart_2154973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154988 : List Nat := [2, 2, 1, 1, 2, 1, 4, 5, 4]
def baseStart_2154988 : Nat := 118140960795 + 2154988 * 2 ^ 59
def prefixEnd_2154988 : Nat := 4983230072969 + 3 ^ 40 * 2154988 * 2
def baseEnd_2154988 : Nat := 245898810815848851830977

theorem tailTrace_2154988 : CollatzResearch.WordTrace tailWord_2154988 prefixEnd_2154988 245898810815848851830977 := by
  unfold tailWord_2154988
  simp only [CollatzResearch.WordTrace]
  refine ⟨39299434758426996747068809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52399246344569328996091745 39299434758426996747068809)
  ·
    refine ⟨29474576068820247560301607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39299434758426996747068809 29474576068820247560301607)
    ·
      refine ⟨44211864103230371340452411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29474576068820247560301607 44211864103230371340452411)
      ·
        refine ⟨66317796154845557010678617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44211864103230371340452411 66317796154845557010678617)
        ·
          refine ⟨49738347116134167758008963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66317796154845557010678617 49738347116134167758008963)
          ·
            refine ⟨74607520674201251637013445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49738347116134167758008963 74607520674201251637013445)
            ·
              refine ⟨13988910126412734681940021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74607520674201251637013445 13988910126412734681940021)
              ·
                refine ⟨1311460324351193876431877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13988910126412734681940021 1311460324351193876431877)
                ·
                  refine ⟨245898810815848851830977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1311460324351193876431877 245898810815848851830977)
                  ·
                    rfl

theorem cell22_2154988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 5, 4].length) (baseStart_2154988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2154988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2154988 prefixEnd_2154988 := by exact prefixLift 2154988
  have htrace : WordTrace (prefixWord ++ tailWord_2154988) baseStart_2154988 baseEnd_2154988 := by
    simpa [prefixWord, tailWord_2154988, baseEnd_2154988] using wordTrace_append hprefix tailTrace_2154988
  have hstable : (prefixWord ++ tailWord_2154988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154988).length < 2 ^ (prefixWord ++ tailWord_2154988).sum := by decide
  have hdescent : baseEnd_2154988 < baseStart_2154988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155020 : List Nat := [2, 2, 1, 2, 4, 1, 2, 3, 2, 3]
def baseStart_2155020 : Nat := 118140960795 + 2155020 * 2 ^ 59
def prefixEnd_2155020 : Nat := 4983230072969 + 3 ^ 40 * 2155020 * 2
def baseEnd_2155020 : Nat := 737707386701509138692833

theorem tailTrace_2155020 : CollatzResearch.WordTrace tailWord_2155020 prefixEnd_2155020 737707386701509138692833 := by
  unfold tailWord_2155020
  simp only [CollatzResearch.WordTrace]
  refine ⟨39300018326369031479651257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52400024435158708639535009 39300018326369031479651257)
  ·
    refine ⟨29475013744776773609738443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39300018326369031479651257 29475013744776773609738443)
    ·
      refine ⟨44212520617165160414607665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29475013744776773609738443 44212520617165160414607665)
      ·
        refine ⟨33159390462873870310955749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44212520617165160414607665 33159390462873870310955749)
        ·
          refine ⟨6217385711788850683304203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33159390462873870310955749 6217385711788850683304203)
          ·
            refine ⟨9326078567683276024956305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6217385711788850683304203 9326078567683276024956305)
            ·
              refine ⟨6994558925762457018717229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9326078567683276024956305 6994558925762457018717229)
              ·
                refine ⟨2622959597160921382018961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6994558925762457018717229 2622959597160921382018961)
                ·
                  refine ⟨1967219697870691036514221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2622959597160921382018961 1967219697870691036514221)
                  ·
                    refine ⟨737707386701509138692833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1967219697870691036514221 737707386701509138692833)
                    ·
                      rfl

theorem cell22_2155020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 2, 3].length) (baseStart_2155020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2155020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2155020 prefixEnd_2155020 := by exact prefixLift 2155020
  have htrace : WordTrace (prefixWord ++ tailWord_2155020) baseStart_2155020 baseEnd_2155020 := by
    simpa [prefixWord, tailWord_2155020, baseEnd_2155020] using wordTrace_append hprefix tailTrace_2155020
  have hstable : (prefixWord ++ tailWord_2155020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155020).length < 2 ^ (prefixWord ++ tailWord_2155020).sum := by decide
  have hdescent : baseEnd_2155020 < baseStart_2155020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155054 : List Nat := [4, 1, 3, 1, 3, 2, 1, 2, 2, 3]
def baseStart_2155054 : Nat := 118140960795 + 2155054 * 2 ^ 59
def prefixEnd_2155054 : Nat := 4983230072969 + 3 ^ 40 * 2155054 * 2
def baseEnd_2155054 : Nat := 737719025596344383342729

theorem tailTrace_2155054 : CollatzResearch.WordTrace tailWord_2155054 prefixEnd_2155054 737719025596344383342729 := by
  unfold tailWord_2155054
  simp only [CollatzResearch.WordTrace]
  refine ⟨9825159591826860845755027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52400851156409924510693477 9825159591826860845755027)
  ·
    refine ⟨14737739387740291268632541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9825159591826860845755027 14737739387740291268632541)
    ·
      refine ⟨5526652270402609225737203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14737739387740291268632541 5526652270402609225737203)
      ·
        refine ⟨8289978405603913838605805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5526652270402609225737203 8289978405603913838605805)
        ·
          refine ⟨3108741902101467689477177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8289978405603913838605805 3108741902101467689477177)
          ·
            refine ⟨2331556426576100767107883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3108741902101467689477177 2331556426576100767107883)
            ·
              refine ⟨3497334639864151150661825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2331556426576100767107883 3497334639864151150661825)
              ·
                refine ⟨2623000979898113362996369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3497334639864151150661825 2623000979898113362996369)
                ·
                  refine ⟨1967250734923585022247277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2623000979898113362996369 1967250734923585022247277)
                  ·
                    refine ⟨737719025596344383342729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1967250734923585022247277 737719025596344383342729)
                    ·
                      rfl

theorem cell22_2155054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_2155054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2155054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2155054 prefixEnd_2155054 := by exact prefixLift 2155054
  have htrace : WordTrace (prefixWord ++ tailWord_2155054) baseStart_2155054 baseEnd_2155054 := by
    simpa [prefixWord, tailWord_2155054, baseEnd_2155054] using wordTrace_append hprefix tailTrace_2155054
  have hstable : (prefixWord ++ tailWord_2155054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155054).length < 2 ^ (prefixWord ++ tailWord_2155054).sum := by decide
  have hdescent : baseEnd_2155054 < baseStart_2155054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155065 : List Nat := [1, 2, 1, 5, 1, 1, 4, 1, 3, 3]
def baseStart_2155065 : Nat := 118140960795 + 2155065 * 2 ^ 59
def prefixEnd_2155065 : Nat := 4983230072969 + 3 ^ 40 * 2155065 * 2
def baseEnd_2155065 : Nat := 737722791121144021317695

theorem tailTrace_2155065 : CollatzResearch.WordTrace tailWord_2155065 prefixEnd_2155065 737722791121144021317695 := by
  unfold tailWord_2155065
  simp only [CollatzResearch.WordTrace]
  refine ⟨78601677937575035644690649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52401118625050023763127099 78601677937575035644690649)
  ·
    refine ⟨58951258453181276733517987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78601677937575035644690649 58951258453181276733517987)
    ·
      refine ⟨88426887679771915100276981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58951258453181276733517987 88426887679771915100276981)
      ·
        refine ⟨8290020719978617040650967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88426887679771915100276981 8290020719978617040650967)
        ·
          refine ⟨12435031079967925560976451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8290020719978617040650967 12435031079967925560976451)
          ·
            refine ⟨18652546619951888341464677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12435031079967925560976451 18652546619951888341464677)
            ·
              refine ⟨3497352491240979064024627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18652546619951888341464677 3497352491240979064024627)
              ·
                refine ⟨5246028736861468596036941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3497352491240979064024627 5246028736861468596036941)
                ·
                  refine ⟨1967260776323050723513853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5246028736861468596036941 1967260776323050723513853)
                  ·
                    refine ⟨737722791121144021317695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1967260776323050723513853 737722791121144021317695)
                    ·
                      rfl

theorem cell22_2155065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 3, 3].length) (baseStart_2155065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2155065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2155065 prefixEnd_2155065 := by exact prefixLift 2155065
  have htrace : WordTrace (prefixWord ++ tailWord_2155065) baseStart_2155065 baseEnd_2155065 := by
    simpa [prefixWord, tailWord_2155065, baseEnd_2155065] using wordTrace_append hprefix tailTrace_2155065
  have hstable : (prefixWord ++ tailWord_2155065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155065).length < 2 ^ (prefixWord ++ tailWord_2155065).sum := by decide
  have hdescent : baseEnd_2155065 < baseStart_2155065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155168 : List Nat := [2, 1, 1, 4, 4, 10]
def baseStart_2155168 : Nat := 118140960795 + 2155168 * 2 ^ 59
def prefixEnd_2155168 : Nat := 4983230072969 + 3 ^ 40 * 2155168 * 2
def baseEnd_2155168 : Nat := 9108124075630692419659

theorem tailTrace_2155168 : CollatzResearch.WordTrace tailWord_2155168 prefixEnd_2155168 9108124075630692419659 := by
  unfold tailWord_2155168
  simp only [CollatzResearch.WordTrace]
  refine ⟨39302717328100942117845079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52403623104134589490460105 39302717328100942117845079)
  ·
    refine ⟨58954075992151413176767619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39302717328100942117845079 58954075992151413176767619)
    ·
      refine ⟨88431113988227119765151429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58954075992151413176767619 88431113988227119765151429)
      ·
        refine ⟨16580833872792584955965893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88431113988227119765151429 16580833872792584955965893)
        ·
          refine ⟨3108906351148609679243605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16580833872792584955965893 3108906351148609679243605)
          ·
            refine ⟨9108124075630692419659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3108906351148609679243605 9108124075630692419659)
            ·
              rfl

theorem cell22_2155168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 10].length) (baseStart_2155168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2155168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2155168 prefixEnd_2155168 := by exact prefixLift 2155168
  have htrace : WordTrace (prefixWord ++ tailWord_2155168) baseStart_2155168 baseEnd_2155168 := by
    simpa [prefixWord, tailWord_2155168, baseEnd_2155168] using wordTrace_append hprefix tailTrace_2155168
  have hstable : (prefixWord ++ tailWord_2155168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155168).length < 2 ^ (prefixWord ++ tailWord_2155168).sum := by decide
  have hdescent : baseEnd_2155168 < baseStart_2155168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155172 : List Nat := [2, 3, 1, 2, 2, 1, 4, 2, 2, 3]
def baseStart_2155172 : Nat := 118140960795 + 2155172 * 2 ^ 59
def prefixEnd_2155172 : Nat := 4983230072969 + 3 ^ 40 * 2155172 * 2
def baseEnd_2155172 : Nat := 737759419407831408892367

theorem tailTrace_2155172 : CollatzResearch.WordTrace tailWord_2155172 prefixEnd_2155172 737759419407831408892367 := by
  unfold tailWord_2155172
  simp only [CollatzResearch.WordTrace]
  refine ⟨39302790274093696459417885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52403720365458261945890513 39302790274093696459417885)
  ·
    refine ⟨14738546352785136172281707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39302790274093696459417885 14738546352785136172281707)
    ·
      refine ⟨22107819529177704258422561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14738546352785136172281707 22107819529177704258422561)
      ·
        refine ⟨16580864646883278193816921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22107819529177704258422561 16580864646883278193816921)
        ·
          refine ⟨12435648485162458645362691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16580864646883278193816921 12435648485162458645362691)
          ·
            refine ⟨18653472727743687968044037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12435648485162458645362691 18653472727743687968044037)
            ·
              refine ⟨3497526136451941494008257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18653472727743687968044037 3497526136451941494008257)
              ·
                refine ⟨2623144602338956120506193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3497526136451941494008257 2623144602338956120506193)
                ·
                  refine ⟨1967358451754217090379645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2623144602338956120506193 1967358451754217090379645)
                  ·
                    refine ⟨737759419407831408892367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1967358451754217090379645 737759419407831408892367)
                    ·
                      rfl

theorem cell22_2155172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_2155172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2155172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2155172 prefixEnd_2155172 := by exact prefixLift 2155172
  have htrace : WordTrace (prefixWord ++ tailWord_2155172) baseStart_2155172 baseEnd_2155172 := by
    simpa [prefixWord, tailWord_2155172, baseEnd_2155172] using wordTrace_append hprefix tailTrace_2155172
  have hstable : (prefixWord ++ tailWord_2155172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155172).length < 2 ^ (prefixWord ++ tailWord_2155172).sum := by decide
  have hdescent : baseEnd_2155172 < baseStart_2155172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155200 : List Nat := [2, 1, 1, 2, 4, 2, 1, 1, 5, 3]
def baseStart_2155200 : Nat := 118140960795 + 2155200 * 2 ^ 59
def prefixEnd_2155200 : Nat := 4983230072969 + 3 ^ 40 * 2155200 * 2
def baseEnd_2155200 : Nat := 737769004380048669192281

theorem tailTrace_2155200 : CollatzResearch.WordTrace tailWord_2155200 prefixEnd_2155200 737769004380048669192281 := by
  unfold tailWord_2155200
  simp only [CollatzResearch.WordTrace]
  refine ⟨39303300896042976850427527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52404401194723969133903369 39303300896042976850427527)
  ·
    refine ⟨58954951344064465275641291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39303300896042976850427527 58954951344064465275641291)
    ·
      refine ⟨88432427016096697913461937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58954951344064465275641291 88432427016096697913461937)
      ·
        refine ⟨66324320262072523435096453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88432427016096697913461937 66324320262072523435096453)
        ·
          refine ⟨12435810049138598144080585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66324320262072523435096453 12435810049138598144080585)
          ·
            refine ⟨9326857536853948608060439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12435810049138598144080585 9326857536853948608060439)
            ·
              refine ⟨13990286305280922912090659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9326857536853948608060439 13990286305280922912090659)
              ·
                refine ⟨20985429457921384368135989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13990286305280922912090659 20985429457921384368135989)
                ·
                  refine ⟨1967384011680129784512749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20985429457921384368135989 1967384011680129784512749)
                  ·
                    refine ⟨737769004380048669192281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1967384011680129784512749 737769004380048669192281)
                    ·
                      rfl

theorem cell22_2155200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 5, 3].length) (baseStart_2155200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2155200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2155200 prefixEnd_2155200 := by exact prefixLift 2155200
  have htrace : WordTrace (prefixWord ++ tailWord_2155200) baseStart_2155200 baseEnd_2155200 := by
    simpa [prefixWord, tailWord_2155200, baseEnd_2155200] using wordTrace_append hprefix tailTrace_2155200
  have hstable : (prefixWord ++ tailWord_2155200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155200).length < 2 ^ (prefixWord ++ tailWord_2155200).sum := by decide
  have hdescent : baseEnd_2155200 < baseStart_2155200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155245 : List Nat := [1, 5, 1, 2, 1, 1, 1, 3, 2, 5]
def baseStart_2155245 : Nat := 118140960795 + 2155245 * 2 ^ 59
def prefixEnd_2155245 : Nat := 4983230072969 + 3 ^ 40 * 2155245 * 2
def baseEnd_2155245 : Nat := 737784408799683551817143

theorem tailTrace_2155245 : CollatzResearch.WordTrace tailWord_2155245 prefixEnd_2155245 737784408799683551817143 := by
  unfold tailWord_2155245
  simp only [CollatzResearch.WordTrace]
  refine ⟨78608243076922926386243189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52405495384615284257495459 78608243076922926386243189)
  ·
    refine ⟨7369522788461524348710299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78608243076922926386243189 7369522788461524348710299)
    ·
      refine ⟨11054284182692286523065449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7369522788461524348710299 11054284182692286523065449)
      ·
        refine ⟨8290713137019214892299087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11054284182692286523065449 8290713137019214892299087)
        ·
          refine ⟨12436069705528822338448631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8290713137019214892299087 12436069705528822338448631)
          ·
            refine ⟨18654104558293233507672947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12436069705528822338448631 18654104558293233507672947)
            ·
              refine ⟨27981156837439850261509421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18654104558293233507672947 27981156837439850261509421)
              ·
                refine ⟨10492933814039943848066033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27981156837439850261509421 10492933814039943848066033)
                ·
                  refine ⟨7869700360529957886049525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10492933814039943848066033 7869700360529957886049525)
                  ·
                    refine ⟨737784408799683551817143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7869700360529957886049525 737784408799683551817143)
                    ·
                      rfl

theorem cell22_2155245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_2155245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2155245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2155245 prefixEnd_2155245 := by exact prefixLift 2155245
  have htrace : WordTrace (prefixWord ++ tailWord_2155245) baseStart_2155245 baseEnd_2155245 := by
    simpa [prefixWord, tailWord_2155245, baseEnd_2155245] using wordTrace_append hprefix tailTrace_2155245
  have hstable : (prefixWord ++ tailWord_2155245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155245).length < 2 ^ (prefixWord ++ tailWord_2155245).sum := by decide
  have hdescent : baseEnd_2155245 < baseStart_2155245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155247 : List Nat := [1, 1, 2, 1, 5, 3, 3, 1, 5]
def baseStart_2155247 : Nat := 118140960795 + 2155247 * 2 ^ 59
def prefixEnd_2155247 : Nat := 4983230072969 + 3 ^ 40 * 2155247 * 2
def baseEnd_2155247 : Nat := 245928364480185404422379

theorem tailTrace_2155247 : CollatzResearch.WordTrace tailWord_2155247 prefixEnd_2155247 245928364480185404422379 := by
  unfold tailWord_2155247
  simp only [CollatzResearch.WordTrace]
  refine ⟨78608316022915680727815995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52405544015277120485210663 78608316022915680727815995)
  ·
    refine ⟨117912474034373521091723993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78608316022915680727815995 117912474034373521091723993)
    ·
      refine ⟨88434355525780140818792995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117912474034373521091723993 88434355525780140818792995)
      ·
        refine ⟨132651533288670211228189493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88434355525780140818792995 132651533288670211228189493)
        ·
          refine ⟨12436081245812832302642765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 132651533288670211228189493 12436081245812832302642765)
          ·
            refine ⟨4663530467179812113491037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12436081245812832302642765 4663530467179812113491037)
            ·
              refine ⟨1748823925192429542559139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4663530467179812113491037 1748823925192429542559139)
              ·
                refine ⟨2623235887788644313838709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1748823925192429542559139 2623235887788644313838709)
                ·
                  refine ⟨245928364480185404422379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2623235887788644313838709 245928364480185404422379)
                  ·
                    rfl

theorem cell22_2155247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 5].length) (baseStart_2155247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2155247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2155247 prefixEnd_2155247 := by exact prefixLift 2155247
  have htrace : WordTrace (prefixWord ++ tailWord_2155247) baseStart_2155247 baseEnd_2155247 := by
    simpa [prefixWord, tailWord_2155247, baseEnd_2155247] using wordTrace_append hprefix tailTrace_2155247
  have hstable : (prefixWord ++ tailWord_2155247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155247).length < 2 ^ (prefixWord ++ tailWord_2155247).sum := by decide
  have hdescent : baseEnd_2155247 < baseStart_2155247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155253 : List Nat := [1, 3, 6, 1, 2, 1, 2, 6]
def baseStart_2155253 : Nat := 118140960795 + 2155253 * 2 ^ 59
def prefixEnd_2155253 : Nat := 4983230072969 + 3 ^ 40 * 2155253 * 2
def baseEnd_2155253 : Nat := 81976349707019355290791

theorem tailTrace_2155253 : CollatzResearch.WordTrace tailWord_2155253 prefixEnd_2155253 81976349707019355290791 := by
  unfold tailWord_2155253
  simp only [CollatzResearch.WordTrace]
  refine ⟨78608534860893943752534413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52405689907262629168356275 78608534860893943752534413)
  ·
    refine ⟨29478200572835228907200405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78608534860893943752534413 29478200572835228907200405)
    ·
      refine ⟨1381790651851651355025019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 29478200572835228907200405 1381790651851651355025019)
      ·
        refine ⟨2072685977777477032537529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1381790651851651355025019 2072685977777477032537529)
        ·
          refine ⟨1554514483333107774403147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2072685977777477032537529 1554514483333107774403147)
          ·
            refine ⟨2331771724999661661604721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1554514483333107774403147 2331771724999661661604721)
            ·
              refine ⟨1748828793749746246203541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2331771724999661661604721 1748828793749746246203541)
              ·
                refine ⟨81976349707019355290791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1748828793749746246203541 81976349707019355290791)
                ·
                  rfl

theorem cell22_2155253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 6].length) (baseStart_2155253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2155253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2155253 prefixEnd_2155253 := by exact prefixLift 2155253
  have htrace : WordTrace (prefixWord ++ tailWord_2155253) baseStart_2155253 baseEnd_2155253 := by
    simpa [prefixWord, tailWord_2155253, baseEnd_2155253] using wordTrace_append hprefix tailTrace_2155253
  have hstable : (prefixWord ++ tailWord_2155253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155253).length < 2 ^ (prefixWord ++ tailWord_2155253).sum := by decide
  have hdescent : baseEnd_2155253 < baseStart_2155253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155292 : List Nat := [2, 2, 3, 1, 1, 5, 1, 1, 6]
def baseStart_2155292 : Nat := 118140960795 + 2155292 * 2 ^ 59
def prefixEnd_2155292 : Nat := 4983230072969 + 3 ^ 40 * 2155292 * 2
def baseEnd_2155292 : Nat := 245933499286730365297333

theorem tailTrace_2155292 : CollatzResearch.WordTrace tailWord_2155292 prefixEnd_2155292 245933499286730365297333 := by
  unfold tailWord_2155292
  simp only [CollatzResearch.WordTrace]
  refine ⟨39304978653876326706602065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52406638205168435608802753 39304978653876326706602065)
  ·
    refine ⟨29478733990407245029951549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39304978653876326706602065 29478733990407245029951549)
    ·
      refine ⟨11054525246402716886231831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29478733990407245029951549 11054525246402716886231831)
      ·
        refine ⟨16581787869604075329347747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11054525246402716886231831 16581787869604075329347747)
        ·
          refine ⟨24872681804406112994021621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16581787869604075329347747 24872681804406112994021621)
          ·
            refine ⟨2331813919163073093189527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24872681804406112994021621 2331813919163073093189527)
            ·
              refine ⟨3497720878744609639784291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2331813919163073093189527 3497720878744609639784291)
              ·
                refine ⟨5246581318116914459676437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3497720878744609639784291 5246581318116914459676437)
                ·
                  refine ⟨245933499286730365297333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5246581318116914459676437 245933499286730365297333)
                  ·
                    rfl

theorem cell22_2155292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 6].length) (baseStart_2155292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2155292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2155292 prefixEnd_2155292 := by exact prefixLift 2155292
  have htrace : WordTrace (prefixWord ++ tailWord_2155292) baseStart_2155292 baseEnd_2155292 := by
    simpa [prefixWord, tailWord_2155292, baseEnd_2155292] using wordTrace_append hprefix tailTrace_2155292
  have hstable : (prefixWord ++ tailWord_2155292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155292).length < 2 ^ (prefixWord ++ tailWord_2155292).sum := by decide
  have hdescent : baseEnd_2155292 < baseStart_2155292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155399 : List Nat := [1, 1, 4, 2, 3, 3, 1, 2, 5]
def baseStart_2155399 : Nat := 118140960795 + 2155399 * 2 ^ 59
def prefixEnd_2155399 : Nat := 4983230072969 + 3 ^ 40 * 2155399 * 2
def baseEnd_2155399 : Nat := 245945708715626161155557

theorem tailTrace_2155399 : CollatzResearch.WordTrace tailWord_2155399 prefixEnd_2155399 245945708715626161155557 := by
  unfold tailWord_2155399
  simp only [CollatzResearch.WordTrace]
  refine ⟨78613859918365010687349251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52409239945576673791566167 78613859918365010687349251)
  ·
    refine ⟨117920789877547516031023877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78613859918365010687349251 117920789877547516031023877)
    ·
      refine ⟨22110148102040159255816977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117920789877547516031023877 22110148102040159255816977)
      ·
        refine ⟨16582611076530119441862733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22110148102040159255816977 16582611076530119441862733)
        ·
          refine ⟨6218479153698794790698525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16582611076530119441862733 6218479153698794790698525)
          ·
            refine ⟨2331929682637048046511947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6218479153698794790698525 2331929682637048046511947)
            ·
              refine ⟨3497894523955572069767921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2331929682637048046511947 3497894523955572069767921)
              ·
                refine ⟨2623420892966679052325941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3497894523955572069767921 2623420892966679052325941)
                ·
                  refine ⟨245945708715626161155557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2623420892966679052325941 245945708715626161155557)
                  ·
                    rfl

theorem cell22_2155399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 5].length) (baseStart_2155399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2155399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2155399 prefixEnd_2155399 := by exact prefixLift 2155399
  have htrace : WordTrace (prefixWord ++ tailWord_2155399) baseStart_2155399 baseEnd_2155399 := by
    simpa [prefixWord, tailWord_2155399, baseEnd_2155399] using wordTrace_append hprefix tailTrace_2155399
  have hstable : (prefixWord ++ tailWord_2155399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155399).length < 2 ^ (prefixWord ++ tailWord_2155399).sum := by decide
  have hdescent : baseEnd_2155399 < baseStart_2155399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155437 : List Nat := [1, 5, 2, 3, 2, 1, 1, 3, 1, 3]
def baseStart_2155437 : Nat := 118140960795 + 2155437 * 2 ^ 59
def prefixEnd_2155437 : Nat := 4983230072969 + 3 ^ 40 * 2155437 * 2
def baseEnd_2155437 : Nat := 737850134323459051016555

theorem tailTrace_2155437 : CollatzResearch.WordTrace tailWord_2155437 prefixEnd_2155437 737850134323459051016555 := by
  unfold tailWord_2155437
  simp only [CollatzResearch.WordTrace]
  refine ⟨78615245892227343177232565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52410163928151562118155043 78615245892227343177232565)
  ·
    refine ⟨7370179302396313422865553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78615245892227343177232565 7370179302396313422865553)
    ·
      refine ⟨5527634476797235067149165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7370179302396313422865553 5527634476797235067149165)
      ·
        refine ⟨2072862928798963150180937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5527634476797235067149165 2072862928798963150180937)
        ·
          refine ⟨1554647196599222362635703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2072862928798963150180937 1554647196599222362635703)
          ·
            refine ⟨2331970794898833543953555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1554647196599222362635703 2331970794898833543953555)
            ·
              refine ⟨3497956192348250315930333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2331970794898833543953555 3497956192348250315930333)
              ·
                refine ⟨1311733572130593868473875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3497956192348250315930333 1311733572130593868473875)
                ·
                  refine ⟨1967600358195890802710813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1311733572130593868473875 1967600358195890802710813)
                  ·
                    refine ⟨737850134323459051016555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1967600358195890802710813 737850134323459051016555)
                    ·
                      rfl

theorem cell22_2155437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_2155437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2155437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2155437 prefixEnd_2155437 := by exact prefixLift 2155437
  have htrace : WordTrace (prefixWord ++ tailWord_2155437) baseStart_2155437 baseEnd_2155437 := by
    simpa [prefixWord, tailWord_2155437, baseEnd_2155437] using wordTrace_append hprefix tailTrace_2155437
  have hstable : (prefixWord ++ tailWord_2155437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155437).length < 2 ^ (prefixWord ++ tailWord_2155437).sum := by decide
  have hdescent : baseEnd_2155437 < baseStart_2155437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155476 : List Nat := [2, 4, 1, 2, 1, 3, 1, 3, 2, 3]
def baseStart_2155476 : Nat := 118140960795 + 2155476 * 2 ^ 59
def prefixEnd_2155476 : Nat := 4983230072969 + 3 ^ 40 * 2155476 * 2
def baseEnd_2155476 : Nat := 737863484820475949291435

theorem tailTrace_2155476 : CollatzResearch.WordTrace tailWord_2155476 prefixEnd_2155476 737863484820475949291435 := by
  unfold tailWord_2155476
  simp only [CollatzResearch.WordTrace]
  refine ⟨39308334169543026418951141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52411112226057368558601521 39308334169543026418951141)
  ·
    refine ⟨7370312656789317453553339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39308334169543026418951141 7370312656789317453553339)
    ·
      refine ⟨11055468985183976180330009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7370312656789317453553339 11055468985183976180330009)
      ·
        refine ⟨8291601738887982135247507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11055468985183976180330009 8291601738887982135247507)
        ·
          refine ⟨12437402608331973202871261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8291601738887982135247507 12437402608331973202871261)
          ·
            refine ⟨4664025978124489951076723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12437402608331973202871261 4664025978124489951076723)
            ·
              refine ⟨6996038967186734926615085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4664025978124489951076723 6996038967186734926615085)
              ·
                refine ⟨2623514612695025597480657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6996038967186734926615085 2623514612695025597480657)
                ·
                  refine ⟨1967635959521269198110493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2623514612695025597480657 1967635959521269198110493)
                  ·
                    refine ⟨737863484820475949291435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1967635959521269198110493 737863484820475949291435)
                    ·
                      rfl

theorem cell22_2155476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_2155476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2155476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2155476 prefixEnd_2155476 := by exact prefixLift 2155476
  have htrace : WordTrace (prefixWord ++ tailWord_2155476) baseStart_2155476 baseEnd_2155476 := by
    simpa [prefixWord, tailWord_2155476, baseEnd_2155476] using wordTrace_append hprefix tailTrace_2155476
  have hstable : (prefixWord ++ tailWord_2155476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155476).length < 2 ^ (prefixWord ++ tailWord_2155476).sum := by decide
  have hdescent : baseEnd_2155476 < baseStart_2155476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155532 : List Nat := [2, 2, 1, 2, 3, 2, 1, 1, 1, 7]
def baseStart_2155532 : Nat := 118140960795 + 2155532 * 2 ^ 59
def prefixEnd_2155532 : Nat := 4983230072969 + 3 ^ 40 * 2155532 * 2
def baseEnd_2155532 : Nat := 737882654764910469891263

theorem tailTrace_2155532 : CollatzResearch.WordTrace tailWord_2155532 prefixEnd_2155532 737882654764910469891263 := by
  unfold tailWord_2155532
  simp only [CollatzResearch.WordTrace]
  refine ⟨39309355413441587200970425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52412473884588782934627233 39309355413441587200970425)
  ·
    refine ⟨29482016560081190400727819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39309355413441587200970425 29482016560081190400727819)
    ·
      refine ⟨44223024840121785601091729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29482016560081190400727819 44223024840121785601091729)
      ·
        refine ⟨33167268630091339200818797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44223024840121785601091729 33167268630091339200818797)
        ·
          refine ⟨12437725736284252200307049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33167268630091339200818797 12437725736284252200307049)
          ·
            refine ⟨9328294302213189150230287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12437725736284252200307049 9328294302213189150230287)
            ·
              refine ⟨13992441453319783725345431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9328294302213189150230287 13992441453319783725345431)
              ·
                refine ⟨20988662179979675588018147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13992441453319783725345431 20988662179979675588018147)
                ·
                  refine ⟨31482993269969513382027221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20988662179979675588018147 31482993269969513382027221)
                  ·
                    refine ⟨737882654764910469891263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31482993269969513382027221 737882654764910469891263)
                    ·
                      rfl

theorem cell22_2155532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_2155532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2155532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2155532 prefixEnd_2155532 := by exact prefixLift 2155532
  have htrace : WordTrace (prefixWord ++ tailWord_2155532) baseStart_2155532 baseEnd_2155532 := by
    simpa [prefixWord, tailWord_2155532, baseEnd_2155532] using wordTrace_append hprefix tailTrace_2155532
  have hstable : (prefixWord ++ tailWord_2155532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155532).length < 2 ^ (prefixWord ++ tailWord_2155532).sum := by decide
  have hdescent : baseEnd_2155532 < baseStart_2155532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155534 : List Nat := [4, 1, 1, 2, 2, 2, 2, 3, 5]
def baseStart_2155534 : Nat := 118140960795 + 2155534 * 2 ^ 59
def prefixEnd_2155534 : Nat := 4983230072969 + 3 ^ 40 * 2155534 * 2
def baseEnd_2155534 : Nat := 245961113135261043780419

theorem tailTrace_2155534 : CollatzResearch.WordTrace tailWord_2155534 prefixEnd_2155534 245961113135261043780419 := by
  unfold tailWord_2155534
  simp only [CollatzResearch.WordTrace]
  refine ⟨9827347971609491092939207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52412522515250619162342437 9827347971609491092939207)
  ·
    refine ⟨14741021957414236639408811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9827347971609491092939207 14741021957414236639408811)
    ·
      refine ⟨22111532936121354959113217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14741021957414236639408811 22111532936121354959113217)
      ·
        refine ⟨16583649702091016219334913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22111532936121354959113217 16583649702091016219334913)
        ·
          refine ⟨12437737276568262164501185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16583649702091016219334913 12437737276568262164501185)
          ·
            refine ⟨9328302957426196623375889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12437737276568262164501185 9328302957426196623375889)
            ·
              refine ⟨6996227218069647467531917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9328302957426196623375889 6996227218069647467531917)
              ·
                refine ⟨2623585206776117800324469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6996227218069647467531917 2623585206776117800324469)
                ·
                  refine ⟨245961113135261043780419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2623585206776117800324469 245961113135261043780419)
                  ·
                    rfl

theorem cell22_2155534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_2155534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2155534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2155534 prefixEnd_2155534 := by exact prefixLift 2155534
  have htrace : WordTrace (prefixWord ++ tailWord_2155534) baseStart_2155534 baseEnd_2155534 := by
    simpa [prefixWord, tailWord_2155534, baseEnd_2155534] using wordTrace_append hprefix tailTrace_2155534
  have hstable : (prefixWord ++ tailWord_2155534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155534).length < 2 ^ (prefixWord ++ tailWord_2155534).sum := by decide
  have hdescent : baseEnd_2155534 < baseStart_2155534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155564 : List Nat := [2, 2, 1, 1, 1, 2, 5, 3, 1, 4]
def baseStart_2155564 : Nat := 118140960795 + 2155564 * 2 ^ 59
def prefixEnd_2155564 : Nat := 4983230072969 + 3 ^ 40 * 2155564 * 2
def baseEnd_2155564 : Nat := 737893609018873053091165

theorem tailTrace_2155564 : CollatzResearch.WordTrace tailWord_2155564 prefixEnd_2155564 737893609018873053091165 := by
  unfold tailWord_2155564
  simp only [CollatzResearch.WordTrace]
  refine ⟨39309938981383621933552873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52413251975178162578070497 39309938981383621933552873)
  ·
    refine ⟨29482454236037716450164655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39309938981383621933552873 29482454236037716450164655)
    ·
      refine ⟨44223681354056574675246983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29482454236037716450164655 44223681354056574675246983)
      ·
        refine ⟨66335522031084862012870475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44223681354056574675246983 66335522031084862012870475)
        ·
          refine ⟨99503283046627293019305713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66335522031084862012870475 99503283046627293019305713)
          ·
            refine ⟨74627462284970469764479285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99503283046627293019305713 74627462284970469764479285)
            ·
              refine ⟨6996324589215981540419933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74627462284970469764479285 6996324589215981540419933)
              ·
                refine ⟨2623621720955993077657475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6996324589215981540419933 2623621720955993077657475)
                ·
                  refine ⟨3935432581433989616486213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2623621720955993077657475 3935432581433989616486213)
                  ·
                    refine ⟨737893609018873053091165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3935432581433989616486213 737893609018873053091165)
                    ·
                      rfl

theorem cell22_2155564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 4].length) (baseStart_2155564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2155564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2155564 prefixEnd_2155564 := by exact prefixLift 2155564
  have htrace : WordTrace (prefixWord ++ tailWord_2155564) baseStart_2155564 baseEnd_2155564 := by
    simpa [prefixWord, tailWord_2155564, baseEnd_2155564] using wordTrace_append hprefix tailTrace_2155564
  have hstable : (prefixWord ++ tailWord_2155564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155564).length < 2 ^ (prefixWord ++ tailWord_2155564).sum := by decide
  have hdescent : baseEnd_2155564 < baseStart_2155564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155592 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 3, 6]
def baseStart_2155592 : Nat := 118140960795 + 2155592 * 2 ^ 59
def prefixEnd_2155592 : Nat := 4983230072969 + 3 ^ 40 * 2155592 * 2
def baseEnd_2155592 : Nat := 737903193991090313391079

theorem tailTrace_2155592 : CollatzResearch.WordTrace tailWord_2155592 prefixEnd_2155592 737903193991090313391079 := by
  unfold tailWord_2155592
  simp only [CollatzResearch.WordTrace]
  refine ⟨39310449603332902324562515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52413932804443869766083353 39310449603332902324562515)
  ·
    refine ⟨58965674404999353486843773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39310449603332902324562515 58965674404999353486843773)
    ·
      refine ⟨22112127901874757557566415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58965674404999353486843773 22112127901874757557566415)
      ·
        refine ⟨33168191852812136336349623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22112127901874757557566415 33168191852812136336349623)
        ·
          refine ⟨49752287779218204504524435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33168191852812136336349623 49752287779218204504524435)
          ·
            refine ⟨74628431668827306756786653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49752287779218204504524435 74628431668827306756786653)
            ·
              refine ⟨27985661875810240033794995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74628431668827306756786653 27985661875810240033794995)
              ·
                refine ⟨41978492813715360050692493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27985661875810240033794995 41978492813715360050692493)
                ·
                  refine ⟨15741934805143260019009685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41978492813715360050692493 15741934805143260019009685)
                  ·
                    refine ⟨737903193991090313391079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15741934805143260019009685 737903193991090313391079)
                    ·
                      rfl

theorem cell22_2155592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_2155592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2155592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2155592 prefixEnd_2155592 := by exact prefixLift 2155592
  have htrace : WordTrace (prefixWord ++ tailWord_2155592) baseStart_2155592 baseEnd_2155592 := by
    simpa [prefixWord, tailWord_2155592, baseEnd_2155592] using wordTrace_append hprefix tailTrace_2155592
  have hstable : (prefixWord ++ tailWord_2155592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155592).length < 2 ^ (prefixWord ++ tailWord_2155592).sum := by decide
  have hdescent : baseEnd_2155592 < baseStart_2155592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155594 : List Nat := [3, 1, 2, 1, 1, 2, 5, 1, 1, 5]
def baseStart_2155594 : Nat := 118140960795 + 2155594 * 2 ^ 59
def prefixEnd_2155594 : Nat := 4983230072969 + 3 ^ 40 * 2155594 * 2
def baseEnd_2155594 : Nat := 737903878631962974841073

theorem tailTrace_2155594 : CollatzResearch.WordTrace tailWord_2155594 prefixEnd_2155594 737903878631962974841073 := by
  unfold tailWord_2155594
  simp only [CollatzResearch.WordTrace]
  refine ⟨19655243038164639747674459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52413981435105705993798557 19655243038164639747674459)
  ·
    refine ⟨29482864557246959621511689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19655243038164639747674459 29482864557246959621511689)
    ·
      refine ⟨22112148417935219716133767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29482864557246959621511689 22112148417935219716133767)
      ·
        refine ⟨33168222626902829574200651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22112148417935219716133767 33168222626902829574200651)
        ·
          refine ⟨49752333940354244361300977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33168222626902829574200651 49752333940354244361300977)
          ·
            refine ⟨37314250455265683270975733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49752333940354244361300977 37314250455265683270975733)
            ·
              refine ⟨3498210980181157806653975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37314250455265683270975733 3498210980181157806653975)
              ·
                refine ⟨5247316470271736709980963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3498210980181157806653975 5247316470271736709980963)
                ·
                  refine ⟨7870974705407605064971445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5247316470271736709980963 7870974705407605064971445)
                  ·
                    refine ⟨737903878631962974841073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7870974705407605064971445 737903878631962974841073)
                    ·
                      rfl

theorem cell22_2155594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_2155594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2155594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2155594 prefixEnd_2155594 := by exact prefixLift 2155594
  have htrace : WordTrace (prefixWord ++ tailWord_2155594) baseStart_2155594 baseEnd_2155594 := by
    simpa [prefixWord, tailWord_2155594, baseEnd_2155594] using wordTrace_append hprefix tailTrace_2155594
  have hstable : (prefixWord ++ tailWord_2155594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155594).length < 2 ^ (prefixWord ++ tailWord_2155594).sum := by decide
  have hdescent : baseEnd_2155594 < baseStart_2155594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155626 : List Nat := [3, 1, 3, 2, 2, 2, 1, 2, 2, 4]
def baseStart_2155626 : Nat := 118140960795 + 2155626 * 2 ^ 59
def prefixEnd_2155626 : Nat := 4983230072969 + 3 ^ 40 * 2155626 * 2
def baseEnd_2155626 : Nat := 737914832885925558040975

theorem tailTrace_2155626 : CollatzResearch.WordTrace tailWord_2155626 prefixEnd_2155626 737914832885925558040975 := by
  unfold tailWord_2155626
  simp only [CollatzResearch.WordTrace]
  refine ⟨19655534822135657113965683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52414759525695085637241821 19655534822135657113965683)
  ·
    refine ⟨29483302233203485670948525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19655534822135657113965683 29483302233203485670948525)
    ·
      refine ⟨11056238337451307126605697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29483302233203485670948525 11056238337451307126605697)
      ·
        refine ⟨8292178753088480344954273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11056238337451307126605697 8292178753088480344954273)
        ·
          refine ⟨6219134064816360258715705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8292178753088480344954273 6219134064816360258715705)
          ·
            refine ⟨4664350548612270194036779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6219134064816360258715705 4664350548612270194036779)
            ·
              refine ⟨6996525822918405291055169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4664350548612270194036779 6996525822918405291055169)
              ·
                refine ⟨5247394367188803968291377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6996525822918405291055169 5247394367188803968291377)
                ·
                  refine ⟨3935545775391602976218533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5247394367188803968291377 3935545775391602976218533)
                  ·
                    refine ⟨737914832885925558040975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3935545775391602976218533 737914832885925558040975)
                    ·
                      rfl

theorem cell22_2155626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_2155626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2155626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2155626 prefixEnd_2155626 := by exact prefixLift 2155626
  have htrace : WordTrace (prefixWord ++ tailWord_2155626) baseStart_2155626 baseEnd_2155626 := by
    simpa [prefixWord, tailWord_2155626, baseEnd_2155626] using wordTrace_append hprefix tailTrace_2155626
  have hstable : (prefixWord ++ tailWord_2155626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155626).length < 2 ^ (prefixWord ++ tailWord_2155626).sum := by decide
  have hdescent : baseEnd_2155626 < baseStart_2155626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155699 : List Nat := [1, 1, 1, 2, 3, 2, 3, 2, 3, 4]
def baseStart_2155699 : Nat := 118140960795 + 2155699 * 2 ^ 59
def prefixEnd_2155699 : Nat := 4983230072969 + 3 ^ 40 * 2155699 * 2
def baseEnd_2155699 : Nat := 737939822277777700965751

theorem tailTrace_2155699 : CollatzResearch.WordTrace tailWord_2155699 prefixEnd_2155699 737939822277777700965751 := by
  unfold tailWord_2155699
  simp only [CollatzResearch.WordTrace]
  refine ⟨78624801817278161923270151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52416534544852107948846767 78624801817278161923270151)
  ·
    refine ⟨117937202725917242884905227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78624801817278161923270151 117937202725917242884905227)
    ·
      refine ⟨176905804088875864327357841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117937202725917242884905227 176905804088875864327357841)
      ·
        refine ⟨132679353066656898245518381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176905804088875864327357841 132679353066656898245518381)
        ·
          refine ⟨49754757399996336842069393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132679353066656898245518381 49754757399996336842069393)
          ·
            refine ⟨37316068049997252631552045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49754757399996336842069393 37316068049997252631552045)
            ·
              refine ⟨13993525518748969736832017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37316068049997252631552045 13993525518748969736832017)
              ·
                refine ⟨10495144139061727302624013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13993525518748969736832017 10495144139061727302624013)
                ·
                  refine ⟨3935679052148147738484005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10495144139061727302624013 3935679052148147738484005)
                  ·
                    refine ⟨737939822277777700965751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3935679052148147738484005 737939822277777700965751)
                    ·
                      rfl

theorem cell22_2155699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 4].length) (baseStart_2155699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2155699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2155699 prefixEnd_2155699 := by exact prefixLift 2155699
  have htrace : WordTrace (prefixWord ++ tailWord_2155699) baseStart_2155699 baseEnd_2155699 := by
    simpa [prefixWord, tailWord_2155699, baseEnd_2155699] using wordTrace_append hprefix tailTrace_2155699
  have hstable : (prefixWord ++ tailWord_2155699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155699).length < 2 ^ (prefixWord ++ tailWord_2155699).sum := by decide
  have hdescent : baseEnd_2155699 < baseStart_2155699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155733 : List Nat := [1, 3, 2, 4, 1, 2, 1, 3, 1, 4]
def baseStart_2155733 : Nat := 118140960795 + 2155733 * 2 ^ 59
def prefixEnd_2155733 : Nat := 4983230072969 + 3 ^ 40 * 2155733 * 2
def baseEnd_2155733 : Nat := 737951461172612945615647

theorem tailTrace_2155733 : CollatzResearch.WordTrace tailWord_2155733 prefixEnd_2155733 737951461172612945615647 := by
  unfold tailWord_2155733
  simp only [CollatzResearch.WordTrace]
  refine ⟨78626041899154985730007853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52417361266103323820005235 78626041899154985730007853)
  ·
    refine ⟨29484765712183119648752945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78626041899154985730007853 29484765712183119648752945)
    ·
      refine ⟨22113574284137339736564709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29484765712183119648752945 22113574284137339736564709)
      ·
        refine ⟨4146295178275751200605883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22113574284137339736564709 4146295178275751200605883)
        ·
          refine ⟨6219442767413626800908825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4146295178275751200605883 6219442767413626800908825)
          ·
            refine ⟨4664582075560220100681619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6219442767413626800908825 4664582075560220100681619)
            ·
              refine ⟨6996873113340330151022429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4664582075560220100681619 6996873113340330151022429)
              ·
                refine ⟨2623827417502623806633411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6996873113340330151022429 2623827417502623806633411)
                ·
                  refine ⟨3935741126253935709950117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2623827417502623806633411 3935741126253935709950117)
                  ·
                    refine ⟨737951461172612945615647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3935741126253935709950117 737951461172612945615647)
                    ·
                      rfl

theorem cell22_2155733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_2155733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2155733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2155733 prefixEnd_2155733 := by exact prefixLift 2155733
  have htrace : WordTrace (prefixWord ++ tailWord_2155733) baseStart_2155733 baseEnd_2155733 := by
    simpa [prefixWord, tailWord_2155733, baseEnd_2155733] using wordTrace_append hprefix tailTrace_2155733
  have hstable : (prefixWord ++ tailWord_2155733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155733).length < 2 ^ (prefixWord ++ tailWord_2155733).sum := by decide
  have hdescent : baseEnd_2155733 < baseStart_2155733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155911 : List Nat := [1, 1, 4, 2, 2, 3, 9]
def baseStart_2155911 : Nat := 118140960795 + 2155911 * 2 ^ 59
def prefixEnd_2155911 : Nat := 4983230072969 + 3 ^ 40 * 2155911 * 2
def baseEnd_2155911 : Nat := 27333792378158511654263

theorem tailTrace_2155911 : CollatzResearch.WordTrace tailWord_2155911 prefixEnd_2155911 27333792378158511654263 := by
  unfold tailWord_2155911
  simp only [CollatzResearch.WordTrace]
  refine ⟨78632534092510122129987587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52421689395006748086658391 78632534092510122129987587)
  ·
    refine ⟨117948801138765183194981381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78632534092510122129987587 117948801138765183194981381)
    ·
      refine ⟨22115400213518471849059009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117948801138765183194981381 22115400213518471849059009)
      ·
        refine ⟨16586550160138853886794257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22115400213518471849059009 16586550160138853886794257)
        ·
          refine ⟨12439912620104140415095693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16586550160138853886794257 12439912620104140415095693)
          ·
            refine ⟨4664967232539052655660885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12439912620104140415095693 4664967232539052655660885)
            ·
              refine ⟨27333792378158511654263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4664967232539052655660885 27333792378158511654263)
              ·
                rfl

theorem cell22_2155911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 9].length) (baseStart_2155911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2155911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2155911 prefixEnd_2155911 := by exact prefixLift 2155911
  have htrace : WordTrace (prefixWord ++ tailWord_2155911) baseStart_2155911 baseEnd_2155911 := by
    simpa [prefixWord, tailWord_2155911, baseEnd_2155911] using wordTrace_append hprefix tailTrace_2155911
  have hstable : (prefixWord ++ tailWord_2155911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155911).length < 2 ^ (prefixWord ++ tailWord_2155911).sum := by decide
  have hdescent : baseEnd_2155911 < baseStart_2155911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155932 : List Nat := [2, 2, 3, 4, 1, 2, 1, 1, 1, 5]
def baseStart_2155932 : Nat := 118140960795 + 2155932 * 2 ^ 59
def prefixEnd_2155932 : Nat := 4983230072969 + 3 ^ 40 * 2155932 * 2
def baseEnd_2155932 : Nat := 738019582939442759890037

theorem tailTrace_2155932 : CollatzResearch.WordTrace tailWord_2155932 prefixEnd_2155932 738019582939442759890037 := by
  unfold tailWord_2155932
  simp only [CollatzResearch.WordTrace]
  refine ⟨39316650012717021358251025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52422200016956028477668033 39316650012717021358251025)
  ·
    refine ⟨29487487509537766018688269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39316650012717021358251025 29487487509537766018688269)
    ·
      refine ⟨11057807816076662257008101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29487487509537766018688269 11057807816076662257008101)
      ·
        refine ⟨2073338965514374173189019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11057807816076662257008101 2073338965514374173189019)
        ·
          refine ⟨3110008448271561259783529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2073338965514374173189019 3110008448271561259783529)
          ·
            refine ⟨2332506336203670944837647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3110008448271561259783529 2332506336203670944837647)
            ·
              refine ⟨3498759504305506417256471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2332506336203670944837647 3498759504305506417256471)
              ·
                refine ⟨5248139256458259625884707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3498759504305506417256471 5248139256458259625884707)
                ·
                  refine ⟨7872208884687389438827061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5248139256458259625884707 7872208884687389438827061)
                  ·
                    refine ⟨738019582939442759890037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7872208884687389438827061 738019582939442759890037)
                    ·
                      rfl

theorem cell22_2155932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_2155932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2155932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2155932 prefixEnd_2155932 := by exact prefixLift 2155932
  have htrace : WordTrace (prefixWord ++ tailWord_2155932) baseStart_2155932 baseEnd_2155932 := by
    simpa [prefixWord, tailWord_2155932, baseEnd_2155932] using wordTrace_append hprefix tailTrace_2155932
  have hstable : (prefixWord ++ tailWord_2155932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155932).length < 2 ^ (prefixWord ++ tailWord_2155932).sum := by decide
  have hdescent : baseEnd_2155932 < baseStart_2155932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155971 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 4, 5]
def baseStart_2155971 : Nat := 118140960795 + 2155971 * 2 ^ 59
def prefixEnd_2155971 : Nat := 4983230072969 + 3 ^ 40 * 2155971 * 2
def baseEnd_2155971 : Nat := 738032933436459658164917

theorem tailTrace_2155971 : CollatzResearch.WordTrace tailWord_2155971 prefixEnd_2155971 738032933436459658164917 := by
  unfold tailWord_2155971
  simp only [CollatzResearch.WordTrace]
  refine ⟨78634722472292752377171767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52423148314861834918114511 78634722472292752377171767)
  ·
    refine ⟨117952083708439128565757651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78634722472292752377171767 117952083708439128565757651)
    ·
      refine ⟨176928125562658692848636477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117952083708439128565757651 176928125562658692848636477)
      ·
        refine ⟨66348047085997009818238679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176928125562658692848636477 66348047085997009818238679)
        ·
          refine ⟨99522070628995514727358019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66348047085997009818238679 99522070628995514727358019)
          ·
            refine ⟨149283105943493272091037029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99522070628995514727358019 149283105943493272091037029)
            ·
              refine ⟨27990582364404988517069443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 149283105943493272091037029 27990582364404988517069443)
              ·
                refine ⟨41985873546607482775604165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27990582364404988517069443 41985873546607482775604165)
                ·
                  refine ⟨7872351289988903020425781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41985873546607482775604165 7872351289988903020425781)
                  ·
                    refine ⟨738032933436459658164917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7872351289988903020425781 738032933436459658164917)
                    ·
                      rfl

theorem cell22_2155971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 5].length) (baseStart_2155971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2155971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2155971 prefixEnd_2155971 := by exact prefixLift 2155971
  have htrace : WordTrace (prefixWord ++ tailWord_2155971) baseStart_2155971 baseEnd_2155971 := by
    simpa [prefixWord, tailWord_2155971, baseEnd_2155971] using wordTrace_append hprefix tailTrace_2155971
  have hstable : (prefixWord ++ tailWord_2155971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155971).length < 2 ^ (prefixWord ++ tailWord_2155971).sum := by decide
  have hdescent : baseEnd_2155971 < baseStart_2155971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156052 : List Nat := [2, 4, 3, 1, 2, 1, 1, 2, 6]
def baseStart_2156052 : Nat := 118140960795 + 2156052 * 2 ^ 59
def prefixEnd_2156052 : Nat := 4983230072969 + 3 ^ 40 * 2156052 * 2
def baseEnd_2156052 : Nat := 246020220463934148963223

theorem tailTrace_2156052 : CollatzResearch.WordTrace tailWord_2156052 prefixEnd_2156052 246020220463934148963223 := by
  unfold tailWord_2156052
  simp only [CollatzResearch.WordTrace]
  refine ⟨39318838392499651605435205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52425117856666202140580273 39318838392499651605435205)
  ·
    refine ⟨7372282198593684676019101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39318838392499651605435205 7372282198593684676019101)
    ·
      refine ⟨2764605824472631753507163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7372282198593684676019101 2764605824472631753507163)
      ·
        refine ⟨4146908736708947630260745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2764605824472631753507163 4146908736708947630260745)
        ·
          refine ⟨3110181552531710722695559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4146908736708947630260745 3110181552531710722695559)
          ·
            refine ⟨4665272328797566084043339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3110181552531710722695559 4665272328797566084043339)
            ·
              refine ⟨6997908493196349126065009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4665272328797566084043339 6997908493196349126065009)
              ·
                refine ⟨5248431369897261844548757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6997908493196349126065009 5248431369897261844548757)
                ·
                  refine ⟨246020220463934148963223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5248431369897261844548757 246020220463934148963223)
                  ·
                    rfl

theorem cell22_2156052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_2156052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2156052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2156052 prefixEnd_2156052 := by exact prefixLift 2156052
  have htrace : WordTrace (prefixWord ++ tailWord_2156052) baseStart_2156052 baseEnd_2156052 := by
    simpa [prefixWord, tailWord_2156052, baseEnd_2156052] using wordTrace_append hprefix tailTrace_2156052
  have hstable : (prefixWord ++ tailWord_2156052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156052).length < 2 ^ (prefixWord ++ tailWord_2156052).sum := by decide
  have hdescent : baseEnd_2156052 < baseStart_2156052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156065 : List Nat := [1, 2, 3, 2, 2, 2, 3, 1, 2, 4]
def baseStart_2156065 : Nat := 118140960795 + 2156065 * 2 ^ 59
def prefixEnd_2156065 : Nat := 4983230072969 + 3 ^ 40 * 2156065 * 2
def baseEnd_2156065 : Nat := 738065111557474746314629

theorem tailTrace_2156065 : CollatzResearch.WordTrace tailWord_2156065 prefixEnd_2156065 738065111557474746314629 := by
  unfold tailWord_2156065
  simp only [CollatzResearch.WordTrace]
  refine ⟨78638150933952206431093649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52425433955968137620729099 78638150933952206431093649)
  ·
    refine ⟨58978613200464154823320237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78638150933952206431093649 58978613200464154823320237)
    ·
      refine ⟨22116979950174058058745089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58978613200464154823320237 22116979950174058058745089)
      ·
        refine ⟨16587734962630543544058817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22116979950174058058745089 16587734962630543544058817)
        ·
          refine ⟨12440801221972907658044113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16587734962630543544058817 12440801221972907658044113)
          ·
            refine ⟨9330600916479680743533085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12440801221972907658044113 9330600916479680743533085)
            ·
              refine ⟨3498975343679880278824907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9330600916479680743533085 3498975343679880278824907)
              ·
                refine ⟨5248463015519820418237361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3498975343679880278824907 5248463015519820418237361)
                ·
                  refine ⟨3936347261639865313678021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5248463015519820418237361 3936347261639865313678021)
                  ·
                    refine ⟨738065111557474746314629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3936347261639865313678021 738065111557474746314629)
                    ·
                      rfl

theorem cell22_2156065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_2156065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2156065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2156065 prefixEnd_2156065 := by exact prefixLift 2156065
  have htrace : WordTrace (prefixWord ++ tailWord_2156065) baseStart_2156065 baseEnd_2156065 := by
    simpa [prefixWord, tailWord_2156065, baseEnd_2156065] using wordTrace_append hprefix tailTrace_2156065
  have hstable : (prefixWord ++ tailWord_2156065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156065).length < 2 ^ (prefixWord ++ tailWord_2156065).sum := by decide
  have hdescent : baseEnd_2156065 < baseStart_2156065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156095 : List Nat := [1, 1, 2, 2, 3, 3, 1, 3, 3, 3]
def baseStart_2156095 : Nat := 118140960795 + 2156095 * 2 ^ 59
def prefixEnd_2156095 : Nat := 4983230072969 + 3 ^ 40 * 2156095 * 2
def baseEnd_2156095 : Nat := 738075381170564668064537

theorem tailTrace_2156095 : CollatzResearch.WordTrace tailWord_2156095 prefixEnd_2156095 738075381170564668064537 := by
  unfold tailWord_2156095
  simp only [CollatzResearch.WordTrace]
  refine ⟨78639245123843521554685739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52426163415895681036457159 78639245123843521554685739)
  ·
    refine ⟨117958867685765282332028609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78639245123843521554685739 117958867685765282332028609)
    ·
      refine ⟨88469150764323961749021457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117958867685765282332028609 88469150764323961749021457)
      ·
        refine ⟨66351863073242971311766093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88469150764323961749021457 66351863073242971311766093)
        ·
          refine ⟨24881948652466114241912285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66351863073242971311766093 24881948652466114241912285)
          ·
            refine ⟨9330730744674792840717107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24881948652466114241912285 9330730744674792840717107)
            ·
              refine ⟨13996096117012189261075661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9330730744674792840717107 13996096117012189261075661)
              ·
                refine ⟨5248536043879570972903373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13996096117012189261075661 5248536043879570972903373)
                ·
                  refine ⟨1968201016454839114838765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5248536043879570972903373 1968201016454839114838765)
                  ·
                    refine ⟨738075381170564668064537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1968201016454839114838765 738075381170564668064537)
                    ·
                      rfl

theorem cell22_2156095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 3, 3].length) (baseStart_2156095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2156095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2156095 prefixEnd_2156095 := by exact prefixLift 2156095
  have htrace : WordTrace (prefixWord ++ tailWord_2156095) baseStart_2156095 baseEnd_2156095 := by
    simpa [prefixWord, tailWord_2156095, baseEnd_2156095] using wordTrace_append hprefix tailTrace_2156095
  have hstable : (prefixWord ++ tailWord_2156095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156095).length < 2 ^ (prefixWord ++ tailWord_2156095).sum := by decide
  have hdescent : baseEnd_2156095 < baseStart_2156095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156146 : List Nat := [3, 2, 1, 2, 3, 2, 3, 2, 1, 3]
def baseStart_2156146 : Nat := 118140960795 + 2156146 * 2 ^ 59
def prefixEnd_2156146 : Nat := 4983230072969 + 3 ^ 40 * 2156146 * 2
def baseEnd_2156146 : Nat := 738092839512817535039381

theorem tailTrace_2156146 : CollatzResearch.WordTrace tailWord_2156146 prefixEnd_2156146 738092839512817535039381 := by
  unfold tailWord_2156146
  simp only [CollatzResearch.WordTrace]
  refine ⟨19660276311664689316198073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52427403497772504843194861 19660276311664689316198073)
  ·
    refine ⟨14745207233748516987148555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19660276311664689316198073 14745207233748516987148555)
    ·
      refine ⟨22117810850622775480722833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14745207233748516987148555 22117810850622775480722833)
      ·
        refine ⟨16588358137967081610542125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22117810850622775480722833 16588358137967081610542125)
        ·
          refine ⟨6220634301737655603953297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16588358137967081610542125 6220634301737655603953297)
          ·
            refine ⟨4665475726303241702964973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6220634301737655603953297 4665475726303241702964973)
            ·
              refine ⟨1749553397363715638611865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4665475726303241702964973 1749553397363715638611865)
              ·
                refine ⟨1312165048022786728958899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1749553397363715638611865 1312165048022786728958899)
                ·
                  refine ⟨1968247572034180093438349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1312165048022786728958899 1968247572034180093438349)
                  ·
                    refine ⟨738092839512817535039381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1968247572034180093438349 738092839512817535039381)
                    ·
                      rfl

theorem cell22_2156146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 2, 1, 3].length) (baseStart_2156146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2156146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2156146 prefixEnd_2156146 := by exact prefixLift 2156146
  have htrace : WordTrace (prefixWord ++ tailWord_2156146) baseStart_2156146 baseEnd_2156146 := by
    simpa [prefixWord, tailWord_2156146, baseEnd_2156146] using wordTrace_append hprefix tailTrace_2156146
  have hstable : (prefixWord ++ tailWord_2156146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156146).length < 2 ^ (prefixWord ++ tailWord_2156146).sum := by decide
  have hdescent : baseEnd_2156146 < baseStart_2156146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156185 : List Nat := [1, 2, 1, 2, 1, 2, 2, 4, 4, 3]
def baseStart_2156185 : Nat := 118140960795 + 2156185 * 2 ^ 59
def prefixEnd_2156185 : Nat := 4983230072969 + 3 ^ 40 * 2156185 * 2
def baseEnd_2156185 : Nat := 738106190009834433314261

theorem tailTrace_2156185 : CollatzResearch.WordTrace tailWord_2156185 prefixEnd_2156185 738106190009834433314261 := by
  unfold tailWord_2156185
  simp only [CollatzResearch.WordTrace]
  refine ⟨78642527693517466925462009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52428351795678311283641339 78642527693517466925462009)
  ·
    refine ⟨58981895770138100194096507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78642527693517466925462009 58981895770138100194096507)
    ·
      refine ⟨88472843655207150291144761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58981895770138100194096507 88472843655207150291144761)
      ·
        refine ⟨66354632741405362718358571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88472843655207150291144761 66354632741405362718358571)
        ·
          refine ⟨99531949112108044077537857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66354632741405362718358571 99531949112108044077537857)
          ·
            refine ⟨74648961834081033058153393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99531949112108044077537857 74648961834081033058153393)
            ·
              refine ⟨55986721375560774793615045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74648961834081033058153393 55986721375560774793615045)
              ·
                refine ⟨10497510257917645273802821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55986721375560774793615045 10497510257917645273802821)
                ·
                  refine ⟨1968283173359558488838029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10497510257917645273802821 1968283173359558488838029)
                  ·
                    refine ⟨738106190009834433314261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1968283173359558488838029 738106190009834433314261)
                    ·
                      rfl

theorem cell22_2156185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 4, 3].length) (baseStart_2156185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2156185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2156185 prefixEnd_2156185 := by exact prefixLift 2156185
  have htrace : WordTrace (prefixWord ++ tailWord_2156185) baseStart_2156185 baseEnd_2156185 := by
    simpa [prefixWord, tailWord_2156185, baseEnd_2156185] using wordTrace_append hprefix tailTrace_2156185
  have hstable : (prefixWord ++ tailWord_2156185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156185).length < 2 ^ (prefixWord ++ tailWord_2156185).sum := by decide
  have hdescent : baseEnd_2156185 < baseStart_2156185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156215 : List Nat := [1, 1, 3, 1, 5, 1, 3, 7]
def baseStart_2156215 : Nat := 118140960795 + 2156215 * 2 ^ 59
def prefixEnd_2156215 : Nat := 4983230072969 + 3 ^ 40 * 2156215 * 2
def baseEnd_2156215 : Nat := 82012939958102706118241

theorem tailTrace_2156215 : CollatzResearch.WordTrace tailWord_2156215 prefixEnd_2156215 82012939958102706118241 := by
  unfold tailWord_2156215
  simp only [CollatzResearch.WordTrace]
  refine ⟨78643621883408782049054099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52429081255605854699369399 78643621883408782049054099)
  ·
    refine ⟨117965432825113173073581149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78643621883408782049054099 117965432825113173073581149)
    ·
      refine ⟨44237037309417439902592931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117965432825113173073581149 44237037309417439902592931)
      ·
        refine ⟨66355555964126159853889397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44237037309417439902592931 66355555964126159853889397)
        ·
          refine ⟨6220833371636827486302131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66355555964126159853889397 6220833371636827486302131)
          ·
            refine ⟨9331250057455241229453197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6220833371636827486302131 9331250057455241229453197)
            ·
              refine ⟨3499218771545715461044949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9331250057455241229453197 3499218771545715461044949)
              ·
                refine ⟨82012939958102706118241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3499218771545715461044949 82012939958102706118241)
                ·
                  rfl

theorem cell22_2156215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 7].length) (baseStart_2156215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2156215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2156215 prefixEnd_2156215 := by exact prefixLift 2156215
  have htrace : WordTrace (prefixWord ++ tailWord_2156215) baseStart_2156215 baseEnd_2156215 := by
    simpa [prefixWord, tailWord_2156215, baseEnd_2156215] using wordTrace_append hprefix tailTrace_2156215
  have hstable : (prefixWord ++ tailWord_2156215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156215).length < 2 ^ (prefixWord ++ tailWord_2156215).sum := by decide
  have hdescent : baseEnd_2156215 < baseStart_2156215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156234 : List Nat := [3, 1, 2, 1, 5, 2, 1, 1, 2, 4]
def baseStart_2156234 : Nat := 118140960795 + 2156234 * 2 ^ 59
def prefixEnd_2156234 : Nat := 4983230072969 + 3 ^ 40 * 2156234 * 2
def baseEnd_2156234 : Nat := 738122963711214638839111

theorem tailTrace_2156234 : CollatzResearch.WordTrace tailWord_2156234 prefixEnd_2156234 738122963711214638839111 := by
  unfold tailWord_2156234
  simp only [CollatzResearch.WordTrace]
  refine ⟨19661078717584987073498939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52429543246893298862663837 19661078717584987073498939)
  ·
    refine ⟨29491618076377480610248409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19661078717584987073498939 29491618076377480610248409)
    ·
      refine ⟨22118713557283110457686307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29491618076377480610248409 22118713557283110457686307)
      ·
        refine ⟨33178070335924665686529461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22118713557283110457686307 33178070335924665686529461)
        ·
          refine ⟨3110444093992937408112137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33178070335924665686529461 3110444093992937408112137)
          ·
            refine ⟨2332833070494703056084103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3110444093992937408112137 2332833070494703056084103)
            ·
              refine ⟨3499249605742054584126155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2332833070494703056084103 3499249605742054584126155)
              ·
                refine ⟨5248874408613081876189233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3499249605742054584126155 5248874408613081876189233)
                ·
                  refine ⟨3936655806459811407141925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5248874408613081876189233 3936655806459811407141925)
                  ·
                    refine ⟨738122963711214638839111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3936655806459811407141925 738122963711214638839111)
                    ·
                      rfl

theorem cell22_2156234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_2156234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2156234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2156234 prefixEnd_2156234 := by exact prefixLift 2156234
  have htrace : WordTrace (prefixWord ++ tailWord_2156234) baseStart_2156234 baseEnd_2156234 := by
    simpa [prefixWord, tailWord_2156234, baseEnd_2156234] using wordTrace_append hprefix tailTrace_2156234
  have hstable : (prefixWord ++ tailWord_2156234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156234).length < 2 ^ (prefixWord ++ tailWord_2156234).sum := by decide
  have hdescent : baseEnd_2156234 < baseStart_2156234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156253 : List Nat := [1, 4, 3, 3, 1, 2, 1, 2, 2, 3]
def baseStart_2156253 : Nat := 118140960795 + 2156253 * 2 ^ 59
def prefixEnd_2156253 : Nat := 4983230072969 + 3 ^ 40 * 2156253 * 2
def baseEnd_2156253 : Nat := 738129467799504922614053

theorem tailTrace_2156253 : CollatzResearch.WordTrace tailWord_2156253 prefixEnd_2156253 738129467799504922614053 := by
  unfold tailWord_2156253
  simp only [CollatzResearch.WordTrace]
  refine ⟨78645007857271114538937413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52430005238180743025958275 78645007857271114538937413)
  ·
    refine ⟨14745938973238333976050765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78645007857271114538937413 14745938973238333976050765)
    ·
      refine ⟨5529727114964375241019037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14745938973238333976050765 5529727114964375241019037)
      ·
        refine ⟨2073647668111640715382139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5529727114964375241019037 2073647668111640715382139)
        ·
          refine ⟨3110471502167461073073209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2073647668111640715382139 3110471502167461073073209)
          ·
            refine ⟨2332853626625595804804907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3110471502167461073073209 2332853626625595804804907)
            ·
              refine ⟨3499280439938393707207361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2332853626625595804804907 3499280439938393707207361)
              ·
                refine ⟨2624460329953795280405521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3499280439938393707207361 2624460329953795280405521)
                ·
                  refine ⟨1968345247465346460304141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2624460329953795280405521 1968345247465346460304141)
                  ·
                    refine ⟨738129467799504922614053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1968345247465346460304141 738129467799504922614053)
                    ·
                      rfl

theorem cell22_2156253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_2156253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2156253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2156253 prefixEnd_2156253 := by exact prefixLift 2156253
  have htrace : WordTrace (prefixWord ++ tailWord_2156253) baseStart_2156253 baseEnd_2156253 := by
    simpa [prefixWord, tailWord_2156253, baseEnd_2156253] using wordTrace_append hprefix tailTrace_2156253
  have hstable : (prefixWord ++ tailWord_2156253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156253).length < 2 ^ (prefixWord ++ tailWord_2156253).sum := by decide
  have hdescent : baseEnd_2156253 < baseStart_2156253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156260 : List Nat := [2, 3, 1, 1, 1, 3, 3, 1, 7]
def baseStart_2156260 : Nat := 118140960795 + 2156260 * 2 ^ 59
def prefixEnd_2156260 : Nat := 4983230072969 + 3 ^ 40 * 2156260 * 2
def baseEnd_2156260 : Nat := 246043954680853079229677

theorem tailTrace_2156260 : CollatzResearch.WordTrace tailWord_2156260 prefixEnd_2156260 246043954680853079229677 := by
  unfold tailWord_2156260
  simp only [CollatzResearch.WordTrace]
  refine ⟨39322631584122877367221117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52430175445497169822961489 39322631584122877367221117)
  ·
    refine ⟨14745986844046079012707919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39322631584122877367221117 14745986844046079012707919)
    ·
      refine ⟨22118980266069118519061879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14745986844046079012707919 22118980266069118519061879)
      ·
        refine ⟨33178470399103677778592819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22118980266069118519061879 33178470399103677778592819)
        ·
          refine ⟨49767705598655516667889229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33178470399103677778592819 49767705598655516667889229)
          ·
            refine ⟨18662889599495818750458461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49767705598655516667889229 18662889599495818750458461)
            ·
              refine ⟨6998583599810932031421923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18662889599495818750458461 6998583599810932031421923)
              ·
                refine ⟨10497875399716398047132885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6998583599810932031421923 10497875399716398047132885)
                ·
                  refine ⟨246043954680853079229677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10497875399716398047132885 246043954680853079229677)
                  ·
                    rfl

theorem cell22_2156260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_2156260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2156260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2156260 prefixEnd_2156260 := by exact prefixLift 2156260
  have htrace : WordTrace (prefixWord ++ tailWord_2156260) baseStart_2156260 baseEnd_2156260 := by
    simpa [prefixWord, tailWord_2156260, baseEnd_2156260] using wordTrace_append hprefix tailTrace_2156260
  have hstable : (prefixWord ++ tailWord_2156260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156260).length < 2 ^ (prefixWord ++ tailWord_2156260).sum := by decide
  have hdescent : baseEnd_2156260 < baseStart_2156260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156264 : List Nat := [2, 1, 4, 1, 3, 2, 2, 1, 3, 3]
def baseStart_2156264 : Nat := 118140960795 + 2156264 * 2 ^ 59
def prefixEnd_2156264 : Nat := 4983230072969 + 3 ^ 40 * 2156264 * 2
def baseEnd_2156264 : Nat := 738133233324304560589019

theorem tailTrace_2156264 : CollatzResearch.WordTrace tailWord_2156264 prefixEnd_2156264 738133233324304560589019 := by
  unfold tailWord_2156264
  simp only [CollatzResearch.WordTrace]
  refine ⟨39322704530115631708793923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52430272706820842278391897 39322704530115631708793923)
  ·
    refine ⟨58984056795173447563190885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39322704530115631708793923 58984056795173447563190885)
    ·
      refine ⟨11059510649095021418098291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58984056795173447563190885 11059510649095021418098291)
      ·
        refine ⟨16589265973642532127147437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11059510649095021418098291 16589265973642532127147437)
        ·
          refine ⟨6220974740115949547680289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16589265973642532127147437 6220974740115949547680289)
          ·
            refine ⟨4665731055086962160760217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6220974740115949547680289 4665731055086962160760217)
            ·
              refine ⟨3499298291315221620570163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4665731055086962160760217 3499298291315221620570163)
              ·
                refine ⟨5248947436972832430855245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3499298291315221620570163 5248947436972832430855245)
                ·
                  refine ⟨1968355288864812161570717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5248947436972832430855245 1968355288864812161570717)
                  ·
                    refine ⟨738133233324304560589019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1968355288864812161570717 738133233324304560589019)
                    ·
                      rfl

theorem cell22_2156264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_2156264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2156264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2156264 prefixEnd_2156264 := by exact prefixLift 2156264
  have htrace : WordTrace (prefixWord ++ tailWord_2156264) baseStart_2156264 baseEnd_2156264 := by
    simpa [prefixWord, tailWord_2156264, baseEnd_2156264] using wordTrace_append hprefix tailTrace_2156264
  have hstable : (prefixWord ++ tailWord_2156264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156264).length < 2 ^ (prefixWord ++ tailWord_2156264).sum := by decide
  have hdescent : baseEnd_2156264 < baseStart_2156264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156275 : List Nat := [1, 1, 1, 2, 2, 3, 4, 1, 2, 5]
def baseStart_2156275 : Nat := 118140960795 + 2156275 * 2 ^ 59
def prefixEnd_2156275 : Nat := 4983230072969 + 3 ^ 40 * 2156275 * 2
def baseEnd_2156275 : Nat := 738136998849104198563985

theorem tailTrace_2156275 : CollatzResearch.WordTrace tailWord_2156275 prefixEnd_2156275 738136998849104198563985 := by
  unfold tailWord_2156275
  simp only [CollatzResearch.WordTrace]
  refine ⟨78645810263191412296238279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52430540175460941530825519 78645810263191412296238279)
  ·
    refine ⟨117968715394787118444357419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78645810263191412296238279 117968715394787118444357419)
    ·
      refine ⟨176953073092180677666536129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117968715394787118444357419 176953073092180677666536129)
      ·
        refine ⟨132714804819135508249902097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176953073092180677666536129 132714804819135508249902097)
        ·
          refine ⟨99536103614351631187426573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132714804819135508249902097 99536103614351631187426573)
          ·
            refine ⟨37326038855381861695284965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99536103614351631187426573 37326038855381861695284965)
            ·
              refine ⟨6998632285384099067865931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37326038855381861695284965 6998632285384099067865931)
              ·
                refine ⟨10497948428076148601798897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6998632285384099067865931 10497948428076148601798897)
                ·
                  refine ⟨7873461321057111451349173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10497948428076148601798897 7873461321057111451349173)
                  ·
                    refine ⟨738136998849104198563985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7873461321057111451349173 738136998849104198563985)
                    ·
                      rfl

theorem cell22_2156275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 5].length) (baseStart_2156275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2156275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2156275 prefixEnd_2156275 := by exact prefixLift 2156275
  have htrace : WordTrace (prefixWord ++ tailWord_2156275) baseStart_2156275 baseEnd_2156275 := by
    simpa [prefixWord, tailWord_2156275, baseEnd_2156275] using wordTrace_append hprefix tailTrace_2156275
  have hstable : (prefixWord ++ tailWord_2156275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156275).length < 2 ^ (prefixWord ++ tailWord_2156275).sum := by decide
  have hdescent : baseEnd_2156275 < baseStart_2156275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156341 : List Nat := [1, 3, 3, 1, 4, 2, 1, 2, 1, 4]
def baseStart_2156341 : Nat := 118140960795 + 2156341 * 2 ^ 59
def prefixEnd_2156341 : Nat := 4983230072969 + 3 ^ 40 * 2156341 * 2
def baseEnd_2156341 : Nat := 738159591997902026413783

theorem tailTrace_2156341 : CollatzResearch.WordTrace tailWord_2156341 prefixEnd_2156341 738159591997902026413783 := by
  unfold tailWord_2156341
  simp only [CollatzResearch.WordTrace]
  refine ⟨78648217480952305568140877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52432144987301537045427251 78648217480952305568140877)
  ·
    refine ⟨29493081555357114588052829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78648217480952305568140877 29493081555357114588052829)
    ·
      refine ⟨11059905583258917970519811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29493081555357114588052829 11059905583258917970519811)
      ·
        refine ⟨16589858374888376955779717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11059905583258917970519811 16589858374888376955779717)
        ·
          refine ⟨3110598445291570679208697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16589858374888376955779717 3110598445291570679208697)
          ·
            refine ⟨2332948833968678009406523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3110598445291570679208697 2332948833968678009406523)
            ·
              refine ⟨3499423250953017014109785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2332948833968678009406523 3499423250953017014109785)
              ·
                refine ⟨2624567438214762760582339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3499423250953017014109785 2624567438214762760582339)
                ·
                  refine ⟨3936851157322144140873509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2624567438214762760582339 3936851157322144140873509)
                  ·
                    refine ⟨738159591997902026413783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3936851157322144140873509 738159591997902026413783)
                    ·
                      rfl

theorem cell22_2156341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_2156341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2156341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2156341 prefixEnd_2156341 := by exact prefixLift 2156341
  have htrace : WordTrace (prefixWord ++ tailWord_2156341) baseStart_2156341 baseEnd_2156341 := by
    simpa [prefixWord, tailWord_2156341, baseEnd_2156341] using wordTrace_append hprefix tailTrace_2156341
  have hstable : (prefixWord ++ tailWord_2156341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156341).length < 2 ^ (prefixWord ++ tailWord_2156341).sum := by decide
  have hdescent : baseEnd_2156341 < baseStart_2156341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156395 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 9]
def baseStart_2156395 : Nat := 118140960795 + 2156395 * 2 ^ 59
def prefixEnd_2156395 : Nat := 4983230072969 + 3 ^ 40 * 2156395 * 2
def baseEnd_2156395 : Nat := 246059359100487961854539

theorem tailTrace_2156395 : CollatzResearch.WordTrace tailWord_2156395 prefixEnd_2156395 246059359100487961854539 := by
  unfold tailWord_2156395
  simp only [CollatzResearch.WordTrace]
  refine ⟨78650187022756672790606639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52433458015171115193737759 78650187022756672790606639)
  ·
    refine ⟨117975280534135009185909959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78650187022756672790606639 117975280534135009185909959)
    ·
      refine ⟨176962920801202513778864939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117975280534135009185909959 176962920801202513778864939)
      ·
        refine ⟨265444381201803770668297409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176962920801202513778864939 265444381201803770668297409)
        ·
          refine ⟨199083285901352828001223057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 265444381201803770668297409 199083285901352828001223057)
          ·
            refine ⟨149312464426014621000917293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199083285901352828001223057 149312464426014621000917293)
            ·
              refine ⟨55992174159755482875343985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 149312464426014621000917293 55992174159755482875343985)
              ·
                refine ⟨41994130619816612156507989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55992174159755482875343985 41994130619816612156507989)
                ·
                  refine ⟨246059359100487961854539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41994130619816612156507989 246059359100487961854539)
                  ·
                    rfl

theorem cell22_2156395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 9].length) (baseStart_2156395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2156395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2156395 prefixEnd_2156395 := by exact prefixLift 2156395
  have htrace : WordTrace (prefixWord ++ tailWord_2156395) baseStart_2156395 baseEnd_2156395 := by
    simpa [prefixWord, tailWord_2156395, baseEnd_2156395] using wordTrace_append hprefix tailTrace_2156395
  have hstable : (prefixWord ++ tailWord_2156395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156395).length < 2 ^ (prefixWord ++ tailWord_2156395).sum := by decide
  have hdescent : baseEnd_2156395 < baseStart_2156395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156416 : List Nat := [2, 1, 1, 2, 1, 2, 6, 3, 1, 3]
def baseStart_2156416 : Nat := 118140960795 + 2156416 * 2 ^ 59
def prefixEnd_2156416 : Nat := 4983230072969 + 3 ^ 40 * 2156416 * 2
def baseEnd_2156416 : Nat := 738185266030626830788553

theorem tailTrace_2156416 : CollatzResearch.WordTrace tailWord_2156416 prefixEnd_2156416 738185266030626830788553 := by
  unfold tailWord_2156416
  simp only [CollatzResearch.WordTrace]
  refine ⟨39325476477840296688560551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52433968637120395584747401 39325476477840296688560551)
  ·
    refine ⟨58988214716760445032840827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39325476477840296688560551 58988214716760445032840827)
    ·
      refine ⟨88482322075140667549261241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58988214716760445032840827 88482322075140667549261241)
      ·
        refine ⟨66361741556355500661945931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88482322075140667549261241 66361741556355500661945931)
        ·
          refine ⟨99542612334533250992918897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66361741556355500661945931 99542612334533250992918897)
          ·
            refine ⟨74656959250899938244689173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99542612334533250992918897 74656959250899938244689173)
            ·
              refine ⟨3499544964885934605219805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 74656959250899938244689173 3499544964885934605219805)
              ·
                refine ⟨1312329361832225476957427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3499544964885934605219805 1312329361832225476957427)
                ·
                  refine ⟨1968494042748338215436141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1312329361832225476957427 1968494042748338215436141)
                  ·
                    refine ⟨738185266030626830788553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1968494042748338215436141 738185266030626830788553)
                    ·
                      rfl

theorem cell22_2156416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 3, 1, 3].length) (baseStart_2156416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2156416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2156416 prefixEnd_2156416 := by exact prefixLift 2156416
  have htrace : WordTrace (prefixWord ++ tailWord_2156416) baseStart_2156416 baseEnd_2156416 := by
    simpa [prefixWord, tailWord_2156416, baseEnd_2156416] using wordTrace_append hprefix tailTrace_2156416
  have hstable : (prefixWord ++ tailWord_2156416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156416).length < 2 ^ (prefixWord ++ tailWord_2156416).sum := by decide
  have hdescent : baseEnd_2156416 < baseStart_2156416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156444 : List Nat := [2, 2, 3, 3, 1, 1, 2, 1, 2, 5]
def baseStart_2156444 : Nat := 118140960795 + 2156444 * 2 ^ 59
def prefixEnd_2156444 : Nat := 4983230072969 + 3 ^ 40 * 2156444 * 2
def baseEnd_2156444 : Nat := 738194851002844091088467

theorem tailTrace_2156444 : CollatzResearch.WordTrace tailWord_2156444 prefixEnd_2156444 738194851002844091088467 := by
  unfold tailWord_2156444
  simp only [CollatzResearch.WordTrace]
  refine ⟨39325987099789577079570193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52434649466386102772760257 39325987099789577079570193)
  ·
    refine ⟨29494490324842182809677645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39325987099789577079570193 29494490324842182809677645)
    ·
      refine ⟨11060433871815818553629117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29494490324842182809677645 11060433871815818553629117)
      ·
        refine ⟨4147662701930931957610919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11060433871815818553629117 4147662701930931957610919)
        ·
          refine ⟨6221494052896397936416379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4147662701930931957610919 6221494052896397936416379)
          ·
            refine ⟨9332241079344596904624569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6221494052896397936416379 9332241079344596904624569)
            ·
              refine ⟨6999180809508447678468427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9332241079344596904624569 6999180809508447678468427)
              ·
                refine ⟨10498771214262671517702641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6999180809508447678468427 10498771214262671517702641)
                ·
                  refine ⟨7874078410697003638276981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10498771214262671517702641 7874078410697003638276981)
                  ·
                    refine ⟨738194851002844091088467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7874078410697003638276981 738194851002844091088467)
                    ·
                      rfl

theorem cell22_2156444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_2156444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2156444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2156444 prefixEnd_2156444 := by exact prefixLift 2156444
  have htrace : WordTrace (prefixWord ++ tailWord_2156444) baseStart_2156444 baseEnd_2156444 := by
    simpa [prefixWord, tailWord_2156444, baseEnd_2156444] using wordTrace_append hprefix tailTrace_2156444
  have hstable : (prefixWord ++ tailWord_2156444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156444).length < 2 ^ (prefixWord ++ tailWord_2156444).sum := by decide
  have hdescent : baseEnd_2156444 < baseStart_2156444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156472 : List Nat := [2, 1, 2, 1, 2, 3, 2, 1, 3, 5]
def baseStart_2156472 : Nat := 118140960795 + 2156472 * 2 ^ 59
def prefixEnd_2156472 : Nat := 4983230072969 + 3 ^ 40 * 2156472 * 2
def baseEnd_2156472 : Nat := 738204435975061351388381

theorem tailTrace_2156472 : CollatzResearch.WordTrace tailWord_2156472 prefixEnd_2156472 738204435975061351388381 := by
  unfold tailWord_2156472
  simp only [CollatzResearch.WordTrace]
  refine ⟨39326497721738857470579835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52435330295651809960773113 39326497721738857470579835)
  ·
    refine ⟨58989746582608286205869753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39326497721738857470579835 58989746582608286205869753)
    ·
      refine ⟨44242309936956214654402315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58989746582608286205869753 44242309936956214654402315)
      ·
        refine ⟨66363464905434321981603473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44242309936956214654402315 66363464905434321981603473)
        ·
          refine ⟨49772598679075741486202605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66363464905434321981603473 49772598679075741486202605)
          ·
            refine ⟨18664724504653403057325977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49772598679075741486202605 18664724504653403057325977)
            ·
              refine ⟨13998543378490052292994483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18664724504653403057325977 13998543378490052292994483)
              ·
                refine ⟨20997815067735078439491725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13998543378490052292994483 20997815067735078439491725)
                ·
                  refine ⟨7874180650400654414809397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20997815067735078439491725 7874180650400654414809397)
                  ·
                    refine ⟨738204435975061351388381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7874180650400654414809397 738204435975061351388381)
                    ·
                      rfl

theorem cell22_2156472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_2156472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2156472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2156472 prefixEnd_2156472 := by exact prefixLift 2156472
  have htrace : WordTrace (prefixWord ++ tailWord_2156472) baseStart_2156472 baseEnd_2156472 := by
    simpa [prefixWord, tailWord_2156472, baseEnd_2156472] using wordTrace_append hprefix tailTrace_2156472
  have hstable : (prefixWord ++ tailWord_2156472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156472).length < 2 ^ (prefixWord ++ tailWord_2156472).sum := by decide
  have hdescent : baseEnd_2156472 < baseStart_2156472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156474 : List Nat := [3, 1, 1, 1, 2, 1, 2, 7, 4]
def baseStart_2156474 : Nat := 118140960795 + 2156474 * 2 ^ 59
def prefixEnd_2156474 : Nat := 4983230072969 + 3 ^ 40 * 2156474 * 2
def baseEnd_2156474 : Nat := 246068373538644670946125

theorem tailTrace_2156474 : CollatzResearch.WordTrace tailWord_2156474 prefixEnd_2156474 246068373538644670946125 := by
  unfold tailWord_2156474
  simp only [CollatzResearch.WordTrace]
  refine ⟨19663267097367617320683119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52435378926313646188488317 19663267097367617320683119)
  ·
    refine ⟨29494900646051425981024679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19663267097367617320683119 29494900646051425981024679)
    ·
      refine ⟨44242350969077138971537019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29494900646051425981024679 44242350969077138971537019)
      ·
        refine ⟨66363526453615708457305529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44242350969077138971537019 66363526453615708457305529)
        ·
          refine ⟨49772644840211781342979147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66363526453615708457305529 49772644840211781342979147)
          ·
            refine ⟨74658967260317672014468721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49772644840211781342979147 74658967260317672014468721)
            ·
              refine ⟨55994225445238254010851541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74658967260317672014468721 55994225445238254010851541)
              ·
                refine ⟨1312364658872771578379333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 55994225445238254010851541 1312364658872771578379333)
                ·
                  refine ⟨246068373538644670946125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1312364658872771578379333 246068373538644670946125)
                  ·
                    rfl

theorem cell22_2156474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 7, 4].length) (baseStart_2156474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2156474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2156474 prefixEnd_2156474 := by exact prefixLift 2156474
  have htrace : WordTrace (prefixWord ++ tailWord_2156474) baseStart_2156474 baseEnd_2156474 := by
    simpa [prefixWord, tailWord_2156474, baseEnd_2156474] using wordTrace_append hprefix tailTrace_2156474
  have hstable : (prefixWord ++ tailWord_2156474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156474).length < 2 ^ (prefixWord ++ tailWord_2156474).sum := by decide
  have hdescent : baseEnd_2156474 < baseStart_2156474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156491 : List Nat := [1, 1, 1, 1, 3, 4, 5, 2, 4]
def baseStart_2156491 : Nat := 118140960795 + 2156491 * 2 ^ 59
def prefixEnd_2156491 : Nat := 4983230072969 + 3 ^ 40 * 2156491 * 2
def baseEnd_2156491 : Nat := 246070313354450545054441

theorem tailTrace_2156491 : CollatzResearch.WordTrace tailWord_2156491 prefixEnd_2156491 246070313354450545054441 := by
  unfold tailWord_2156491
  simp only [CollatzResearch.WordTrace]
  refine ⟨78653688430408881186101327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52435792286939254124067551 78653688430408881186101327)
  ·
    refine ⟨117980532645613321779151991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78653688430408881186101327 117980532645613321779151991)
    ·
      refine ⟨176970798968419982668727987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117980532645613321779151991 176970798968419982668727987)
      ·
        refine ⟨265456198452629974003091981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176970798968419982668727987 265456198452629974003091981)
        ·
          refine ⟨99546074419736240251159493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 265456198452629974003091981 99546074419736240251159493)
          ·
            refine ⟨18664888953700545047092405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99546074419736240251159493 18664888953700545047092405)
            ·
              refine ⟨1749833339409426098164913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18664888953700545047092405 1749833339409426098164913)
              ·
                refine ⟨1312375004557069573623685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1749833339409426098164913 1312375004557069573623685)
                ·
                  refine ⟨246070313354450545054441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1312375004557069573623685 246070313354450545054441)
                  ·
                    rfl

theorem cell22_2156491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 2, 4].length) (baseStart_2156491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2156491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2156491 prefixEnd_2156491 := by exact prefixLift 2156491
  have htrace : WordTrace (prefixWord ++ tailWord_2156491) baseStart_2156491 baseEnd_2156491 := by
    simpa [prefixWord, tailWord_2156491, baseEnd_2156491] using wordTrace_append hprefix tailTrace_2156491
  have hstable : (prefixWord ++ tailWord_2156491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156491).length < 2 ^ (prefixWord ++ tailWord_2156491).sum := by decide
  have hdescent : baseEnd_2156491 < baseStart_2156491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156547 : List Nat := [1, 1, 1, 3, 2, 1, 1, 5, 7]
def baseStart_2156547 : Nat := 118140960795 + 2156547 * 2 ^ 59
def prefixEnd_2156547 : Nat := 4983230072969 + 3 ^ 40 * 2156547 * 2
def baseEnd_2156547 : Nat := 246076703335928718587717

theorem tailTrace_2156547 : CollatzResearch.WordTrace tailWord_2156547 prefixEnd_2156547 246076703335928718587717 := by
  unfold tailWord_2156547
  simp only [CollatzResearch.WordTrace]
  refine ⟨78655730918206002750139895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52437153945470668500093263 78655730918206002750139895)
  ·
    refine ⟨117983596377309004125209843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78655730918206002750139895 117983596377309004125209843)
    ·
      refine ⟨176975394565963506187814765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117983596377309004125209843 176975394565963506187814765)
      ·
        refine ⟨66365772962236314820430537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176975394565963506187814765 66365772962236314820430537)
        ·
          refine ⟨49774329721677236115322903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66365772962236314820430537 49774329721677236115322903)
          ·
            refine ⟨74661494582515854172984355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49774329721677236115322903 74661494582515854172984355)
            ·
              refine ⟨111992241873773781259476533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74661494582515854172984355 111992241873773781259476533)
              ·
                refine ⟨10499272675666291993075925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 111992241873773781259476533 10499272675666291993075925)
                ·
                  refine ⟨246076703335928718587717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10499272675666291993075925 246076703335928718587717)
                  ·
                    rfl

theorem cell22_2156547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 7].length) (baseStart_2156547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2156547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2156547 prefixEnd_2156547 := by exact prefixLift 2156547
  have htrace : WordTrace (prefixWord ++ tailWord_2156547) baseStart_2156547 baseEnd_2156547 := by
    simpa [prefixWord, tailWord_2156547, baseEnd_2156547] using wordTrace_append hprefix tailTrace_2156547
  have hstable : (prefixWord ++ tailWord_2156547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156547).length < 2 ^ (prefixWord ++ tailWord_2156547).sum := by decide
  have hdescent : baseEnd_2156547 < baseStart_2156547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156656 : List Nat := [2, 1, 1, 1, 5, 3, 1, 2, 2, 4]
def baseStart_2156656 : Nat := 118140960795 + 2156656 * 2 ^ 59
def prefixEnd_2156656 : Nat := 4983230072969 + 3 ^ 40 * 2156656 * 2
def baseEnd_2156656 : Nat := 738267422935346204787817

theorem tailTrace_2156656 : CollatzResearch.WordTrace tailWord_2156656 prefixEnd_2156656 738267422935346204787817 := by
  unfold tailWord_2156656
  simp only [CollatzResearch.WordTrace]
  refine ⟨39329853237405557182928911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52439804316540742910571881 39329853237405557182928911)
  ·
    refine ⟨58994779856108335774393367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39329853237405557182928911 58994779856108335774393367)
    ·
      refine ⟨88492169784162503661590051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58994779856108335774393367 88492169784162503661590051)
      ·
        refine ⟨132738254676243755492385077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88492169784162503661590051 132738254676243755492385077)
        ·
          refine ⟨12444211375897852077411101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 132738254676243755492385077 12444211375897852077411101)
          ·
            refine ⟨4666579265961694529029163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12444211375897852077411101 4666579265961694529029163)
            ·
              refine ⟨6999868898942541793543745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4666579265961694529029163 6999868898942541793543745)
              ·
                refine ⟨5249901674206906345157809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6999868898942541793543745 5249901674206906345157809)
                ·
                  refine ⟨3937426255655179758868357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5249901674206906345157809 3937426255655179758868357)
                  ·
                    refine ⟨738267422935346204787817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3937426255655179758868357 738267422935346204787817)
                    ·
                      rfl

theorem cell22_2156656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 2, 4].length) (baseStart_2156656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2156656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2156656 prefixEnd_2156656 := by exact prefixLift 2156656
  have htrace : WordTrace (prefixWord ++ tailWord_2156656) baseStart_2156656 baseEnd_2156656 := by
    simpa [prefixWord, tailWord_2156656, baseEnd_2156656] using wordTrace_append hprefix tailTrace_2156656
  have hstable : (prefixWord ++ tailWord_2156656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156656).length < 2 ^ (prefixWord ++ tailWord_2156656).sum := by decide
  have hdescent : baseEnd_2156656 < baseStart_2156656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156675 : List Nat := [1, 1, 1, 3, 3, 5, 2, 1, 2, 3]
def baseStart_2156675 : Nat := 118140960795 + 2156675 * 2 ^ 59
def prefixEnd_2156675 : Nat := 4983230072969 + 3 ^ 40 * 2156675 * 2
def baseEnd_2156675 : Nat := 738273927023636488562759

theorem tailTrace_2156675 : CollatzResearch.WordTrace tailWord_2156675 prefixEnd_2156675 738273927023636488562759 := by
  unfold tailWord_2156675
  simp only [CollatzResearch.WordTrace]
  refine ⟨78660399461742280610799479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52440266307828187073866319 78660399461742280610799479)
  ·
    refine ⟨117990599192613420916199219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78660399461742280610799479 117990599192613420916199219)
    ·
      refine ⟨176985898788920131374298829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117990599192613420916199219 176985898788920131374298829)
      ·
        refine ⟨66369712045845049265362061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176985898788920131374298829 66369712045845049265362061)
        ·
          refine ⟨24888642017191893474510773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66369712045845049265362061 24888642017191893474510773)
          ·
            refine ⟨2333310189111740013235385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24888642017191893474510773 2333310189111740013235385)
            ·
              refine ⟨1749982641833805009926539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2333310189111740013235385 1749982641833805009926539)
              ·
                refine ⟨2624973962750707514889809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1749982641833805009926539 2624973962750707514889809)
                ·
                  refine ⟨1968730472063030636167357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2624973962750707514889809 1968730472063030636167357)
                  ·
                    refine ⟨738273927023636488562759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1968730472063030636167357 738273927023636488562759)
                    ·
                      rfl

theorem cell22_2156675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 2, 3].length) (baseStart_2156675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2156675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2156675 prefixEnd_2156675 := by exact prefixLift 2156675
  have htrace : WordTrace (prefixWord ++ tailWord_2156675) baseStart_2156675 baseEnd_2156675 := by
    simpa [prefixWord, tailWord_2156675, baseEnd_2156675] using wordTrace_append hprefix tailTrace_2156675
  have hstable : (prefixWord ++ tailWord_2156675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156675).length < 2 ^ (prefixWord ++ tailWord_2156675).sum := by decide
  have hdescent : baseEnd_2156675 < baseStart_2156675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156746 : List Nat := [3, 1, 2, 1, 3, 1, 1, 3, 3, 4]
def baseStart_2156746 : Nat := 118140960795 + 2156746 * 2 ^ 59
def prefixEnd_2156746 : Nat := 4983230072969 + 3 ^ 40 * 2156746 * 2
def baseEnd_2156746 : Nat := 738298231774615970037541

theorem tailTrace_2156746 : CollatzResearch.WordTrace tailWord_2156746 prefixEnd_2156746 738298231774615970037541 := by
  unfold tailWord_2156746
  simp only [CollatzResearch.WordTrace]
  refine ⟨19665747261121264934158523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52441992696323373157756061 19665747261121264934158523)
  ·
    refine ⟨29498620891681897401237785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19665747261121264934158523 29498620891681897401237785)
    ·
      refine ⟨22123965668761423050928339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29498620891681897401237785 22123965668761423050928339)
      ·
        refine ⟨33185948503142134576392509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22123965668761423050928339 33185948503142134576392509)
        ·
          refine ⟨12444730688678300466147191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33185948503142134576392509 12444730688678300466147191)
          ·
            refine ⟨18667096033017450699220787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12444730688678300466147191 18667096033017450699220787)
            ·
              refine ⟨28000644049526176048831181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18667096033017450699220787 28000644049526176048831181)
              ·
                refine ⟨10500241518572316018311693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28000644049526176048831181 10500241518572316018311693)
                ·
                  refine ⟨3937590569464618506866885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10500241518572316018311693 3937590569464618506866885)
                  ·
                    refine ⟨738298231774615970037541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3937590569464618506866885 738298231774615970037541)
                    ·
                      rfl

theorem cell22_2156746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_2156746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2156746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2156746 prefixEnd_2156746 := by exact prefixLift 2156746
  have htrace : WordTrace (prefixWord ++ tailWord_2156746) baseStart_2156746 baseEnd_2156746 := by
    simpa [prefixWord, tailWord_2156746, baseEnd_2156746] using wordTrace_append hprefix tailTrace_2156746
  have hstable : (prefixWord ++ tailWord_2156746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156746).length < 2 ^ (prefixWord ++ tailWord_2156746).sum := by decide
  have hdescent : baseEnd_2156746 < baseStart_2156746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156778 : List Nat := [3, 1, 3, 1, 1, 2, 1, 6, 4]
def baseStart_2156778 : Nat := 118140960795 + 2156778 * 2 ^ 59
def prefixEnd_2156778 : Nat := 4983230072969 + 3 ^ 40 * 2156778 * 2
def baseEnd_2156778 : Nat := 246103062009526184412481

theorem tailTrace_2156778 : CollatzResearch.WordTrace tailWord_2156778 prefixEnd_2156778 246103062009526184412481 := by
  unfold tailWord_2156778
  simp only [CollatzResearch.WordTrace]
  refine ⟨19666039045092282300449747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52442770786912752801199325 19666039045092282300449747)
  ·
    refine ⟨29499058567638423450674621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19666039045092282300449747 29499058567638423450674621)
    ·
      refine ⟨11062146962864408794002983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29499058567638423450674621 11062146962864408794002983)
      ·
        refine ⟨16593220444296613191004475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11062146962864408794002983 16593220444296613191004475)
        ·
          refine ⟨24889830666444919786506713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16593220444296613191004475 24889830666444919786506713)
          ·
            refine ⟨18667372999833689839880035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24889830666444919786506713 18667372999833689839880035)
            ·
              refine ⟨28001059499750534759820053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18667372999833689839880035 28001059499750534759820053)
              ·
                refine ⟨1312549664050806316866565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28001059499750534759820053 1312549664050806316866565)
                ·
                  refine ⟨246103062009526184412481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1312549664050806316866565 246103062009526184412481)
                  ·
                    rfl

theorem cell22_2156778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 6, 4].length) (baseStart_2156778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2156778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2156778 prefixEnd_2156778 := by exact prefixLift 2156778
  have htrace : WordTrace (prefixWord ++ tailWord_2156778) baseStart_2156778 baseEnd_2156778 := by
    simpa [prefixWord, tailWord_2156778, baseEnd_2156778] using wordTrace_append hprefix tailTrace_2156778
  have hstable : (prefixWord ++ tailWord_2156778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156778).length < 2 ^ (prefixWord ++ tailWord_2156778).sum := by decide
  have hdescent : baseEnd_2156778 < baseStart_2156778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156885 : List Nat := [1, 3, 2, 2, 4, 1, 2, 2, 5]
def baseStart_2156885 : Nat := 118140960795 + 2156885 * 2 ^ 59
def prefixEnd_2156885 : Nat := 4983230072969 + 3 ^ 40 * 2156885 * 2
def baseEnd_2156885 : Nat := 246115271438421980270705

theorem tailTrace_2156885 : CollatzResearch.WordTrace tailWord_2156885 prefixEnd_2156885 246115271438421980270705 := by
  unfold tailWord_2156885
  simp only [CollatzResearch.WordTrace]
  refine ⟨78668058790981486475944109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52445372527320990983962739 78668058790981486475944109)
  ·
    refine ⟨29500522046618057428479041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78668058790981486475944109 29500522046618057428479041)
    ·
      refine ⟨22125391534963543071359281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29500522046618057428479041 22125391534963543071359281)
      ·
        refine ⟨16594043651222657303519461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22125391534963543071359281 16594043651222657303519461)
        ·
          refine ⟨3111383184604248244409899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16594043651222657303519461 3111383184604248244409899)
          ·
            refine ⟨4667074776906372366614849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3111383184604248244409899 4667074776906372366614849)
            ·
              refine ⟨3500306082679779274961137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4667074776906372366614849 3500306082679779274961137)
              ·
                refine ⟨2625229562009834456220853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3500306082679779274961137 2625229562009834456220853)
                ·
                  refine ⟨246115271438421980270705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2625229562009834456220853 246115271438421980270705)
                  ·
                    rfl

theorem cell22_2156885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 5].length) (baseStart_2156885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2156885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2156885 prefixEnd_2156885 := by exact prefixLift 2156885
  have htrace : WordTrace (prefixWord ++ tailWord_2156885) baseStart_2156885 baseEnd_2156885 := by
    simpa [prefixWord, tailWord_2156885, baseEnd_2156885] using wordTrace_append hprefix tailTrace_2156885
  have hstable : (prefixWord ++ tailWord_2156885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156885).length < 2 ^ (prefixWord ++ tailWord_2156885).sum := by decide
  have hdescent : baseEnd_2156885 < baseStart_2156885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156990 : List Nat := [4, 2, 1, 1, 1, 1, 2, 2, 5, 3]
def baseStart_2156990 : Nat := 118140960795 + 2156990 * 2 ^ 59
def prefixEnd_2156990 : Nat := 4983230072969 + 3 ^ 40 * 2156990 * 2
def baseEnd_2156990 : Nat := 738381757961080666936793

theorem tailTrace_2156990 : CollatzResearch.WordTrace tailWord_2156990 prefixEnd_2156990 738381757961080666936793 := by
  unfold tailWord_2156990
  simp only [CollatzResearch.WordTrace]
  refine ⟨9833986056950136176064553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52447925637067392939010949 9833986056950136176064553)
  ·
    refine ⟨7375489542712602132048415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9833986056950136176064553 7375489542712602132048415)
    ·
      refine ⟨11063234314068903198072623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7375489542712602132048415 11063234314068903198072623)
      ·
        refine ⟨16594851471103354797108935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11063234314068903198072623 16594851471103354797108935)
        ·
          refine ⟨24892277206655032195663403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16594851471103354797108935 24892277206655032195663403)
          ·
            refine ⟨37338415809982548293495105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24892277206655032195663403 37338415809982548293495105)
            ·
              refine ⟨28003811857486911220121329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37338415809982548293495105 28003811857486911220121329)
              ·
                refine ⟨21002858893115183415090997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28003811857486911220121329 21002858893115183415090997)
                ·
                  refine ⟨1969018021229548445164781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21002858893115183415090997 1969018021229548445164781)
                  ·
                    refine ⟨738381757961080666936793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1969018021229548445164781 738381757961080666936793)
                    ·
                      rfl

theorem cell22_2156990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_2156990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2156990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2156990 prefixEnd_2156990 := by exact prefixLift 2156990
  have htrace : WordTrace (prefixWord ++ tailWord_2156990) baseStart_2156990 baseEnd_2156990 := by
    simpa [prefixWord, tailWord_2156990, baseEnd_2156990] using wordTrace_append hprefix tailTrace_2156990
  have hstable : (prefixWord ++ tailWord_2156990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156990).length < 2 ^ (prefixWord ++ tailWord_2156990).sum := by decide
  have hdescent : baseEnd_2156990 < baseStart_2156990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157003 : List Nat := [1, 1, 1, 1, 3, 3, 1, 6, 5]
def baseStart_2157003 : Nat := 118140960795 + 2157003 * 2 ^ 59
def prefixEnd_2157003 : Nat := 4983230072969 + 3 ^ 40 * 2157003 * 2
def baseEnd_2157003 : Nat := 246128736042250988787251

theorem tailTrace_2157003 : CollatzResearch.WordTrace tailWord_2157003 prefixEnd_2157003 246128736042250988787251 := by
  unfold tailWord_2157003
  simp only [CollatzResearch.WordTrace]
  refine ⟨78672362604553992628739663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52448241736369328419159775 78672362604553992628739663)
  ·
    refine ⟨118008543906830988943109495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78672362604553992628739663 118008543906830988943109495)
    ·
      refine ⟨177012815860246483414664243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118008543906830988943109495 177012815860246483414664243)
      ·
        refine ⟨265519223790369725121996365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177012815860246483414664243 265519223790369725121996365)
        ·
          refine ⟨99569708921388646920748637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 265519223790369725121996365 99569708921388646920748637)
          ·
            refine ⟨37338640845520742595280739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99569708921388646920748637 37338640845520742595280739)
            ·
              refine ⟨56007961268281113892921109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37338640845520742595280739 56007961268281113892921109)
              ·
                refine ⟨2625373184450677213730677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56007961268281113892921109 2625373184450677213730677)
                ·
                  refine ⟨246128736042250988787251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2625373184450677213730677 246128736042250988787251)
                  ·
                    rfl

theorem cell22_2157003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 5].length) (baseStart_2157003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2157003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2157003 prefixEnd_2157003 := by exact prefixLift 2157003
  have htrace : WordTrace (prefixWord ++ tailWord_2157003) baseStart_2157003 baseEnd_2157003 := by
    simpa [prefixWord, tailWord_2157003, baseEnd_2157003] using wordTrace_append hprefix tailTrace_2157003
  have hstable : (prefixWord ++ tailWord_2157003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157003).length < 2 ^ (prefixWord ++ tailWord_2157003).sum := by decide
  have hdescent : baseEnd_2157003 < baseStart_2157003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157018 : List Nat := [3, 1, 1, 2, 3, 1, 2, 1, 1, 7]
def baseStart_2157018 : Nat := 118140960795 + 2157018 * 2 ^ 59
def prefixEnd_2157018 : Nat := 4983230072969 + 3 ^ 40 * 2157018 * 2
def baseEnd_2157018 : Nat := 738391342933297927236707

theorem tailTrace_2157018 : CollatzResearch.WordTrace tailWord_2157018 prefixEnd_2157018 738391342933297927236707 := by
  unfold tailWord_2157018
  simp only [CollatzResearch.WordTrace]
  refine ⟨19668227424874912547633927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52448606466333100127023805 19668227424874912547633927)
  ·
    refine ⟨29502341137312368821450891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19668227424874912547633927 29502341137312368821450891)
    ·
      refine ⟨44253511705968553232176337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29502341137312368821450891 44253511705968553232176337)
      ·
        refine ⟨33190133779476414924132253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44253511705968553232176337 33190133779476414924132253)
        ·
          refine ⟨12446300167303655596549595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33190133779476414924132253 12446300167303655596549595)
          ·
            refine ⟨18669450250955483394824393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12446300167303655596549595 18669450250955483394824393)
            ·
              refine ⟨14002087688216612546118295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18669450250955483394824393 14002087688216612546118295)
              ·
                refine ⟨21003131532324918819177443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14002087688216612546118295 21003131532324918819177443)
                ·
                  refine ⟨31504697298487378228766165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21003131532324918819177443 31504697298487378228766165)
                  ·
                    refine ⟨738391342933297927236707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31504697298487378228766165 738391342933297927236707)
                    ·
                      rfl

theorem cell22_2157018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_2157018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2157018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2157018 prefixEnd_2157018 := by exact prefixLift 2157018
  have htrace : WordTrace (prefixWord ++ tailWord_2157018) baseStart_2157018 baseEnd_2157018 := by
    simpa [prefixWord, tailWord_2157018, baseEnd_2157018] using wordTrace_append hprefix tailTrace_2157018
  have hstable : (prefixWord ++ tailWord_2157018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157018).length < 2 ^ (prefixWord ++ tailWord_2157018).sum := by decide
  have hdescent : baseEnd_2157018 < baseStart_2157018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157069 : List Nat := [1, 7, 1, 1, 1, 2, 1, 1, 2, 5]
def baseStart_2157069 : Nat := 118140960795 + 2157069 * 2 ^ 59
def prefixEnd_2157069 : Nat := 4983230072969 + 3 ^ 40 * 2157069 * 2
def baseEnd_2157069 : Nat := 738408801275550794211551

theorem tailTrace_2157069 : CollatzResearch.WordTrace tailWord_2157069 prefixEnd_2157069 738408801275550794211551 := by
  unfold tailWord_2157069
  simp only [CollatzResearch.WordTrace]
  refine ⟨78674769822314885900642261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52449846548209923933761507 78674769822314885900642261)
  ·
    refine ⟨1843939917710505138296303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 78674769822314885900642261 1843939917710505138296303)
    ·
      refine ⟨2765909876565757707444455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1843939917710505138296303 2765909876565757707444455)
      ·
        refine ⟨4148864814848636561166683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2765909876565757707444455 4148864814848636561166683)
        ·
          refine ⟨6223297222272954841750025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4148864814848636561166683 6223297222272954841750025)
          ·
            refine ⟨4667472916704716131312519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6223297222272954841750025 4667472916704716131312519)
            ·
              refine ⟨7001209375057074196968779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4667472916704716131312519 7001209375057074196968779)
              ·
                refine ⟨10501814062585611295453169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7001209375057074196968779 10501814062585611295453169)
                ·
                  refine ⟨7876360546939208471589877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10501814062585611295453169 7876360546939208471589877)
                  ·
                    refine ⟨738408801275550794211551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7876360546939208471589877 738408801275550794211551)
                    ·
                      rfl

theorem cell22_2157069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_2157069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2157069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2157069 prefixEnd_2157069 := by exact prefixLift 2157069
  have htrace : WordTrace (prefixWord ++ tailWord_2157069) baseStart_2157069 baseEnd_2157069 := by
    simpa [prefixWord, tailWord_2157069, baseEnd_2157069] using wordTrace_append hprefix tailTrace_2157069
  have hstable : (prefixWord ++ tailWord_2157069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157069).length < 2 ^ (prefixWord ++ tailWord_2157069).sum := by decide
  have hdescent : baseEnd_2157069 < baseStart_2157069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157080 : List Nat := [2, 1, 2, 3, 3, 1, 1, 3, 1, 5]
def baseStart_2157080 : Nat := 118140960795 + 2157080 * 2 ^ 59
def prefixEnd_2157080 : Nat := 4983230072969 + 3 ^ 40 * 2157080 * 2
def baseEnd_2157080 : Nat := 738412566800350432186517

theorem tailTrace_2157080 : CollatzResearch.WordTrace tailWord_2157080 prefixEnd_2157080 738412566800350432186517 := by
  unfold tailWord_2157080
  simp only [CollatzResearch.WordTrace]
  refine ⟨39337585512637517389646347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52450114016850023186195129 39337585512637517389646347)
  ·
    refine ⟨59006378268956276084469521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39337585512637517389646347 59006378268956276084469521)
    ·
      refine ⟨44254783701717207063352141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59006378268956276084469521 44254783701717207063352141)
      ·
        refine ⟨16595543888143952648757053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44254783701717207063352141 16595543888143952648757053)
        ·
          refine ⟨6223328958053982243283895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16595543888143952648757053 6223328958053982243283895)
          ·
            refine ⟨9334993437080973364925843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6223328958053982243283895 9334993437080973364925843)
            ·
              refine ⟨14002490155621460047388765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9334993437080973364925843 14002490155621460047388765)
              ·
                refine ⟨5250933808358047517770787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14002490155621460047388765 5250933808358047517770787)
                ·
                  refine ⟨7876400712537071276656181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5250933808358047517770787 7876400712537071276656181)
                  ·
                    refine ⟨738412566800350432186517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7876400712537071276656181 738412566800350432186517)
                    ·
                      rfl

theorem cell22_2157080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_2157080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2157080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2157080 prefixEnd_2157080 := by exact prefixLift 2157080
  have htrace : WordTrace (prefixWord ++ tailWord_2157080) baseStart_2157080 baseEnd_2157080 := by
    simpa [prefixWord, tailWord_2157080, baseEnd_2157080] using wordTrace_append hprefix tailTrace_2157080
  have hstable : (prefixWord ++ tailWord_2157080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157080).length < 2 ^ (prefixWord ++ tailWord_2157080).sum := by decide
  have hdescent : baseEnd_2157080 < baseStart_2157080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157093 : List Nat := [1, 3, 1, 2, 2, 1, 2, 10]
def baseStart_2157093 : Nat := 118140960795 + 2157093 * 2 ^ 59
def prefixEnd_2157093 : Nat := 4983230072969 + 3 ^ 40 * 2157093 * 2
def baseEnd_2157093 : Nat := 82046335218446970179053

theorem tailTrace_2157093 : CollatzResearch.WordTrace tailWord_2157093 prefixEnd_2157093 82046335218446970179053 := by
  unfold tailWord_2157093
  simp only [CollatzResearch.WordTrace]
  refine ⟨78675645174227937999515933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52450430116151958666343955 78675645174227937999515933)
  ·
    refine ⟨29503366940335476749818475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78675645174227937999515933 29503366940335476749818475)
    ·
      refine ⟨44255050410503215124727713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29503366940335476749818475 44255050410503215124727713)
      ·
        refine ⟨33191287807877411343545785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44255050410503215124727713 33191287807877411343545785)
        ·
          refine ⟨24893465855908058507659339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33191287807877411343545785 24893465855908058507659339)
          ·
            refine ⟨37340198783862087761489009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24893465855908058507659339 37340198783862087761489009)
            ·
              refine ⟨28005149087896565821116757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37340198783862087761489009 28005149087896565821116757)
              ·
                refine ⟨82046335218446970179053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 28005149087896565821116757 82046335218446970179053)
                ·
                  rfl

theorem cell22_2157093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 10].length) (baseStart_2157093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2157093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2157093 prefixEnd_2157093 := by exact prefixLift 2157093
  have htrace : WordTrace (prefixWord ++ tailWord_2157093) baseStart_2157093 baseEnd_2157093 := by
    simpa [prefixWord, tailWord_2157093, baseEnd_2157093] using wordTrace_append hprefix tailTrace_2157093
  have hstable : (prefixWord ++ tailWord_2157093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157093).length < 2 ^ (prefixWord ++ tailWord_2157093).sum := by decide
  have hdescent : baseEnd_2157093 < baseStart_2157093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157114 : List Nat := [3, 1, 1, 1, 3, 5, 1, 2, 2, 3]
def baseStart_2157114 : Nat := 118140960795 + 2157114 * 2 ^ 59
def prefixEnd_2157114 : Nat := 4983230072969 + 3 ^ 40 * 2157114 * 2
def baseEnd_2157114 : Nat := 738424205695185676836413

theorem tailTrace_2157114 : CollatzResearch.WordTrace tailWord_2157114 prefixEnd_2157114 738424205695185676836413 := by
  unfold tailWord_2157114
  simp only [CollatzResearch.WordTrace]
  refine ⟨19669102776787964646507599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52450940738101239057353597 19669102776787964646507599)
  ·
    refine ⟨29503654165181946969761399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19669102776787964646507599 29503654165181946969761399)
    ·
      refine ⟨44255481247772920454642099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29503654165181946969761399 44255481247772920454642099)
      ·
        refine ⟨66383221871659380681963149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44255481247772920454642099 66383221871659380681963149)
        ·
          refine ⟨24893708201872267755736181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66383221871659380681963149 24893708201872267755736181)
          ·
            refine ⟨2333785143925525102100267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24893708201872267755736181 2333785143925525102100267)
            ·
              refine ⟨3500677715888287653150401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2333785143925525102100267 3500677715888287653150401)
              ·
                refine ⟨2625508286916215739862801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3500677715888287653150401 2625508286916215739862801)
                ·
                  refine ⟨1969131215187161804897101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2625508286916215739862801 1969131215187161804897101)
                  ·
                    refine ⟨738424205695185676836413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1969131215187161804897101 738424205695185676836413)
                    ·
                      rfl

theorem cell22_2157114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 2, 3].length) (baseStart_2157114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2157114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2157114 prefixEnd_2157114 := by exact prefixLift 2157114
  have htrace : WordTrace (prefixWord ++ tailWord_2157114) baseStart_2157114 baseEnd_2157114 := by
    simpa [prefixWord, tailWord_2157114, baseEnd_2157114] using wordTrace_append hprefix tailTrace_2157114
  have hstable : (prefixWord ++ tailWord_2157114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157114).length < 2 ^ (prefixWord ++ tailWord_2157114).sum := by decide
  have hdescent : baseEnd_2157114 < baseStart_2157114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157123 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 1, 8]
def baseStart_2157123 : Nat := 118140960795 + 2157123 * 2 ^ 59
def prefixEnd_2157123 : Nat := 4983230072969 + 3 ^ 40 * 2157123 * 2
def baseEnd_2157123 : Nat := 738427286579112653361385

theorem tailTrace_2157123 : CollatzResearch.WordTrace tailWord_2157123 prefixEnd_2157123 738427286579112653361385 := by
  unfold tailWord_2157123
  simp only [CollatzResearch.WordTrace]
  refine ⟨78676739364119253123108023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52451159576079502082072015 78676739364119253123108023)
  ·
    refine ⟨118015109046178879684662035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78676739364119253123108023 118015109046178879684662035)
    ·
      refine ⟨177022663569268319526993053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118015109046178879684662035 177022663569268319526993053)
      ·
        refine ⟨66383498838475619822622395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177022663569268319526993053 66383498838475619822622395)
        ·
          refine ⟨99575248257713429733933593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66383498838475619822622395 99575248257713429733933593)
          ·
            refine ⟨74681436193285072300450195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99575248257713429733933593 74681436193285072300450195)
            ·
              refine ⟨112022154289927608450675293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74681436193285072300450195 112022154289927608450675293)
              ·
                refine ⟨42008307858722853169003235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112022154289927608450675293 42008307858722853169003235)
                ·
                  refine ⟨63012461788084279753504853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42008307858722853169003235 63012461788084279753504853)
                  ·
                    refine ⟨738427286579112653361385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63012461788084279753504853 738427286579112653361385)
                    ·
                      rfl

theorem cell22_2157123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 8].length) (baseStart_2157123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2157123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2157123 prefixEnd_2157123 := by exact prefixLift 2157123
  have htrace : WordTrace (prefixWord ++ tailWord_2157123) baseStart_2157123 baseEnd_2157123 := by
    simpa [prefixWord, tailWord_2157123, baseEnd_2157123] using wordTrace_append hprefix tailTrace_2157123
  have hstable : (prefixWord ++ tailWord_2157123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157123).length < 2 ^ (prefixWord ++ tailWord_2157123).sum := by decide
  have hdescent : baseEnd_2157123 < baseStart_2157123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157150 : List Nat := [4, 4, 1, 2, 1, 2, 1, 3, 4]
def baseStart_2157150 : Nat := 118140960795 + 2157150 * 2 ^ 59
def prefixEnd_2157150 : Nat := 4983230072969 + 3 ^ 40 * 2157150 * 2
def baseEnd_2157150 : Nat := 246145509743631194312101

theorem tailTrace_2157150 : CollatzResearch.WordTrace tailWord_2157150 prefixEnd_2157150 246145509743631194312101 := by
  unfold tailWord_2157150
  simp only [CollatzResearch.WordTrace]
  refine ⟨9834715516877679591792613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52451816090014291156227269 9834715516877679591792613)
  ·
    refine ⟨1844009159414564923461115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9834715516877679591792613 1844009159414564923461115)
    ·
      refine ⟨2766013739121847385191673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1844009159414564923461115 2766013739121847385191673)
      ·
        refine ⟨2074510304341385538893755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2766013739121847385191673 2074510304341385538893755)
        ·
          refine ⟨3111765456512078308340633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2074510304341385538893755 3111765456512078308340633)
          ·
            refine ⟨2333824092384058731255475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3111765456512078308340633 2333824092384058731255475)
            ·
              refine ⟨3500736138576088096883213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2333824092384058731255475 3500736138576088096883213)
              ·
                refine ⟨1312776051966033036331205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3500736138576088096883213 1312776051966033036331205)
                ·
                  refine ⟨246145509743631194312101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1312776051966033036331205 246145509743631194312101)
                  ·
                    rfl

theorem cell22_2157150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_2157150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2157150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2157150 prefixEnd_2157150 := by exact prefixLift 2157150
  have htrace : WordTrace (prefixWord ++ tailWord_2157150) baseStart_2157150 baseEnd_2157150 := by
    simpa [prefixWord, tailWord_2157150, baseEnd_2157150] using wordTrace_append hprefix tailTrace_2157150
  have hstable : (prefixWord ++ tailWord_2157150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157150).length < 2 ^ (prefixWord ++ tailWord_2157150).sum := by decide
  have hdescent : baseEnd_2157150 < baseStart_2157150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157189 : List Nat := [1, 3, 1, 1, 4, 4, 2, 1, 5]
def baseStart_2157189 : Nat := 118140960795 + 2157189 * 2 ^ 59
def prefixEnd_2157189 : Nat := 4983230072969 + 3 ^ 40 * 2157189 * 2
def baseEnd_2157189 : Nat := 246149959909303493737061

theorem tailTrace_2157189 : CollatzResearch.WordTrace tailWord_2157189 prefixEnd_2157189 246149959909303493737061 := by
  unfold tailWord_2157189
  simp only [CollatzResearch.WordTrace]
  refine ⟨78679146581880146395010621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52452764387920097596673747 78679146581880146395010621)
  ·
    refine ⟨29504679968205054898128983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78679146581880146395010621 29504679968205054898128983)
    ·
      refine ⟨44257019952307582347193475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29504679968205054898128983 44257019952307582347193475)
      ·
        refine ⟨66385529928461373520790213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44257019952307582347193475 66385529928461373520790213)
        ·
          refine ⟨12447286861586507535148165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66385529928461373520790213 12447286861586507535148165)
          ·
            refine ⟨2333866286547470162840281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12447286861586507535148165 2333866286547470162840281)
            ·
              refine ⟨1750399714910602622130211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2333866286547470162840281 1750399714910602622130211)
              ·
                refine ⟨2625599572365903933195317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1750399714910602622130211 2625599572365903933195317)
                ·
                  refine ⟨246149959909303493737061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2625599572365903933195317 246149959909303493737061)
                  ·
                    rfl

theorem cell22_2157189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 5].length) (baseStart_2157189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2157189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2157189 prefixEnd_2157189 := by exact prefixLift 2157189
  have htrace : WordTrace (prefixWord ++ tailWord_2157189) baseStart_2157189 baseEnd_2157189 := by
    simpa [prefixWord, tailWord_2157189, baseEnd_2157189] using wordTrace_append hprefix tailTrace_2157189
  have hstable : (prefixWord ++ tailWord_2157189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157189).length < 2 ^ (prefixWord ++ tailWord_2157189).sum := by decide
  have hdescent : baseEnd_2157189 < baseStart_2157189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157294 : List Nat := [4, 1, 2, 1, 1, 3, 1, 3, 3, 3]
def baseStart_2157294 : Nat := 118140960795 + 2157294 * 2 ^ 59
def prefixEnd_2157294 : Nat := 4983230072969 + 3 ^ 40 * 2157294 * 2
def baseEnd_2157294 : Nat := 738485823373725207335861

theorem tailTrace_2157294 : CollatzResearch.WordTrace tailWord_2157294 prefixEnd_2157294 738485823373725207335861 := by
  unfold tailWord_2157294
  simp only [CollatzResearch.WordTrace]
  refine ⟨9835372030812468665947867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52455317497666499551721957 9835372030812468665947867)
  ·
    refine ⟨14753058046218702998921801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9835372030812468665947867 14753058046218702998921801)
    ·
      refine ⟨11064793534664027249191351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14753058046218702998921801 11064793534664027249191351)
      ·
        refine ⟨16597190301996040873787027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11064793534664027249191351 16597190301996040873787027)
        ·
          refine ⟨24895785452994061310680541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16597190301996040873787027 24895785452994061310680541)
          ·
            refine ⟨9335919544872772991505203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24895785452994061310680541 9335919544872772991505203)
            ·
              refine ⟨14003879317309159487257805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9335919544872772991505203 14003879317309159487257805)
              ·
                refine ⟨5251454743990934807721677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14003879317309159487257805 5251454743990934807721677)
                ·
                  refine ⟨1969295528996600552895629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5251454743990934807721677 1969295528996600552895629)
                  ·
                    refine ⟨738485823373725207335861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1969295528996600552895629 738485823373725207335861)
                    ·
                      rfl

theorem cell22_2157294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_2157294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2157294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2157294 prefixEnd_2157294 := by exact prefixLift 2157294
  have htrace : WordTrace (prefixWord ++ tailWord_2157294) baseStart_2157294 baseEnd_2157294 := by
    simpa [prefixWord, tailWord_2157294, baseEnd_2157294] using wordTrace_append hprefix tailTrace_2157294
  have hstable : (prefixWord ++ tailWord_2157294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157294).length < 2 ^ (prefixWord ++ tailWord_2157294).sum := by decide
  have hdescent : baseEnd_2157294 < baseStart_2157294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157300 : List Nat := [2, 6, 1, 1, 3, 1, 1, 1, 1, 5]
def baseStart_2157300 : Nat := 118140960795 + 2157300 * 2 ^ 59
def prefixEnd_2157300 : Nat := 4983230072969 + 3 ^ 40 * 2157300 * 2
def baseEnd_2157300 : Nat := 738487877296343191685843

theorem tailTrace_2157300 : CollatzResearch.WordTrace tailWord_2157300 prefixEnd_2157300 738487877296343191685843 := by
  unfold tailWord_2157300
  simp only [CollatzResearch.WordTrace]
  refine ⟨39341597542239006176150677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52455463389652008234867569 39341597542239006176150677)
  ·
    refine ⟨1844137384792453414507063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 39341597542239006176150677 1844137384792453414507063)
    ·
      refine ⟨2766206077188680121760595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1844137384792453414507063 2766206077188680121760595)
      ·
        refine ⟨4149309115783020182640893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2766206077188680121760595 4149309115783020182640893)
        ·
          refine ⟨1555990918418632568490335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4149309115783020182640893 1555990918418632568490335)
          ·
            refine ⟨2333986377627948852735503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1555990918418632568490335 2333986377627948852735503)
            ·
              refine ⟨3500979566441923279103255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2333986377627948852735503 3500979566441923279103255)
              ·
                refine ⟨5251469349662884918654883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3500979566441923279103255 5251469349662884918654883)
                ·
                  refine ⟨7877204024494327377982325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5251469349662884918654883 7877204024494327377982325)
                  ·
                    refine ⟨738487877296343191685843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7877204024494327377982325 738487877296343191685843)
                    ·
                      rfl

theorem cell22_2157300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_2157300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2157300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2157300 prefixEnd_2157300 := by exact prefixLift 2157300
  have htrace : WordTrace (prefixWord ++ tailWord_2157300) baseStart_2157300 baseEnd_2157300 := by
    simpa [prefixWord, tailWord_2157300, baseEnd_2157300] using wordTrace_append hprefix tailTrace_2157300
  have hstable : (prefixWord ++ tailWord_2157300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157300).length < 2 ^ (prefixWord ++ tailWord_2157300).sum := by decide
  have hdescent : baseEnd_2157300 < baseStart_2157300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157358 : List Nat := [4, 1, 3, 2, 1, 3, 2, 1, 5]
def baseStart_2157358 : Nat := 118140960795 + 2157358 * 2 ^ 59
def prefixEnd_2157358 : Nat := 4983230072969 + 3 ^ 40 * 2157358 * 2
def baseEnd_2157358 : Nat := 246169243960550124578555

theorem tailTrace_2157358 : CollatzResearch.WordTrace tailWord_2157358 prefixEnd_2157358 246169243960550124578555 := by
  unfold tailWord_2157358
  simp only [CollatzResearch.WordTrace]
  refine ⟨9835663814783486032239091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52456873678845258838608485 9835663814783486032239091)
  ·
    refine ⟨14753495722175229048358637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9835663814783486032239091 14753495722175229048358637)
    ·
      refine ⟨5532560895815710893134489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14753495722175229048358637 5532560895815710893134489)
      ·
        refine ⟨4149420671861783169850867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5532560895815710893134489 4149420671861783169850867)
        ·
          refine ⟨6224131007792674754776301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4149420671861783169850867 6224131007792674754776301)
          ·
            refine ⟨2334049127922253033041113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6224131007792674754776301 2334049127922253033041113)
            ·
              refine ⟨1750536845941689774780835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2334049127922253033041113 1750536845941689774780835)
              ·
                refine ⟨2625805268912534662171253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1750536845941689774780835 2625805268912534662171253)
                ·
                  refine ⟨246169243960550124578555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2625805268912534662171253 246169243960550124578555)
                  ·
                    rfl

theorem cell22_2157358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_2157358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2157358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2157358 prefixEnd_2157358 := by exact prefixLift 2157358
  have htrace : WordTrace (prefixWord ++ tailWord_2157358) baseStart_2157358 baseEnd_2157358 := by
    simpa [prefixWord, tailWord_2157358, baseEnd_2157358] using wordTrace_append hprefix tailTrace_2157358
  have hstable : (prefixWord ++ tailWord_2157358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157358).length < 2 ^ (prefixWord ++ tailWord_2157358).sum := by decide
  have hdescent : baseEnd_2157358 < baseStart_2157358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157367 : List Nat := [1, 1, 3, 1, 2, 1, 4, 3, 1, 5]
def baseStart_2157367 : Nat := 118140960795 + 2157367 * 2 ^ 59
def prefixEnd_2157367 : Nat := 4983230072969 + 3 ^ 40 * 2157367 * 2
def baseEnd_2157367 : Nat := 738510812765577350260637

theorem tailTrace_2157367 : CollatzResearch.WordTrace tailWord_2157367 prefixEnd_2157367 738510812765577350260637 := by
  unfold tailWord_2157367
  simp only [CollatzResearch.WordTrace]
  refine ⟨78685638775235282794990355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52457092516823521863326903 78685638775235282794990355)
  ·
    refine ⟨118028458162852924192485533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78685638775235282794990355 118028458162852924192485533)
    ·
      refine ⟨44260671811069846572182075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118028458162852924192485533 44260671811069846572182075)
      ·
        refine ⟨66391007716604769858273113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44260671811069846572182075 66391007716604769858273113)
        ·
          refine ⟨49793255787453577393704835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66391007716604769858273113 49793255787453577393704835)
          ·
            refine ⟨74689883681180366090557253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49793255787453577393704835 74689883681180366090557253)
            ·
              refine ⟨14004353190221318641979485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74689883681180366090557253 14004353190221318641979485)
              ·
                refine ⟨5251632446332994490742307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14004353190221318641979485 5251632446332994490742307)
                ·
                  refine ⟨7877448669499491736113461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5251632446332994490742307 7877448669499491736113461)
                  ·
                    refine ⟨738510812765577350260637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7877448669499491736113461 738510812765577350260637)
                    ·
                      rfl

theorem cell22_2157367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_2157367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2157367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2157367 prefixEnd_2157367 := by exact prefixLift 2157367
  have htrace : WordTrace (prefixWord ++ tailWord_2157367) baseStart_2157367 baseEnd_2157367 := by
    simpa [prefixWord, tailWord_2157367, baseEnd_2157367] using wordTrace_append hprefix tailTrace_2157367
  have hstable : (prefixWord ++ tailWord_2157367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157367).length < 2 ^ (prefixWord ++ tailWord_2157367).sum := by decide
  have hdescent : baseEnd_2157367 < baseStart_2157367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157399 : List Nat := [1, 1, 3, 2, 4, 1, 2, 2, 2, 4]
def baseStart_2157399 : Nat := 118140960795 + 2157399 * 2 ^ 59
def prefixEnd_2157399 : Nat := 4983230072969 + 3 ^ 40 * 2157399 * 2
def baseEnd_2157399 : Nat := 738521767019539933460539

theorem tailTrace_2157399 : CollatzResearch.WordTrace tailWord_2157399 prefixEnd_2157399 738521767019539933460539 := by
  unfold tailWord_2157399
  simp only [CollatzResearch.WordTrace]
  refine ⟨78686805911119352260155251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52457870607412901506770167 78686805911119352260155251)
  ·
    refine ⟨118030208866679028390232877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78686805911119352260155251 118030208866679028390232877)
    ·
      refine ⟨44261328325004635646337329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118030208866679028390232877 44261328325004635646337329)
      ·
        refine ⟨33195996243753476734752997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44261328325004635646337329 33195996243753476734752997)
        ·
          refine ⟨6224249295703776887766187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33195996243753476734752997 6224249295703776887766187)
          ·
            refine ⟨9336373943555665331649281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6224249295703776887766187 9336373943555665331649281)
            ·
              refine ⟨7002280457666748998736961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9336373943555665331649281 7002280457666748998736961)
              ·
                refine ⟨5251710343250061749052721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7002280457666748998736961 5251710343250061749052721)
                ·
                  refine ⟨3938782757437546311789541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5251710343250061749052721 3938782757437546311789541)
                  ·
                    refine ⟨738521767019539933460539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3938782757437546311789541 738521767019539933460539)
                    ·
                      rfl

theorem cell22_2157399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_2157399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2157399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2157399 prefixEnd_2157399 := by exact prefixLift 2157399
  have htrace : WordTrace (prefixWord ++ tailWord_2157399) baseStart_2157399 baseEnd_2157399 := by
    simpa [prefixWord, tailWord_2157399, baseEnd_2157399] using wordTrace_append hprefix tailTrace_2157399
  have hstable : (prefixWord ++ tailWord_2157399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157399).length < 2 ^ (prefixWord ++ tailWord_2157399).sum := by decide
  have hdescent : baseEnd_2157399 < baseStart_2157399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157401 : List Nat := [1, 2, 1, 2, 2, 5, 2, 2, 2, 3]
def baseStart_2157401 : Nat := 118140960795 + 2157401 * 2 ^ 59
def prefixEnd_2157401 : Nat := 4983230072969 + 3 ^ 40 * 2157401 * 2
def baseEnd_2157401 : Nat := 738522451660412594910533

theorem tailTrace_2157401 : CollatzResearch.WordTrace tailWord_2157401 prefixEnd_2157401 738522451660412594910533 := by
  unfold tailWord_2157401
  simp only [CollatzResearch.WordTrace]
  refine ⟨78686878857112106601728057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52457919238074737734485371 78686878857112106601728057)
  ·
    refine ⟨59015159142834079951296043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78686878857112106601728057 59015159142834079951296043)
    ·
      refine ⟨88522738714251119926944065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59015159142834079951296043 88522738714251119926944065)
      ·
        refine ⟨66392054035688339945208049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88522738714251119926944065 66392054035688339945208049)
        ·
          refine ⟨49794040526766254958906037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66392054035688339945208049 49794040526766254958906037)
          ·
            refine ⟨4668191299384336402397441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49794040526766254958906037 4668191299384336402397441)
            ·
              refine ⟨3501143474538252301798081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4668191299384336402397441 3501143474538252301798081)
              ·
                refine ⟨2625857605903689226348561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3501143474538252301798081 2625857605903689226348561)
                ·
                  refine ⟨1969393204427766919761421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2625857605903689226348561 1969393204427766919761421)
                  ·
                    refine ⟨738522451660412594910533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1969393204427766919761421 738522451660412594910533)
                    ·
                      rfl

theorem cell22_2157401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 2, 3].length) (baseStart_2157401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2157401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2157401 prefixEnd_2157401 := by exact prefixLift 2157401
  have htrace : WordTrace (prefixWord ++ tailWord_2157401) baseStart_2157401 baseEnd_2157401 := by
    simpa [prefixWord, tailWord_2157401, baseEnd_2157401] using wordTrace_append hprefix tailTrace_2157401
  have hstable : (prefixWord ++ tailWord_2157401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157401).length < 2 ^ (prefixWord ++ tailWord_2157401).sum := by decide
  have hdescent : baseEnd_2157401 < baseStart_2157401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157476 : List Nat := [2, 3, 1, 2, 1, 2, 5, 1, 5]
def baseStart_2157476 : Nat := 118140960795 + 2157476 * 2 ^ 59
def prefixEnd_2157476 : Nat := 4983230072969 + 3 ^ 40 * 2157476 * 2
def baseEnd_2157476 : Nat := 246182708564379133095101

theorem tailTrace_2157476 : CollatzResearch.WordTrace tailWord_2157476 prefixEnd_2157476 246182708564379133095101 := by
  unfold tailWord_2157476
  simp only [CollatzResearch.WordTrace]
  refine ⟨39344807165920197205354141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52459742887893596273805521 39344807165920197205354141)
  ·
    refine ⟨14754302687220073952007803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39344807165920197205354141 14754302687220073952007803)
    ·
      refine ⟨22131454030830110928011705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14754302687220073952007803 22131454030830110928011705)
      ·
        refine ⟨16598590523122583196008779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22131454030830110928011705 16598590523122583196008779)
        ·
          refine ⟨24897885784683874794013169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16598590523122583196008779 24897885784683874794013169)
          ·
            refine ⟨18673414338512906095509877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24897885784683874794013169 18673414338512906095509877)
            ·
              refine ⟨1750632594235584946454051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18673414338512906095509877 1750632594235584946454051)
              ·
                refine ⟨2625948891353377419681077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1750632594235584946454051 2625948891353377419681077)
                ·
                  refine ⟨246182708564379133095101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2625948891353377419681077 246182708564379133095101)
                  ·
                    rfl

theorem cell22_2157476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_2157476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2157476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2157476 prefixEnd_2157476 := by exact prefixLift 2157476
  have htrace : WordTrace (prefixWord ++ tailWord_2157476) baseStart_2157476 baseEnd_2157476 := by
    simpa [prefixWord, tailWord_2157476, baseEnd_2157476] using wordTrace_append hprefix tailTrace_2157476
  have hstable : (prefixWord ++ tailWord_2157476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157476).length < 2 ^ (prefixWord ++ tailWord_2157476).sum := by decide
  have hdescent : baseEnd_2157476 < baseStart_2157476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157487 : List Nat := [1, 1, 2, 1, 2, 2, 2, 3, 8]
def baseStart_2157487 : Nat := 118140960795 + 2157487 * 2 ^ 59
def prefixEnd_2157487 : Nat := 4983230072969 + 3 ^ 40 * 2157487 * 2
def baseEnd_2157487 : Nat := 246183963739312345753423

theorem tailTrace_2157487 : CollatzResearch.WordTrace tailWord_2157487 prefixEnd_2157487 246183963739312345753423 := by
  unfold tailWord_2157487
  simp only [CollatzResearch.WordTrace]
  refine ⟨78690015534800543289358715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52460010356533695526239143 78690015534800543289358715)
  ·
    refine ⟨118035023302200814934038073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78690015534800543289358715 118035023302200814934038073)
    ·
      refine ⟨88526267476650611200528555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118035023302200814934038073 88526267476650611200528555)
      ·
        refine ⟨132789401214975916800792833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88526267476650611200528555 132789401214975916800792833)
        ·
          refine ⟨99592050911231937600594625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132789401214975916800792833 99592050911231937600594625)
          ·
            refine ⟨74694038183423953200445969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99592050911231937600594625 74694038183423953200445969)
            ·
              refine ⟨56020528637567964900334477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74694038183423953200445969 56020528637567964900334477)
              ·
                refine ⟨21007698239087986837625429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56020528637567964900334477 21007698239087986837625429)
                ·
                  refine ⟨246183963739312345753423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21007698239087986837625429 246183963739312345753423)
                  ·
                    rfl

theorem cell22_2157487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 8].length) (baseStart_2157487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2157487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2157487 prefixEnd_2157487 := by exact prefixLift 2157487
  have htrace : WordTrace (prefixWord ++ tailWord_2157487) baseStart_2157487 baseEnd_2157487 := by
    simpa [prefixWord, tailWord_2157487, baseEnd_2157487] using wordTrace_append hprefix tailTrace_2157487
  have hstable : (prefixWord ++ tailWord_2157487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157487).length < 2 ^ (prefixWord ++ tailWord_2157487).sum := by decide
  have hdescent : baseEnd_2157487 < baseStart_2157487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157551 : List Nat := [1, 1, 2, 1, 4, 4, 2, 1, 2, 4]
def baseStart_2157551 : Nat := 118140960795 + 2157551 * 2 ^ 59
def prefixEnd_2157551 : Nat := 4983230072969 + 3 ^ 40 * 2157551 * 2
def baseEnd_2157551 : Nat := 738573799725862203660073

theorem tailTrace_2157551 : CollatzResearch.WordTrace tailWord_2157551 prefixEnd_2157551 738573799725862203660073 := by
  unfold tailWord_2157551
  simp only [CollatzResearch.WordTrace]
  refine ⟨78692349806568682219688507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52461566537712454813125671 78692349806568682219688507)
  ·
    refine ⟨118038524709853023329532761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78692349806568682219688507 118038524709853023329532761)
    ·
      refine ⟨88528893532389767497149571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118038524709853023329532761 88528893532389767497149571)
      ·
        refine ⟨132793340298584651245724357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88528893532389767497149571 132793340298584651245724357)
        ·
          refine ⟨24898751305984622108573317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132793340298584651245724357 24898751305984622108573317)
          ·
            refine ⟨4668515869872116645357497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24898751305984622108573317 4668515869872116645357497)
            ·
              refine ⟨3501386902404087484018123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4668515869872116645357497 3501386902404087484018123)
              ·
                refine ⟨5252080353606131226027185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3501386902404087484018123 5252080353606131226027185)
                ·
                  refine ⟨3939060265204598419520389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5252080353606131226027185 3939060265204598419520389)
                  ·
                    refine ⟨738573799725862203660073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3939060265204598419520389 738573799725862203660073)
                    ·
                      rfl

theorem cell22_2157551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 4].length) (baseStart_2157551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2157551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2157551 prefixEnd_2157551 := by exact prefixLift 2157551
  have htrace : WordTrace (prefixWord ++ tailWord_2157551) baseStart_2157551 baseEnd_2157551 := by
    simpa [prefixWord, tailWord_2157551, baseEnd_2157551] using wordTrace_append hprefix tailTrace_2157551
  have hstable : (prefixWord ++ tailWord_2157551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157551).length < 2 ^ (prefixWord ++ tailWord_2157551).sum := by decide
  have hdescent : baseEnd_2157551 < baseStart_2157551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157557 : List Nat := [1, 3, 5, 2, 1, 1, 3, 1, 1, 4]
def baseStart_2157557 : Nat := 118140960795 + 2157557 * 2 ^ 59
def prefixEnd_2157557 : Nat := 4983230072969 + 3 ^ 40 * 2157557 * 2
def baseEnd_2157557 : Nat := 738575853648480188010055

theorem tailTrace_2157557 : CollatzResearch.WordTrace tailWord_2157557 prefixEnd_2157557 738575853648480188010055 := by
  unfold tailWord_2157557
  simp only [CollatzResearch.WordTrace]
  refine ⟨78692568644546945244406925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52461712429697963496271283 78692568644546945244406925)
  ·
    refine ⟨29509713241705104466652597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78692568644546945244406925 29509713241705104466652597)
    ·
      refine ⟨2766535616409853543748681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29509713241705104466652597 2766535616409853543748681)
      ·
        refine ⟨2074901712307390157811511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2766535616409853543748681 2074901712307390157811511)
        ·
          refine ⟨3112352568461085236717267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2074901712307390157811511 3112352568461085236717267)
          ·
            refine ⟨4668528852691627855075901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3112352568461085236717267 4668528852691627855075901)
            ·
              refine ⟨1750698319759360445653463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4668528852691627855075901 1750698319759360445653463)
              ·
                refine ⟨2626047479639040668480195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1750698319759360445653463 2626047479639040668480195)
                ·
                  refine ⟨3939071219458561002720293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2626047479639040668480195 3939071219458561002720293)
                  ·
                    refine ⟨738575853648480188010055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3939071219458561002720293 738575853648480188010055)
                    ·
                      rfl

theorem cell22_2157557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_2157557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2157557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2157557 prefixEnd_2157557 := by exact prefixLift 2157557
  have htrace : WordTrace (prefixWord ++ tailWord_2157557) baseStart_2157557 baseEnd_2157557 := by
    simpa [prefixWord, tailWord_2157557, baseEnd_2157557] using wordTrace_append hprefix tailTrace_2157557
  have hstable : (prefixWord ++ tailWord_2157557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157557).length < 2 ^ (prefixWord ++ tailWord_2157557).sum := by decide
  have hdescent : baseEnd_2157557 < baseStart_2157557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157566 : List Nat := [4, 2, 2, 2, 2, 10]
def baseStart_2157566 : Nat := 118140960795 + 2157566 * 2 ^ 59
def prefixEnd_2157566 : Nat := 4983230072969 + 3 ^ 40 * 2157566 * 2
def baseEnd_2157566 : Nat := 9118258451017372401667

theorem tailTrace_2157566 : CollatzResearch.WordTrace tailWord_2157566 prefixEnd_2157566 9118258451017372401667 := by
  unfold tailWord_2157566
  simp only [CollatzResearch.WordTrace]
  refine ⟨9836612112689292472685569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52461931267676226520989701 9836612112689292472685569)
  ·
    refine ⟨7377459084516969354514177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9836612112689292472685569 7377459084516969354514177)
    ·
      refine ⟨5533094313387727015885633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7377459084516969354514177 5533094313387727015885633)
      ·
        refine ⟨4149820735040795261914225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5533094313387727015885633 4149820735040795261914225)
        ·
          refine ⟨3112365551280596446435669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4149820735040795261914225 3112365551280596446435669)
          ·
            refine ⟨9118258451017372401667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3112365551280596446435669 9118258451017372401667)
            ·
              rfl

theorem cell22_2157566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 10].length) (baseStart_2157566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2157566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2157566 prefixEnd_2157566 := by exact prefixLift 2157566
  have htrace : WordTrace (prefixWord ++ tailWord_2157566) baseStart_2157566 baseEnd_2157566 := by
    simpa [prefixWord, tailWord_2157566, baseEnd_2157566] using wordTrace_append hprefix tailTrace_2157566
  have hstable : (prefixWord ++ tailWord_2157566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157566).length < 2 ^ (prefixWord ++ tailWord_2157566).sum := by decide
  have hdescent : baseEnd_2157566 < baseStart_2157566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
