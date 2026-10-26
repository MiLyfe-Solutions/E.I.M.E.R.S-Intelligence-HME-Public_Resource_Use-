import V185TrunkScan23Chunk0749

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4435644 : List Nat := [2, 2, 2, 3, 1, 3, 2, 3, 1, 1, 3]
def baseStart_4435644 : Nat := 118140960795 + 4435644 * 2 ^ 59
def prefixEnd_4435644 : Nat := 4983230072969 + 3 ^ 40 * 4435644 * 2
def baseEnd_4435644 : Nat := 2277617384231748756150851

theorem tailTrace_4435644 : CollatzResearch.WordTrace tailWord_4435644 prefixEnd_4435644 2277617384231748756150851 := by
  unfold tailWord_4435644
  simp only [CollatzResearch.WordTrace]
  refine ⟨80890613771213405264428993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107854151694951207019238657 80890613771213405264428993)
  ·
    refine ⟨60667960328410053948321745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80890613771213405264428993 60667960328410053948321745)
    ·
      refine ⟨45500970246307540461241309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60667960328410053948321745 45500970246307540461241309)
      ·
        refine ⟨17062863842365327672965491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45500970246307540461241309 17062863842365327672965491)
        ·
          refine ⟨25594295763547991509448237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17062863842365327672965491 25594295763547991509448237)
          ·
            refine ⟨9597860911330496816043089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25594295763547991509448237 9597860911330496816043089)
            ·
              refine ⟨7198395683497872612032317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9597860911330496816043089 7198395683497872612032317)
              ·
                refine ⟨2699398381311702229512119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7198395683497872612032317 2699398381311702229512119)
                ·
                  refine ⟨4049097571967553344268179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2699398381311702229512119 4049097571967553344268179)
                  ·
                    refine ⟨6073646357951330016402269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4049097571967553344268179 6073646357951330016402269)
                    ·
                      refine ⟨2277617384231748756150851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6073646357951330016402269 2277617384231748756150851)
                      ·
                        rfl

theorem cell23_4435644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_4435644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4435644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4435644 prefixEnd_4435644 := by exact prefixLift 4435644
  have htrace : WordTrace (prefixWord ++ tailWord_4435644) baseStart_4435644 baseEnd_4435644 := by
    simpa [prefixWord, tailWord_4435644, baseEnd_4435644] using wordTrace_append hprefix tailTrace_4435644
  have hstable : (prefixWord ++ tailWord_4435644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4435644).length < 2 ^ (prefixWord ++ tailWord_4435644).sum := by decide
  have hdescent : baseEnd_4435644 < baseStart_4435644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4435644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4435656 : List Nat := [2, 1, 3, 1, 2, 2, 12]
def baseStart_4435656 : Nat := 118140960795 + 4435656 * 2 ^ 59
def prefixEnd_4435656 : Nat := 4983230072969 + 3 ^ 40 * 4435656 * 2
def baseEnd_4435656 : Nat := 28118809209871638385195

theorem tailTrace_4435656 : CollatzResearch.WordTrace tailWord_4435656 prefixEnd_4435656 28118809209871638385195 := by
  unfold tailWord_4435656
  simp only [CollatzResearch.WordTrace]
  refine ⟨80890832609191668289147411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107854443478922224385529881 80890832609191668289147411)
  ·
    refine ⟨121336248913787502433721117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80890832609191668289147411 121336248913787502433721117)
    ·
      refine ⟨45501093342670313412645419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121336248913787502433721117 45501093342670313412645419)
      ·
        refine ⟨68251640014005470118968129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45501093342670313412645419 68251640014005470118968129)
        ·
          refine ⟨51188730010504102589226097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68251640014005470118968129 51188730010504102589226097)
          ·
            refine ⟨38391547507878076941919573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51188730010504102589226097 38391547507878076941919573)
            ·
              refine ⟨28118809209871638385195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 38391547507878076941919573 28118809209871638385195)
              ·
                rfl

theorem cell23_4435656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 12].length) (baseStart_4435656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4435656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4435656 prefixEnd_4435656 := by exact prefixLift 4435656
  have htrace : WordTrace (prefixWord ++ tailWord_4435656) baseStart_4435656 baseEnd_4435656 := by
    simpa [prefixWord, tailWord_4435656, baseEnd_4435656] using wordTrace_append hprefix tailTrace_4435656
  have hstable : (prefixWord ++ tailWord_4435656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4435656).length < 2 ^ (prefixWord ++ tailWord_4435656).sum := by decide
  have hdescent : baseEnd_4435656 < baseStart_4435656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4435656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4435661 : List Nat := [1, 6, 2, 1, 1, 1, 2, 4, 1, 1, 3]
def baseStart_4435661 : Nat := 118140960795 + 4435661 * 2 ^ 59
def prefixEnd_4435661 : Nat := 4983230072969 + 3 ^ 40 * 4435661 * 2
def baseEnd_4435661 : Nat := 2277626113402875189638273

theorem tailTrace_4435661 : CollatzResearch.WordTrace tailWord_4435661 prefixEnd_4435661 2277626113402875189638273 := by
  unfold tailWord_4435661
  simp only [CollatzResearch.WordTrace]
  refine ⟨161781847583365222432226837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107854565055576814954817891 161781847583365222432226837)
  ·
    refine ⟨7583524105470244801510633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 161781847583365222432226837 7583524105470244801510633)
    ·
      refine ⟨5687643079102683601132975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7583524105470244801510633 5687643079102683601132975)
      ·
        refine ⟨8531464618654025401699463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5687643079102683601132975 8531464618654025401699463)
        ·
          refine ⟨12797196927981038102549195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8531464618654025401699463 12797196927981038102549195)
          ·
            refine ⟨19195795391971557153823793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12797196927981038102549195 19195795391971557153823793)
            ·
              refine ⟨14396846543978667865367845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19195795391971557153823793 14396846543978667865367845)
              ·
                refine ⟨2699408726996000224756471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14396846543978667865367845 2699408726996000224756471)
                ·
                  refine ⟨4049113090494000337134707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2699408726996000224756471 4049113090494000337134707)
                  ·
                    refine ⟨6073669635741000505702061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4049113090494000337134707 6073669635741000505702061)
                    ·
                      refine ⟨2277626113402875189638273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6073669635741000505702061 2277626113402875189638273)
                      ·
                        rfl

theorem cell23_4435661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_4435661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4435661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4435661 prefixEnd_4435661 := by exact prefixLift 4435661
  have htrace : WordTrace (prefixWord ++ tailWord_4435661) baseStart_4435661 baseEnd_4435661 := by
    simpa [prefixWord, tailWord_4435661, baseEnd_4435661] using wordTrace_append hprefix tailTrace_4435661
  have hstable : (prefixWord ++ tailWord_4435661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4435661).length < 2 ^ (prefixWord ++ tailWord_4435661).sum := by decide
  have hdescent : baseEnd_4435661 < baseStart_4435661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4435661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4435743 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 5]
def baseStart_4435743 : Nat := 118140960795 + 4435743 * 2 ^ 59
def prefixEnd_4435743 : Nat := 4983230072969 + 3 ^ 40 * 4435743 * 2
def baseEnd_4435743 : Nat := 2277668218816543868812895

theorem tailTrace_4435743 : CollatzResearch.WordTrace tailWord_4435743 prefixEnd_4435743 2277668218816543868812895 := by
  unfold tailWord_4435743
  simp only [CollatzResearch.WordTrace]
  refine ⟨161784838369068150436711883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107856558912712100291141255 161784838369068150436711883)
  ·
    refine ⟨242677257553602225655067825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161784838369068150436711883 242677257553602225655067825)
    ·
      refine ⟨182007943165201669241300869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242677257553602225655067825 182007943165201669241300869)
      ·
        refine ⟨34126489343475312982743913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 182007943165201669241300869 34126489343475312982743913)
        ·
          refine ⟨25594867007606484737057935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34126489343475312982743913 25594867007606484737057935)
          ·
            refine ⟨38392300511409727105586903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25594867007606484737057935 38392300511409727105586903)
            ·
              refine ⟨57588450767114590658380355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38392300511409727105586903 57588450767114590658380355)
              ·
                refine ⟨86382676150671885987570533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57588450767114590658380355 86382676150671885987570533)
                ·
                  refine ⟨16196751778250978622669475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86382676150671885987570533 16196751778250978622669475)
                  ·
                    refine ⟨24295127667376467934004213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16196751778250978622669475 24295127667376467934004213)
                    ·
                      refine ⟨2277668218816543868812895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24295127667376467934004213 2277668218816543868812895)
                      ·
                        rfl

theorem cell23_4435743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_4435743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4435743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4435743 prefixEnd_4435743 := by exact prefixLift 4435743
  have htrace : WordTrace (prefixWord ++ tailWord_4435743) baseStart_4435743 baseEnd_4435743 := by
    simpa [prefixWord, tailWord_4435743, baseEnd_4435743] using wordTrace_append hprefix tailTrace_4435743
  have hstable : (prefixWord ++ tailWord_4435743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4435743).length < 2 ^ (prefixWord ++ tailWord_4435743).sum := by decide
  have hdescent : baseEnd_4435743 < baseStart_4435743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4435743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4435937 : List Nat := [1, 2, 3, 1, 2, 1, 2, 5, 1, 1, 4]
def baseStart_4435937 : Nat := 118140960795 + 4435937 * 2 ^ 59
def prefixEnd_4435937 : Nat := 4983230072969 + 3 ^ 40 * 4435937 * 2
def baseEnd_4435937 : Nat := 2277767834063516109787003

theorem tailTrace_4435937 : CollatzResearch.WordTrace tailWord_4435937 prefixEnd_4435937 2277767834063516109787003 := by
  unfold tailWord_4435937
  simp only [CollatzResearch.WordTrace]
  refine ⟨161791914130365321569274065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107861276086910214379516043 161791914130365321569274065)
  ·
    refine ⟨121343935597773991176955549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161791914130365321569274065 121343935597773991176955549)
    ·
      refine ⟨45503975849165246691358331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121343935597773991176955549 45503975849165246691358331)
      ·
        refine ⟨68255963773747870037037497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45503975849165246691358331 68255963773747870037037497)
        ·
          refine ⟨51191972830310902527778123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68255963773747870037037497 51191972830310902527778123)
          ·
            refine ⟨76787959245466353791667185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51191972830310902527778123 76787959245466353791667185)
            ·
              refine ⟨57590969434099765343750389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76787959245466353791667185 57590969434099765343750389)
              ·
                refine ⟨5399153384446853000976599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57590969434099765343750389 5399153384446853000976599)
                ·
                  refine ⟨8098730076670279501464899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5399153384446853000976599 8098730076670279501464899)
                  ·
                    refine ⟨12148095115005419252197349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8098730076670279501464899 12148095115005419252197349)
                    ·
                      refine ⟨2277767834063516109787003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12148095115005419252197349 2277767834063516109787003)
                      ·
                        rfl

theorem cell23_4435937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 1, 4].length) (baseStart_4435937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4435937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4435937 prefixEnd_4435937 := by exact prefixLift 4435937
  have htrace : WordTrace (prefixWord ++ tailWord_4435937) baseStart_4435937 baseEnd_4435937 := by
    simpa [prefixWord, tailWord_4435937, baseEnd_4435937] using wordTrace_append hprefix tailTrace_4435937
  have hstable : (prefixWord ++ tailWord_4435937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4435937).length < 2 ^ (prefixWord ++ tailWord_4435937).sum := by decide
  have hdescent : baseEnd_4435937 < baseStart_4435937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4435937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4435960 : List Nat := [2, 1, 2, 1, 1, 3, 5, 8]
def baseStart_4435960 : Nat := 118140960795 + 4435960 * 2 ^ 59
def prefixEnd_4435960 : Nat := 4983230072969 + 3 ^ 40 * 4435960 * 2
def baseEnd_4435960 : Nat := 84362209041428500733311

theorem tailTrace_4435960 : CollatzResearch.WordTrace tailWord_4435960 prefixEnd_4435960 84362209041428500733311 := by
  unfold tailWord_4435960
  simp only [CollatzResearch.WordTrace]
  refine ⟨80896376504640998248680667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107861835339521330998240889 80896376504640998248680667)
  ·
    refine ⟨121344564756961497373021001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80896376504640998248680667 121344564756961497373021001)
    ·
      refine ⟨91008423567721123029765751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121344564756961497373021001 91008423567721123029765751)
      ·
        refine ⟨136512635351581684544648627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91008423567721123029765751 136512635351581684544648627)
        ·
          refine ⟨204768953027372526816972941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136512635351581684544648627 204768953027372526816972941)
          ·
            refine ⟨76788357385264697556364853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 204768953027372526816972941 76788357385264697556364853)
            ·
              refine ⟨7198908504868565395909205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76788357385264697556364853 7198908504868565395909205)
              ·
                refine ⟨84362209041428500733311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7198908504868565395909205 84362209041428500733311)
                ·
                  rfl

theorem cell23_4435960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 8].length) (baseStart_4435960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4435960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4435960 prefixEnd_4435960 := by exact prefixLift 4435960
  have htrace : WordTrace (prefixWord ++ tailWord_4435960) baseStart_4435960 baseEnd_4435960 := by
    simpa [prefixWord, tailWord_4435960, baseEnd_4435960] using wordTrace_append hprefix tailTrace_4435960
  have hstable : (prefixWord ++ tailWord_4435960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4435960).length < 2 ^ (prefixWord ++ tailWord_4435960).sum := by decide
  have hdescent : baseEnd_4435960 < baseStart_4435960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4435960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4435987 : List Nat := [1, 1, 1, 2, 1, 4, 4, 2, 1, 3, 3]
def baseStart_4435987 : Nat := 118140960795 + 4435987 * 2 ^ 59
def prefixEnd_4435987 : Nat := 4983230072969 + 3 ^ 40 * 4435987 * 2
def baseEnd_4435987 : Nat := 2277793508096240914161773

theorem tailTrace_4435987 : CollatzResearch.WordTrace tailWord_4435987 prefixEnd_4435987 2277793508096240914161773 := by
  unfold tailWord_4435987
  simp only [CollatzResearch.WordTrace]
  refine ⟨161793737780184180108594215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107862491853456120072396143 161793737780184180108594215)
  ·
    refine ⟨242690606670276270162891323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161793737780184180108594215 242690606670276270162891323)
    ·
      refine ⟨364035910005414405244336985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242690606670276270162891323 364035910005414405244336985)
      ·
        refine ⟨273026932504060803933252739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 364035910005414405244336985 273026932504060803933252739)
        ·
          refine ⟨409540398756091205899879109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273026932504060803933252739 409540398756091205899879109)
          ·
            refine ⟨76788824766767101106227333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 409540398756091205899879109 76788824766767101106227333)
            ·
              refine ⟨14397904643768831457417625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76788824766767101106227333 14397904643768831457417625)
              ·
                refine ⟨10798428482826623593063219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14397904643768831457417625 10798428482826623593063219)
                ·
                  refine ⟨16197642724239935389594829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10798428482826623593063219 16197642724239935389594829)
                  ·
                    refine ⟨6074116021589975771098061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16197642724239935389594829 6074116021589975771098061)
                    ·
                      refine ⟨2277793508096240914161773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6074116021589975771098061 2277793508096240914161773)
                      ·
                        rfl

theorem cell23_4435987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 3, 3].length) (baseStart_4435987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4435987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4435987 prefixEnd_4435987 := by exact prefixLift 4435987
  have htrace : WordTrace (prefixWord ++ tailWord_4435987) baseStart_4435987 baseEnd_4435987 := by
    simpa [prefixWord, tailWord_4435987, baseEnd_4435987] using wordTrace_append hprefix tailTrace_4435987
  have hstable : (prefixWord ++ tailWord_4435987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4435987).length < 2 ^ (prefixWord ++ tailWord_4435987).sum := by decide
  have hdescent : baseEnd_4435987 < baseStart_4435987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4435987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4435988 : List Nat := [2, 4, 3, 2, 1, 1, 1, 3, 1, 1, 4]
def baseStart_4435988 : Nat := 118140960795 + 4435988 * 2 ^ 59
def prefixEnd_4435988 : Nat := 4983230072969 + 3 ^ 40 * 4435988 * 2
def baseEnd_4435988 : Nat := 2277794021576895410249269

theorem tailTrace_4435988 : CollatzResearch.WordTrace tailWord_4435988 prefixEnd_4435988 2277794021576895410249269 := by
  unfold tailWord_4435988
  simp only [CollatzResearch.WordTrace]
  refine ⟨80896887126590278639690309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107862516168787038186253745 80896887126590278639690309)
  ·
    refine ⟨15168166336235677244941933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80896887126590278639690309 15168166336235677244941933)
    ·
      refine ⟨5688062376088378966853225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15168166336235677244941933 5688062376088378966853225)
      ·
        refine ⟨4266046782066284225139919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5688062376088378966853225 4266046782066284225139919)
        ·
          refine ⟨6399070173099426337709879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4266046782066284225139919 6399070173099426337709879)
          ·
            refine ⟨9598605259649139506564819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6399070173099426337709879 9598605259649139506564819)
            ·
              refine ⟨14397907889473709259847229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9598605259649139506564819 14397907889473709259847229)
              ·
                refine ⟨5399215458552640972442711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14397907889473709259847229 5399215458552640972442711)
                ·
                  refine ⟨8098823187828961458664067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5399215458552640972442711 8098823187828961458664067)
                  ·
                    refine ⟨12148234781743442187996101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8098823187828961458664067 12148234781743442187996101)
                    ·
                      refine ⟨2277794021576895410249269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12148234781743442187996101 2277794021576895410249269)
                      ·
                        rfl

theorem cell23_4435988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_4435988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4435988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4435988 prefixEnd_4435988 := by exact prefixLift 4435988
  have htrace : WordTrace (prefixWord ++ tailWord_4435988) baseStart_4435988 baseEnd_4435988 := by
    simpa [prefixWord, tailWord_4435988, baseEnd_4435988] using wordTrace_append hprefix tailTrace_4435988
  have hstable : (prefixWord ++ tailWord_4435988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4435988).length < 2 ^ (prefixWord ++ tailWord_4435988).sum := by decide
  have hdescent : baseEnd_4435988 < baseStart_4435988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4435988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4435991 : List Nat := [1, 1, 3, 5, 2, 1, 1, 3, 1, 2, 3]
def baseStart_4435991 : Nat := 118140960795 + 4435991 * 2 ^ 59
def prefixEnd_4435991 : Nat := 4983230072969 + 3 ^ 40 * 4435991 * 2
def baseEnd_4435991 : Nat := 2277795562018858898511755

theorem tailTrace_4435991 : CollatzResearch.WordTrace tailWord_4435991 prefixEnd_4435991 2277795562018858898511755 := by
  unfold tailWord_4435991
  simp only [CollatzResearch.WordTrace]
  refine ⟨161793883672169688791739827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107862589114779792527826551 161793883672169688791739827)
  ·
    refine ⟨242690825508254533187609741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161793883672169688791739827 242690825508254533187609741)
    ·
      refine ⟨91009059565595449945353653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 242690825508254533187609741 91009059565595449945353653)
      ·
        refine ⟨8532099334274573432376905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 91009059565595449945353653 8532099334274573432376905)
        ·
          refine ⟨6399074500705930074282679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8532099334274573432376905 6399074500705930074282679)
          ·
            refine ⟨9598611751058895111424019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6399074500705930074282679 9598611751058895111424019)
            ·
              refine ⟨14397917626588342667136029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9598611751058895111424019 14397917626588342667136029)
              ·
                refine ⟨5399219109970628500176011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14397917626588342667136029 5399219109970628500176011)
                ·
                  refine ⟨8098828664955942750264017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5399219109970628500176011 8098828664955942750264017)
                  ·
                    refine ⟨6074121498716957062698013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8098828664955942750264017 6074121498716957062698013)
                    ·
                      refine ⟨2277795562018858898511755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6074121498716957062698013 2277795562018858898511755)
                      ·
                        rfl

theorem cell23_4435991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_4435991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4435991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4435991 prefixEnd_4435991 := by exact prefixLift 4435991
  have htrace : WordTrace (prefixWord ++ tailWord_4435991) baseStart_4435991 baseEnd_4435991 := by
    simpa [prefixWord, tailWord_4435991, baseEnd_4435991] using wordTrace_append hprefix tailTrace_4435991
  have hstable : (prefixWord ++ tailWord_4435991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4435991).length < 2 ^ (prefixWord ++ tailWord_4435991).sum := by decide
  have hdescent : baseEnd_4435991 < baseStart_4435991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4435991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436044 : List Nat := [2, 2, 1, 3, 1, 1, 2, 4, 1, 4, 2]
def baseStart_4436044 : Nat := 118140960795 + 4436044 * 2 ^ 59
def prefixEnd_4436044 : Nat := 4983230072969 + 3 ^ 40 * 4436044 * 2
def baseEnd_4436044 : Nat := 2277822776493547191149011

theorem tailTrace_4436044 : CollatzResearch.WordTrace tailWord_4436044 prefixEnd_4436044 2277822776493547191149011 := by
  unfold tailWord_4436044
  simp only [CollatzResearch.WordTrace]
  refine ⟨80897908370488839421709593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107863877827318452562279457 80897908370488839421709593)
  ·
    refine ⟨60673431277866629566282195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80897908370488839421709593 60673431277866629566282195)
    ·
      refine ⟨91010146916799944349423293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60673431277866629566282195 91010146916799944349423293)
      ·
        refine ⟨34128805093799979131033735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91010146916799944349423293 34128805093799979131033735)
        ·
          refine ⟨51193207640699968696550603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34128805093799979131033735 51193207640699968696550603)
          ·
            refine ⟨76789811461049953044825905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51193207640699968696550603 76789811461049953044825905)
            ·
              refine ⟨57592358595787464783619429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76789811461049953044825905 57592358595787464783619429)
              ·
                refine ⟨10798567236710149646928643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57592358595787464783619429 10798567236710149646928643)
                ·
                  refine ⟨16197850855065224470392965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10798567236710149646928643 16197850855065224470392965)
                  ·
                    refine ⟨3037097035324729588198681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16197850855065224470392965 3037097035324729588198681)
                    ·
                      refine ⟨2277822776493547191149011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3037097035324729588198681 2277822776493547191149011)
                      ·
                        rfl

theorem cell23_4436044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_4436044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436044 prefixEnd_4436044 := by exact prefixLift 4436044
  have htrace : WordTrace (prefixWord ++ tailWord_4436044) baseStart_4436044 baseEnd_4436044 := by
    simpa [prefixWord, tailWord_4436044, baseEnd_4436044] using wordTrace_append hprefix tailTrace_4436044
  have hstable : (prefixWord ++ tailWord_4436044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436044).length < 2 ^ (prefixWord ++ tailWord_4436044).sum := by decide
  have hdescent : baseEnd_4436044 < baseStart_4436044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436067 : List Nat := [1, 1, 1, 5, 1, 1, 5, 1, 7]
def baseStart_4436067 : Nat := 118140960795 + 4436067 * 2 ^ 59
def prefixEnd_4436067 : Nat := 4983230072969 + 3 ^ 40 * 4436067 * 2
def baseEnd_4436067 : Nat := 253092731838733400129045

theorem tailTrace_4436067 : CollatzResearch.WordTrace tailWord_4436067 prefixEnd_4436067 253092731838733400129045 := by
  unfold tailWord_4436067
  simp only [CollatzResearch.WordTrace]
  refine ⟨161796655619894353771506455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107864437079929569181004303 161796655619894353771506455)
  ·
    refine ⟨242694983429841530657259683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161796655619894353771506455 242694983429841530657259683)
    ·
      refine ⟨364042475144762295985889525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242694983429841530657259683 364042475144762295985889525)
      ·
        refine ⟨34128982044821465248677143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 364042475144762295985889525 34128982044821465248677143)
        ·
          refine ⟨51193473067232197873015715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34128982044821465248677143 51193473067232197873015715)
          ·
            refine ⟨76790209600848296809523573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51193473067232197873015715 76790209600848296809523573)
            ·
              refine ⟨7199082150079527825892835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76790209600848296809523573 7199082150079527825892835)
              ·
                refine ⟨10798623225119291738839253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7199082150079527825892835 10798623225119291738839253)
                ·
                  refine ⟨253092731838733400129045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10798623225119291738839253 253092731838733400129045)
                  ·
                    rfl

theorem cell23_4436067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 7].length) (baseStart_4436067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436067 prefixEnd_4436067 := by exact prefixLift 4436067
  have htrace : WordTrace (prefixWord ++ tailWord_4436067) baseStart_4436067 baseEnd_4436067 := by
    simpa [prefixWord, tailWord_4436067, baseEnd_4436067] using wordTrace_append hprefix tailTrace_4436067
  have hstable : (prefixWord ++ tailWord_4436067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436067).length < 2 ^ (prefixWord ++ tailWord_4436067).sum := by decide
  have hdescent : baseEnd_4436067 < baseStart_4436067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436078 : List Nat := [4, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2]
def baseStart_4436078 : Nat := 118140960795 + 4436078 * 2 ^ 59
def prefixEnd_4436078 : Nat := 4983230072969 + 3 ^ 40 * 4436078 * 2
def baseEnd_4436078 : Nat := 2277840234835800058123855

theorem tailTrace_4436078 : CollatzResearch.WordTrace tailWord_4436078 prefixEnd_4436078 2277840234835800058123855 := by
  unfold tailWord_4436078
  simp only [CollatzResearch.WordTrace]
  refine ⟨20224632102856812831269611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107864704548569668433437925 20224632102856812831269611)
  ·
    refine ⟨30336948154285219246904417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20224632102856812831269611 30336948154285219246904417)
    ·
      refine ⟨22752711115713914435178313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30336948154285219246904417 22752711115713914435178313)
      ·
        refine ⟨17064533336785435826383735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22752711115713914435178313 17064533336785435826383735)
        ·
          refine ⟨25596800005178153739575603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17064533336785435826383735 25596800005178153739575603)
          ·
            refine ⟨38395200007767230609363405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25596800005178153739575603 38395200007767230609363405)
            ·
              refine ⟨14398200002912711478511277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38395200007767230609363405 14398200002912711478511277)
              ·
                refine ⟨5399325001092266804441729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14398200002912711478511277 5399325001092266804441729)
                ·
                  refine ⟨4049493750819200103331297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5399325001092266804441729 4049493750819200103331297)
                  ·
                    refine ⟨3037120313114400077498473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4049493750819200103331297 3037120313114400077498473)
                    ·
                      refine ⟨2277840234835800058123855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3037120313114400077498473 2277840234835800058123855)
                      ·
                        rfl

theorem cell23_4436078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_4436078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436078 prefixEnd_4436078 := by exact prefixLift 4436078
  have htrace : WordTrace (prefixWord ++ tailWord_4436078) baseStart_4436078 baseEnd_4436078 := by
    simpa [prefixWord, tailWord_4436078, baseEnd_4436078] using wordTrace_append hprefix tailTrace_4436078
  have hstable : (prefixWord ++ tailWord_4436078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436078).length < 2 ^ (prefixWord ++ tailWord_4436078).sum := by decide
  have hdescent : baseEnd_4436078 < baseStart_4436078 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436114 : List Nat := [3, 2, 3, 1, 1, 1, 1, 4, 2, 5]
def baseStart_4436114 : Nat := 118140960795 + 4436114 * 2 ^ 59
def prefixEnd_4436114 : Nat := 4983230072969 + 3 ^ 40 * 4436114 * 2
def baseEnd_4436114 : Nat := 759286240046453972424563

theorem tailTrace_4436114 : CollatzResearch.WordTrace tailWord_4436114 prefixEnd_4436114 759286240046453972424563 := by
  unfold tailWord_4436114
  simp only [CollatzResearch.WordTrace]
  refine ⟨40449592462681020199616849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107865579900482720532311597 40449592462681020199616849)
  ·
    refine ⟨30337194347010765149712637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40449592462681020199616849 30337194347010765149712637)
    ·
      refine ⟨11376447880129036931142239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30337194347010765149712637 11376447880129036931142239)
      ·
        refine ⟨17064671820193555396713359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11376447880129036931142239 17064671820193555396713359)
        ·
          refine ⟨25597007730290333095070039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17064671820193555396713359 25597007730290333095070039)
          ·
            refine ⟨38395511595435499642605059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25597007730290333095070039 38395511595435499642605059)
            ·
              refine ⟨57593267393153249463907589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38395511595435499642605059 57593267393153249463907589)
              ·
                refine ⟨10798737636216234274482673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57593267393153249463907589 10798737636216234274482673)
                ·
                  refine ⟨8099053227162175705862005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10798737636216234274482673 8099053227162175705862005)
                  ·
                    refine ⟨759286240046453972424563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8099053227162175705862005 759286240046453972424563)
                    ·
                      rfl

theorem cell23_4436114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_4436114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436114 prefixEnd_4436114 := by exact prefixLift 4436114
  have htrace : WordTrace (prefixWord ++ tailWord_4436114) baseStart_4436114 baseEnd_4436114 := by
    simpa [prefixWord, tailWord_4436114, baseEnd_4436114] using wordTrace_append hprefix tailTrace_4436114
  have hstable : (prefixWord ++ tailWord_4436114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436114).length < 2 ^ (prefixWord ++ tailWord_4436114).sum := by decide
  have hdescent : baseEnd_4436114 < baseStart_4436114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436151 : List Nat := [1, 1, 3, 1, 4, 4, 1, 1, 2, 1, 4]
def baseStart_4436151 : Nat := 118140960795 + 4436151 * 2 ^ 59
def prefixEnd_4436151 : Nat := 4983230072969 + 3 ^ 40 * 4436151 * 2
def baseEnd_4436151 : Nat := 2277877718923578272511019

theorem tailTrace_4436151 : CollatzResearch.WordTrace tailWord_4436151 prefixEnd_4436151 2277877718923578272511019 := by
  unfold tailWord_4436151
  simp only [CollatzResearch.WordTrace]
  refine ⟨161799719351590036117564307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107866479567726690745042871 161799719351590036117564307)
  ·
    refine ⟨242699579027385054176346461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161799719351590036117564307 242699579027385054176346461)
    ·
      refine ⟨91012342135269395316129923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 242699579027385054176346461 91012342135269395316129923)
      ·
        refine ⟨136518513202904092974194885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91012342135269395316129923 136518513202904092974194885)
        ·
          refine ⟨25597221225544517432661541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136518513202904092974194885 25597221225544517432661541)
          ·
            refine ⟨4799478979789597018624039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25597221225544517432661541 4799478979789597018624039)
            ·
              refine ⟨7199218469684395527936059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4799478979789597018624039 7199218469684395527936059)
              ·
                refine ⟨10798827704526593291904089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7199218469684395527936059 10798827704526593291904089)
                ·
                  refine ⟨8099120778394944968928067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10798827704526593291904089 8099120778394944968928067)
                  ·
                    refine ⟨12148681167592417453392101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8099120778394944968928067 12148681167592417453392101)
                    ·
                      refine ⟨2277877718923578272511019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12148681167592417453392101 2277877718923578272511019)
                      ·
                        rfl

theorem cell23_4436151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 1, 4].length) (baseStart_4436151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436151 prefixEnd_4436151 := by exact prefixLift 4436151
  have htrace : WordTrace (prefixWord ++ tailWord_4436151) baseStart_4436151 baseEnd_4436151 := by
    simpa [prefixWord, tailWord_4436151, baseEnd_4436151] using wordTrace_append hprefix tailTrace_4436151
  have hstable : (prefixWord ++ tailWord_4436151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436151).length < 2 ^ (prefixWord ++ tailWord_4436151).sum := by decide
  have hdescent : baseEnd_4436151 < baseStart_4436151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436157 : List Nat := [1, 4, 1, 2, 1, 1, 1, 4, 8]
def baseStart_4436157 : Nat := 118140960795 + 4436157 * 2 ^ 59
def prefixEnd_4436157 : Nat := 4983230072969 + 3 ^ 40 * 4436157 * 2
def baseEnd_4436157 : Nat := 253097866645278361003999

theorem tailTrace_4436157 : CollatzResearch.WordTrace tailWord_4436157 prefixEnd_4436157 253097866645278361003999 := by
  unfold tailWord_4436157
  simp only [CollatzResearch.WordTrace]
  refine ⟨161799938189568299142282725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107866625459712199428188483 161799938189568299142282725)
  ·
    refine ⟨30337488410544056089178011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161799938189568299142282725 30337488410544056089178011)
    ·
      refine ⟨45506232615816084133767017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30337488410544056089178011 45506232615816084133767017)
      ·
        refine ⟨34129674461862063100325263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45506232615816084133767017 34129674461862063100325263)
        ·
          refine ⟨51194511692793094650487895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34129674461862063100325263 51194511692793094650487895)
          ·
            refine ⟨76791767539189641975731843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51194511692793094650487895 76791767539189641975731843)
            ·
              refine ⟨115187651308784462963597765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76791767539189641975731843 115187651308784462963597765)
              ·
                refine ⟨21597684620397086805674581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 115187651308784462963597765 21597684620397086805674581)
                ·
                  refine ⟨253097866645278361003999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21597684620397086805674581 253097866645278361003999)
                  ·
                    rfl

theorem cell23_4436157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 8].length) (baseStart_4436157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436157 prefixEnd_4436157 := by exact prefixLift 4436157
  have htrace : WordTrace (prefixWord ++ tailWord_4436157) baseStart_4436157 baseEnd_4436157 := by
    simpa [prefixWord, tailWord_4436157, baseEnd_4436157] using wordTrace_append hprefix tailTrace_4436157
  have hstable : (prefixWord ++ tailWord_4436157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436157).length < 2 ^ (prefixWord ++ tailWord_4436157).sum := by decide
  have hdescent : baseEnd_4436157 < baseStart_4436157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436164 : List Nat := [2, 3, 3, 1, 2, 1, 1, 1, 2, 1, 6]
def baseStart_4436164 : Nat := 118140960795 + 4436164 * 2 ^ 59
def prefixEnd_4436164 : Nat := 4983230072969 + 3 ^ 40 * 4436164 * 2
def baseEnd_4436164 : Nat := 2277884394172086721648459

theorem tailTrace_4436164 : CollatzResearch.WordTrace tailWord_4436164 prefixEnd_4436164 2277884394172086721648459 := by
  unfold tailWord_4436164
  simp only [CollatzResearch.WordTrace]
  refine ⟨80900096750271469668893773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107866795667028626225191697 80900096750271469668893773)
  ·
    refine ⟨30337536281351801125835165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80900096750271469668893773 30337536281351801125835165)
    ·
      refine ⟨11376576105506925422188187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30337536281351801125835165 11376576105506925422188187)
      ·
        refine ⟨17064864158260388133282281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11376576105506925422188187 17064864158260388133282281)
        ·
          refine ⟨12798648118695291099961711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17064864158260388133282281 12798648118695291099961711)
          ·
            refine ⟨19197972178042936649942567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12798648118695291099961711 19197972178042936649942567)
            ·
              refine ⟨28796958267064404974913851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19197972178042936649942567 28796958267064404974913851)
              ·
                refine ⟨43195437400596607462370777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28796958267064404974913851 43195437400596607462370777)
                ·
                  refine ⟨32396578050447455596778083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43195437400596607462370777 32396578050447455596778083)
                  ·
                    refine ⟨48594867075671183395167125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32396578050447455596778083 48594867075671183395167125)
                    ·
                      refine ⟨2277884394172086721648459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48594867075671183395167125 2277884394172086721648459)
                      ·
                        rfl

theorem cell23_4436164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_4436164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436164 prefixEnd_4436164 := by exact prefixLift 4436164
  have htrace : WordTrace (prefixWord ++ tailWord_4436164) baseStart_4436164 baseEnd_4436164 := by
    simpa [prefixWord, tailWord_4436164, baseEnd_4436164] using wordTrace_append hprefix tailTrace_4436164
  have hstable : (prefixWord ++ tailWord_4436164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436164).length < 2 ^ (prefixWord ++ tailWord_4436164).sum := by decide
  have hdescent : baseEnd_4436164 < baseStart_4436164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436174 : List Nat := [4, 1, 1, 1, 4, 2, 1, 1, 8]
def baseStart_4436174 : Nat := 118140960795 + 4436174 * 2 ^ 59
def prefixEnd_4436174 : Nat := 4983230072969 + 3 ^ 40 * 4436174 * 2
def baseEnd_4436174 : Nat := 253098836553181298058157

theorem tailTrace_4436174 : CollatzResearch.WordTrace tailWord_4436174 prefixEnd_4436174 253098836553181298058157 := by
  unfold tailWord_4436174
  simp only [CollatzResearch.WordTrace]
  refine ⟨20225069778813338880706447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107867038820337807363767717 20225069778813338880706447)
  ·
    refine ⟨30337604668220008321059671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20225069778813338880706447 30337604668220008321059671)
    ·
      refine ⟨45506407002330012481589507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30337604668220008321059671 45506407002330012481589507)
      ·
        refine ⟨68259610503495018722384261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45506407002330012481589507 68259610503495018722384261)
        ·
          refine ⟨12798676969405316010447049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68259610503495018722384261 12798676969405316010447049)
          ·
            refine ⟨9599007727053987007835287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12798676969405316010447049 9599007727053987007835287)
            ·
              refine ⟨14398511590580980511752931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9599007727053987007835287 14398511590580980511752931)
              ·
                refine ⟨21597767385871470767629397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14398511590580980511752931 21597767385871470767629397)
                ·
                  refine ⟨253098836553181298058157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21597767385871470767629397 253098836553181298058157)
                  ·
                    rfl

theorem cell23_4436174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 8].length) (baseStart_4436174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436174 prefixEnd_4436174 := by exact prefixLift 4436174
  have htrace : WordTrace (prefixWord ++ tailWord_4436174) baseStart_4436174 baseEnd_4436174 := by
    simpa [prefixWord, tailWord_4436174, baseEnd_4436174] using wordTrace_append hprefix tailTrace_4436174
  have hstable : (prefixWord ++ tailWord_4436174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436174).length < 2 ^ (prefixWord ++ tailWord_4436174).sum := by decide
  have hdescent : baseEnd_4436174 < baseStart_4436174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436177 : List Nat := [1, 2, 2, 1, 2, 2, 3, 1, 1, 2, 6]
def baseStart_4436177 : Nat := 118140960795 + 4436177 * 2 ^ 59
def prefixEnd_4436177 : Nat := 4983230072969 + 3 ^ 40 * 4436177 * 2
def baseEnd_4436177 : Nat := 2277891069420595170785899

theorem tailTrace_4436177 : CollatzResearch.WordTrace tailWord_4436177 prefixEnd_4436177 2277891069420595170785899 := by
  unfold tailWord_4436177
  simp only [CollatzResearch.WordTrace]
  refine ⟨161800667649495842558010785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107867111766330561705340523 161800667649495842558010785)
  ·
    refine ⟨121350500737121881918508089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161800667649495842558010785 121350500737121881918508089)
    ·
      refine ⟨91012875552841411438881067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121350500737121881918508089 91012875552841411438881067)
      ·
        refine ⟨136519313329262117158321601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91012875552841411438881067 136519313329262117158321601)
        ·
          refine ⟨102389484996946587868741201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136519313329262117158321601 102389484996946587868741201)
          ·
            refine ⟨76792113747709940901555901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102389484996946587868741201 76792113747709940901555901)
            ·
              refine ⟨28797042655391227838083463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76792113747709940901555901 28797042655391227838083463)
              ·
                refine ⟨43195563983086841757125195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28797042655391227838083463 43195563983086841757125195)
                ·
                  refine ⟨64793345974630262635687793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43195563983086841757125195 64793345974630262635687793)
                  ·
                    refine ⟨48595009480972696976765845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64793345974630262635687793 48595009480972696976765845)
                    ·
                      refine ⟨2277891069420595170785899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48595009480972696976765845 2277891069420595170785899)
                      ·
                        rfl

theorem cell23_4436177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_4436177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436177 prefixEnd_4436177 := by exact prefixLift 4436177
  have htrace : WordTrace (prefixWord ++ tailWord_4436177) baseStart_4436177 baseEnd_4436177 := by
    simpa [prefixWord, tailWord_4436177, baseEnd_4436177] using wordTrace_append hprefix tailTrace_4436177
  have hstable : (prefixWord ++ tailWord_4436177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436177).length < 2 ^ (prefixWord ++ tailWord_4436177).sum := by decide
  have hdescent : baseEnd_4436177 < baseStart_4436177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436178 : List Nat := [3, 2, 2, 2, 1, 2, 2, 4, 1, 4]
def baseStart_4436178 : Nat := 118140960795 + 4436178 * 2 ^ 59
def prefixEnd_4436178 : Nat := 4983230072969 + 3 ^ 40 * 4436178 * 2
def baseEnd_4436178 : Nat := 759297194300416555624465

theorem tailTrace_4436178 : CollatzResearch.WordTrace tailWord_4436178 prefixEnd_4436178 759297194300416555624465 := by
  unfold tailWord_4436178
  simp only [CollatzResearch.WordTrace]
  refine ⟨40450176030623054932199297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107867136081661479819198125 40450176030623054932199297)
  ·
    refine ⟨30337632022967291199149473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40450176030623054932199297 30337632022967291199149473)
    ·
      refine ⟨22753224017225468399362105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30337632022967291199149473 22753224017225468399362105)
      ·
        refine ⟨17064918012919101299521579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22753224017225468399362105 17064918012919101299521579)
        ·
          refine ⟨25597377019378651949282369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17064918012919101299521579 25597377019378651949282369)
          ·
            refine ⟨19198032764533988961961777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25597377019378651949282369 19198032764533988961961777)
            ·
              refine ⟨14398524573400491721471333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19198032764533988961961777 14398524573400491721471333)
              ·
                refine ⟨2699723357512592197775875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14398524573400491721471333 2699723357512592197775875)
                ·
                  refine ⟨4049585036268888296663813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2699723357512592197775875 4049585036268888296663813)
                  ·
                    refine ⟨759297194300416555624465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4049585036268888296663813 759297194300416555624465)
                    ·
                      rfl

theorem cell23_4436178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_4436178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436178 prefixEnd_4436178 := by exact prefixLift 4436178
  have htrace : WordTrace (prefixWord ++ tailWord_4436178) baseStart_4436178 baseEnd_4436178 := by
    simpa [prefixWord, tailWord_4436178, baseEnd_4436178] using wordTrace_append hprefix tailTrace_4436178
  have hstable : (prefixWord ++ tailWord_4436178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436178).length < 2 ^ (prefixWord ++ tailWord_4436178).sum := by decide
  have hdescent : baseEnd_4436178 < baseStart_4436178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436211 : List Nat := [1, 1, 1, 2, 2, 4, 2, 3, 2, 3, 2]
def baseStart_4436211 : Nat := 118140960795 + 4436211 * 2 ^ 59
def prefixEnd_4436211 : Nat := 4983230072969 + 3 ^ 40 * 4436211 * 2
def baseEnd_4436211 : Nat := 2277908527762848037760743

theorem tailTrace_4436211 : CollatzResearch.WordTrace tailWord_4436211 prefixEnd_4436211 2277908527762848037760743 := by
  unfold tailWord_4436211
  simp only [CollatzResearch.WordTrace]
  refine ⟨161801907731372666364748487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107867938487581777576498991 161801907731372666364748487)
  ·
    refine ⟨242702861597058999547122731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161801907731372666364748487 242702861597058999547122731)
    ·
      refine ⟨364054292395588499320684097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242702861597058999547122731 364054292395588499320684097)
      ·
        refine ⟨273040719296691374490513073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 364054292395588499320684097 273040719296691374490513073)
        ·
          refine ⟨204780539472518530867884805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 273040719296691374490513073 204780539472518530867884805)
          ·
            refine ⟨38396351151097224537728401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 204780539472518530867884805 38396351151097224537728401)
            ·
              refine ⟨28797263363322918403296301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38396351151097224537728401 28797263363322918403296301)
              ·
                refine ⟨10798973761246094401236113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28797263363322918403296301 10798973761246094401236113)
                ·
                  refine ⟨8099230320934570800927085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10798973761246094401236113 8099230320934570800927085)
                  ·
                    refine ⟨3037211370350464050347657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8099230320934570800927085 3037211370350464050347657)
                    ·
                      refine ⟨2277908527762848037760743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3037211370350464050347657 2277908527762848037760743)
                      ·
                        rfl

theorem cell23_4436211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 3, 2].length) (baseStart_4436211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436211 prefixEnd_4436211 := by exact prefixLift 4436211
  have htrace : WordTrace (prefixWord ++ tailWord_4436211) baseStart_4436211 baseEnd_4436211 := by
    simpa [prefixWord, tailWord_4436211, baseEnd_4436211] using wordTrace_append hprefix tailTrace_4436211
  have hstable : (prefixWord ++ tailWord_4436211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436211).length < 2 ^ (prefixWord ++ tailWord_4436211).sum := by decide
  have hdescent : baseEnd_4436211 < baseStart_4436211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436235 : List Nat := [1, 1, 1, 1, 5, 2, 5, 2, 1, 1, 3]
def baseStart_4436235 : Nat := 118140960795 + 4436235 * 2 ^ 59
def prefixEnd_4436235 : Nat := 4983230072969 + 3 ^ 40 * 4436235 * 2
def baseEnd_4436235 : Nat := 2277920851298555943860633

theorem tailTrace_4436235 : CollatzResearch.WordTrace tailWord_4436235 prefixEnd_4436235 2277920851298555943860633 := by
  unfold tailWord_4436235
  simp only [CollatzResearch.WordTrace]
  refine ⟨161802783083285718463622159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107868522055523812309081439 161802783083285718463622159)
  ·
    refine ⟨242704174624928577695433239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161802783083285718463622159 242704174624928577695433239)
    ·
      refine ⟨364056261937392866543149859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242704174624928577695433239 364056261937392866543149859)
      ·
        refine ⟨546084392906089299814724789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 364056261937392866543149859 546084392906089299814724789)
        ·
          refine ⟨51195411834945871857630449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 546084392906089299814724789 51195411834945871857630449)
          ·
            refine ⟨38396558876209403893222837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51195411834945871857630449 38396558876209403893222837)
            ·
              refine ⟨3599677394644631614989641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38396558876209403893222837 3599677394644631614989641)
              ·
                refine ⟨2699758045983473711242231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3599677394644631614989641 2699758045983473711242231)
                ·
                  refine ⟨4049637068975210566863347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2699758045983473711242231 4049637068975210566863347)
                  ·
                    refine ⟨6074455603462815850295021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4049637068975210566863347 6074455603462815850295021)
                    ·
                      refine ⟨2277920851298555943860633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6074455603462815850295021 2277920851298555943860633)
                      ·
                        rfl

theorem cell23_4436235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 2, 1, 1, 3].length) (baseStart_4436235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436235 prefixEnd_4436235 := by exact prefixLift 4436235
  have htrace : WordTrace (prefixWord ++ tailWord_4436235) baseStart_4436235 baseEnd_4436235 := by
    simpa [prefixWord, tailWord_4436235, baseEnd_4436235] using wordTrace_append hprefix tailTrace_4436235
  have hstable : (prefixWord ++ tailWord_4436235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436235).length < 2 ^ (prefixWord ++ tailWord_4436235).sum := by decide
  have hdescent : baseEnd_4436235 < baseStart_4436235 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436258 : List Nat := [3, 3, 1, 1, 3, 1, 3, 2, 1, 1, 4]
def baseStart_4436258 : Nat := 118140960795 + 4436258 * 2 ^ 59
def prefixEnd_4436258 : Nat := 4983230072969 + 3 ^ 40 * 4436258 * 2
def baseEnd_4436258 : Nat := 2277932661353609353873027

theorem tailTrace_4436258 : CollatzResearch.WordTrace tailWord_4436258 prefixEnd_4436258 2277932661353609353873027 := by
  unfold tailWord_4436258
  simp only [CollatzResearch.WordTrace]
  refine ⟨40450905490550598347927357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107869081308134928927806285 40450905490550598347927357)
  ·
    refine ⟨15169089558956474380472759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40450905490550598347927357 15169089558956474380472759)
    ·
      refine ⟨22753634338434711570709139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15169089558956474380472759 22753634338434711570709139)
      ·
        refine ⟨34130451507652067356063709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22753634338434711570709139 34130451507652067356063709)
        ·
          refine ⟨12798919315369525258523891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34130451507652067356063709 12798919315369525258523891)
          ·
            refine ⟨19198378973054287887785837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12798919315369525258523891 19198378973054287887785837)
            ·
              refine ⟨7199392114895357957919689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19198378973054287887785837 7199392114895357957919689)
              ·
                refine ⟨5399544086171518468439767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7199392114895357957919689 5399544086171518468439767)
                ·
                  refine ⟨8099316129257277702659651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5399544086171518468439767 8099316129257277702659651)
                  ·
                    refine ⟨12148974193885916553989477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8099316129257277702659651 12148974193885916553989477)
                    ·
                      refine ⟨2277932661353609353873027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12148974193885916553989477 2277932661353609353873027)
                      ·
                        rfl

theorem cell23_4436258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_4436258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436258 prefixEnd_4436258 := by exact prefixLift 4436258
  have htrace : WordTrace (prefixWord ++ tailWord_4436258) baseStart_4436258 baseEnd_4436258 := by
    simpa [prefixWord, tailWord_4436258, baseEnd_4436258] using wordTrace_append hprefix tailTrace_4436258
  have hstable : (prefixWord ++ tailWord_4436258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436258).length < 2 ^ (prefixWord ++ tailWord_4436258).sum := by decide
  have hdescent : baseEnd_4436258 < baseStart_4436258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436275 : List Nat := [1, 1, 1, 2, 5, 1, 2, 5, 1, 2, 2]
def baseStart_4436275 : Nat := 118140960795 + 4436275 * 2 ^ 59
def prefixEnd_4436275 : Nat := 4983230072969 + 3 ^ 40 * 4436275 * 2
def baseEnd_4436275 : Nat := 2277941390524735787360449

theorem tailTrace_4436275 : CollatzResearch.WordTrace tailWord_4436275 prefixEnd_4436275 2277941390524735787360449 := by
  unfold tailWord_4436275
  simp only [CollatzResearch.WordTrace]
  refine ⟨161804242003140805295078279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107869494668760536863385519 161804242003140805295078279)
  ·
    refine ⟨242706363004711207942617419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161804242003140805295078279 242706363004711207942617419)
    ·
      refine ⟨364059544507066811913926129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242706363004711207942617419 364059544507066811913926129)
      ·
        refine ⟨273044658380300108935444597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 364059544507066811913926129 273044658380300108935444597)
        ·
          refine ⟨25597936723153135212697931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 273044658380300108935444597 25597936723153135212697931)
          ·
            refine ⟨38396905084729702819046897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25597936723153135212697931 38396905084729702819046897)
            ·
              refine ⟨28797678813547277114285173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38396905084729702819046897 28797678813547277114285173)
              ·
                refine ⟨2699782388770057229464235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28797678813547277114285173 2699782388770057229464235)
                ·
                  refine ⟨4049673583155085844196353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2699782388770057229464235 4049673583155085844196353)
                  ·
                    refine ⟨3037255187366314383147265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4049673583155085844196353 3037255187366314383147265)
                    ·
                      refine ⟨2277941390524735787360449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3037255187366314383147265 2277941390524735787360449)
                      ·
                        rfl

theorem cell23_4436275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 5, 1, 2, 2].length) (baseStart_4436275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436275 prefixEnd_4436275 := by exact prefixLift 4436275
  have htrace : WordTrace (prefixWord ++ tailWord_4436275) baseStart_4436275 baseEnd_4436275 := by
    simpa [prefixWord, tailWord_4436275, baseEnd_4436275] using wordTrace_append hprefix tailTrace_4436275
  have hstable : (prefixWord ++ tailWord_4436275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436275).length < 2 ^ (prefixWord ++ tailWord_4436275).sum := by decide
  have hdescent : baseEnd_4436275 < baseStart_4436275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436291 : List Nat := [1, 1, 1, 3, 1, 3, 2, 3, 4, 1, 3]
def baseStart_4436291 : Nat := 118140960795 + 4436291 * 2 ^ 59
def prefixEnd_4436291 : Nat := 4983230072969 + 3 ^ 40 * 4436291 * 2
def baseEnd_4436291 : Nat := 2277949606215207724760375

theorem tailTrace_4436291 : CollatzResearch.WordTrace tailWord_4436291 prefixEnd_4436291 2277949606215207724760375 := by
  unfold tailWord_4436291
  simp only [CollatzResearch.WordTrace]
  refine ⟨161804825571082840027660727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107869883714055226685107151 161804825571082840027660727)
  ·
    refine ⟨242707238356624260041491091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161804825571082840027660727 242707238356624260041491091)
    ·
      refine ⟨364060857534936390062236637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242707238356624260041491091 364060857534936390062236637)
      ·
        refine ⟨136522821575601146273338739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 364060857534936390062236637 136522821575601146273338739)
        ·
          refine ⟨204784232363401719410008109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136522821575601146273338739 204784232363401719410008109)
          ·
            refine ⟨76794087136275644778753041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 204784232363401719410008109 76794087136275644778753041)
            ·
              refine ⟨57595565352206733584064781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76794087136275644778753041 57595565352206733584064781)
              ·
                refine ⟨21598337007077525094024293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57595565352206733584064781 21598337007077525094024293)
                ·
                  refine ⟨4049688188827035955129555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21598337007077525094024293 4049688188827035955129555)
                  ·
                    refine ⟨6074532283240553932694333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4049688188827035955129555 6074532283240553932694333)
                    ·
                      refine ⟨2277949606215207724760375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6074532283240553932694333 2277949606215207724760375)
                      ·
                        rfl

theorem cell23_4436291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 1, 3].length) (baseStart_4436291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436291 prefixEnd_4436291 := by exact prefixLift 4436291
  have htrace : WordTrace (prefixWord ++ tailWord_4436291) baseStart_4436291 baseEnd_4436291 := by
    simpa [prefixWord, tailWord_4436291, baseEnd_4436291] using wordTrace_append hprefix tailTrace_4436291
  have hstable : (prefixWord ++ tailWord_4436291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436291).length < 2 ^ (prefixWord ++ tailWord_4436291).sum := by decide
  have hdescent : baseEnd_4436291 < baseStart_4436291 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436308 : List Nat := [2, 4, 1, 1, 2, 3, 2, 1, 1, 3, 3]
def baseStart_4436308 : Nat := 118140960795 + 4436308 * 2 ^ 59
def prefixEnd_4436308 : Nat := 4983230072969 + 3 ^ 40 * 4436308 * 2
def baseEnd_4436308 : Nat := 2277958335386334158247797

theorem tailTrace_4436308 : CollatzResearch.WordTrace tailWord_4436308 prefixEnd_4436308 2277958335386334158247797 := by
  unfold tailWord_4436308
  simp only [CollatzResearch.WordTrace]
  refine ⟨80902722806010625965514789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107870297074680834620686385 80902722806010625965514789)
  ·
    refine ⟨15169260526126992368534023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80902722806010625965514789 15169260526126992368534023)
    ·
      refine ⟨22753890789190488552801035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15169260526126992368534023 22753890789190488552801035)
      ·
        refine ⟨34130836183785732829201553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22753890789190488552801035 34130836183785732829201553)
        ·
          refine ⟨25598127137839299621901165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34130836183785732829201553 25598127137839299621901165)
          ·
            refine ⟨9599297676689737358212937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25598127137839299621901165 9599297676689737358212937)
            ·
              refine ⟨7199473257517303018659703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9599297676689737358212937 7199473257517303018659703)
              ·
                refine ⟨10799209886275954527989555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7199473257517303018659703 10799209886275954527989555)
                ·
                  refine ⟨16198814829413931791984333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10799209886275954527989555 16198814829413931791984333)
                  ·
                    refine ⟨6074555561030224421994125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16198814829413931791984333 6074555561030224421994125)
                    ·
                      refine ⟨2277958335386334158247797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6074555561030224421994125 2277958335386334158247797)
                      ·
                        rfl

theorem cell23_4436308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_4436308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436308 prefixEnd_4436308 := by exact prefixLift 4436308
  have htrace : WordTrace (prefixWord ++ tailWord_4436308) baseStart_4436308 baseEnd_4436308 := by
    simpa [prefixWord, tailWord_4436308, baseEnd_4436308] using wordTrace_append hprefix tailTrace_4436308
  have hstable : (prefixWord ++ tailWord_4436308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436308).length < 2 ^ (prefixWord ++ tailWord_4436308).sum := by decide
  have hdescent : baseEnd_4436308 < baseStart_4436308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436314 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 4, 3, 4]
def baseStart_4436314 : Nat := 118140960795 + 4436314 * 2 ^ 59
def prefixEnd_4436314 : Nat := 4983230072969 + 3 ^ 40 * 4436314 * 2
def baseEnd_4436314 : Nat := 2277961416270261134772769

theorem tailTrace_4436314 : CollatzResearch.WordTrace tailWord_4436314 prefixEnd_4436314 2277961416270261134772769 := by
  unfold tailWord_4436314
  simp only [CollatzResearch.WordTrace]
  refine ⟨40451416112499878738936999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107870442966666343303831997 40451416112499878738936999)
  ·
    refine ⟨60677124168749818108405499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40451416112499878738936999 60677124168749818108405499)
    ·
      refine ⟨91015686253124727162608249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60677124168749818108405499 91015686253124727162608249)
      ·
        refine ⟨68261764689843545371956187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91015686253124727162608249 68261764689843545371956187)
        ·
          refine ⟨102392647034765318057934281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68261764689843545371956187 102392647034765318057934281)
          ·
            refine ⟨76794485276073988543450711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102392647034765318057934281 76794485276073988543450711)
            ·
              refine ⟨115191727914110982815176067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76794485276073988543450711 115191727914110982815176067)
              ·
                refine ⟨172787591871166474222764101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115191727914110982815176067 172787591871166474222764101)
                ·
                  refine ⟨32397673475843713916768269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 172787591871166474222764101 32397673475843713916768269)
                  ·
                    refine ⟨12149127553441392718788101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32397673475843713916768269 12149127553441392718788101)
                    ·
                      refine ⟨2277961416270261134772769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12149127553441392718788101 2277961416270261134772769)
                      ·
                        rfl

theorem cell23_4436314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_4436314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436314 prefixEnd_4436314 := by exact prefixLift 4436314
  have htrace : WordTrace (prefixWord ++ tailWord_4436314) baseStart_4436314 baseEnd_4436314 := by
    simpa [prefixWord, tailWord_4436314, baseEnd_4436314] using wordTrace_append hprefix tailTrace_4436314
  have hstable : (prefixWord ++ tailWord_4436314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436314).length < 2 ^ (prefixWord ++ tailWord_4436314).sum := by decide
  have hdescent : baseEnd_4436314 < baseStart_4436314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436324 : List Nat := [2, 3, 1, 1, 3, 1, 1, 2, 1, 8]
def baseStart_4436324 : Nat := 118140960795 + 4436324 * 2 ^ 59
def prefixEnd_4436324 : Nat := 4983230072969 + 3 ^ 40 * 4436324 * 2
def baseEnd_4436324 : Nat := 759322183692268698549241

theorem tailTrace_4436324 : CollatzResearch.WordTrace tailWord_4436324 prefixEnd_4436324 759322183692268698549241 := by
  unfold tailWord_4436324
  simp only [CollatzResearch.WordTrace]
  refine ⟨80903014589981643331806013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107870686119975524442408017 80903014589981643331806013)
  ·
    refine ⟨30338630471243116249427255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80903014589981643331806013 30338630471243116249427255)
    ·
      refine ⟨45507945706864674374140883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30338630471243116249427255 45507945706864674374140883)
      ·
        refine ⟨68261918560297011561211325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45507945706864674374140883 68261918560297011561211325)
        ·
          refine ⟨25598219460111379335454247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68261918560297011561211325 25598219460111379335454247)
          ·
            refine ⟨38397329190167069003181371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25598219460111379335454247 38397329190167069003181371)
            ·
              refine ⟨57595993785250603504772057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38397329190167069003181371 57595993785250603504772057)
              ·
                refine ⟨43196995338937952628579043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57595993785250603504772057 43196995338937952628579043)
                ·
                  refine ⟨64795493008406928942868565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43196995338937952628579043 64795493008406928942868565)
                  ·
                    refine ⟨759322183692268698549241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 64795493008406928942868565 759322183692268698549241)
                    ·
                      rfl

theorem cell23_4436324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_4436324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436324 prefixEnd_4436324 := by exact prefixLift 4436324
  have htrace : WordTrace (prefixWord ++ tailWord_4436324) baseStart_4436324 baseEnd_4436324 := by
    simpa [prefixWord, tailWord_4436324, baseEnd_4436324] using wordTrace_append hprefix tailTrace_4436324
  have hstable : (prefixWord ++ tailWord_4436324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436324).length < 2 ^ (prefixWord ++ tailWord_4436324).sum := by decide
  have hdescent : baseEnd_4436324 < baseStart_4436324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436341 : List Nat := [1, 3, 4, 1, 2, 1, 1, 2, 2, 6]
def baseStart_4436341 : Nat := 118140960795 + 4436341 * 2 ^ 59
def prefixEnd_4436341 : Nat := 4983230072969 + 3 ^ 40 * 4436341 * 2
def baseEnd_4436341 : Nat := 759325093415977509711715

theorem tailTrace_4436341 : CollatzResearch.WordTrace tailWord_4436341 prefixEnd_4436341 759325093415977509711715 := by
  unfold tailWord_4436341
  simp only [CollatzResearch.WordTrace]
  refine ⟨161806649220901698566980877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107871099480601132377987251 161806649220901698566980877)
  ·
    refine ⟨60677493457838136962617829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161806649220901698566980877 60677493457838136962617829)
    ·
      refine ⟨11377030023344650680490843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60677493457838136962617829 11377030023344650680490843)
      ·
        refine ⟨17065545035016976020736265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11377030023344650680490843 17065545035016976020736265)
        ·
          refine ⟨12799158776262732015552199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17065545035016976020736265 12799158776262732015552199)
          ·
            refine ⟨19198738164394098023328299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12799158776262732015552199 19198738164394098023328299)
            ·
              refine ⟨28798107246591147034992449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19198738164394098023328299 28798107246591147034992449)
              ·
                refine ⟨21598580434943360276244337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28798107246591147034992449 21598580434943360276244337)
                ·
                  refine ⟨16198935326207520207183253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21598580434943360276244337 16198935326207520207183253)
                  ·
                    refine ⟨759325093415977509711715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16198935326207520207183253 759325093415977509711715)
                    ·
                      rfl

theorem cell23_4436341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_4436341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436341 prefixEnd_4436341 := by exact prefixLift 4436341
  have htrace : WordTrace (prefixWord ++ tailWord_4436341) baseStart_4436341 baseEnd_4436341 := by
    simpa [prefixWord, tailWord_4436341, baseEnd_4436341] using wordTrace_append hprefix tailTrace_4436341
  have hstable : (prefixWord ++ tailWord_4436341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436341).length < 2 ^ (prefixWord ++ tailWord_4436341).sum := by decide
  have hdescent : baseEnd_4436341 < baseStart_4436341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436342 : List Nat := [5, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3]
def baseStart_4436342 : Nat := 118140960795 + 4436342 * 2 ^ 59
def prefixEnd_4436342 : Nat := 4983230072969 + 3 ^ 40 * 4436342 * 2
def baseEnd_4436342 : Nat := 2277975793728587025222641

theorem tailTrace_4436342 : CollatzResearch.WordTrace tailWord_4436342 prefixEnd_4436342 2277975793728587025222641 := by
  unfold tailWord_4436342
  simp only [CollatzResearch.WordTrace]
  refine ⟨10112917855868629733610455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107871123795932050491844853 10112917855868629733610455)
  ·
    refine ⟨15169376783802944600415683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10112917855868629733610455 15169376783802944600415683)
    ·
      refine ⟨22754065175704416900623525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15169376783802944600415683 22754065175704416900623525)
      ·
        refine ⟨4266387220444578168866911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22754065175704416900623525 4266387220444578168866911)
        ·
          refine ⟨6399580830666867253300367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4266387220444578168866911 6399580830666867253300367)
          ·
            refine ⟨9599371246000300879950551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6399580830666867253300367 9599371246000300879950551)
            ·
              refine ⟨14399056869000451319925827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9599371246000300879950551 14399056869000451319925827)
              ·
                refine ⟨21598585303500676979888741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14399056869000451319925827 21598585303500676979888741)
                ·
                  refine ⟨4049734744406376933729139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21598585303500676979888741 4049734744406376933729139)
                  ·
                    refine ⟨6074602116609565400593709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4049734744406376933729139 6074602116609565400593709)
                    ·
                      refine ⟨2277975793728587025222641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6074602116609565400593709 2277975793728587025222641)
                      ·
                        rfl

theorem cell23_4436342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_4436342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436342 prefixEnd_4436342 := by exact prefixLift 4436342
  have htrace : WordTrace (prefixWord ++ tailWord_4436342) baseStart_4436342 baseEnd_4436342 := by
    simpa [prefixWord, tailWord_4436342, baseEnd_4436342] using wordTrace_append hprefix tailTrace_4436342
  have hstable : (prefixWord ++ tailWord_4436342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436342).length < 2 ^ (prefixWord ++ tailWord_4436342).sum := by decide
  have hdescent : baseEnd_4436342 < baseStart_4436342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436361 : List Nat := [1, 2, 1, 1, 6, 1, 2, 1, 2, 2, 4]
def baseStart_4436361 : Nat := 118140960795 + 4436361 * 2 ^ 59
def prefixEnd_4436361 : Nat := 4983230072969 + 3 ^ 40 * 4436361 * 2
def baseEnd_4436361 : Nat := 2277985549861022450885053

theorem tailTrace_4436361 : CollatzResearch.WordTrace tailWord_4436361 prefixEnd_4436361 2277985549861022450885053 := by
  unfold tailWord_4436361
  simp only [CollatzResearch.WordTrace]
  refine ⟨161807378680829241982708937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107871585787219494655139291 161807378680829241982708937)
  ·
    refine ⟨121355534010621931487031703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161807378680829241982708937 121355534010621931487031703)
    ·
      refine ⟨182033301015932897230547555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121355534010621931487031703 182033301015932897230547555)
      ·
        refine ⟨273049951523899345845821333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182033301015932897230547555 273049951523899345845821333)
        ·
          refine ⟨12799216477682781836522875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 273049951523899345845821333 12799216477682781836522875)
          ·
            refine ⟨19198824716524172754784313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12799216477682781836522875 19198824716524172754784313)
            ·
              refine ⟨14399118537393129566088235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19198824716524172754784313 14399118537393129566088235)
              ·
                refine ⟨21598677806089694349132353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14399118537393129566088235 21598677806089694349132353)
                ·
                  refine ⟨16199008354567270761849265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21598677806089694349132353 16199008354567270761849265)
                  ·
                    refine ⟨12149256265925453071386949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16199008354567270761849265 12149256265925453071386949)
                    ·
                      refine ⟨2277985549861022450885053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12149256265925453071386949 2277985549861022450885053)
                      ·
                        rfl

theorem cell23_4436361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 2, 4].length) (baseStart_4436361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436361 prefixEnd_4436361 := by exact prefixLift 4436361
  have htrace : WordTrace (prefixWord ++ tailWord_4436361) baseStart_4436361 baseEnd_4436361 := by
    simpa [prefixWord, tailWord_4436361, baseEnd_4436361] using wordTrace_append hprefix tailTrace_4436361
  have hstable : (prefixWord ++ tailWord_4436361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436361).length < 2 ^ (prefixWord ++ tailWord_4436361).sum := by decide
  have hdescent : baseEnd_4436361 < baseStart_4436361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436382 : List Nat := [4, 3, 1, 2, 1, 1, 1, 2, 4, 2, 2]
def baseStart_4436382 : Nat := 118140960795 + 4436382 * 2 ^ 59
def prefixEnd_4436382 : Nat := 4983230072969 + 3 ^ 40 * 4436382 * 2
def baseEnd_4436382 : Nat := 2277996332954766868722457

theorem tailTrace_4436382 : CollatzResearch.WordTrace tailWord_4436382 prefixEnd_4436382 2277996332954766868722457 := by
  unfold tailWord_4436382
  simp only [CollatzResearch.WordTrace]
  refine ⟨20226018076719145321152925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107872096409168775046148933 20226018076719145321152925)
  ·
    refine ⟨7584756778769679495432347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20226018076719145321152925 7584756778769679495432347)
    ·
      refine ⟨11377135168154519243148521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7584756778769679495432347 11377135168154519243148521)
      ·
        refine ⟨8532851376115889432361391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11377135168154519243148521 8532851376115889432361391)
        ·
          refine ⟨12799277064173834148542087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8532851376115889432361391 12799277064173834148542087)
          ·
            refine ⟨19198915596260751222813131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12799277064173834148542087 19198915596260751222813131)
            ·
              refine ⟨28798373394391126834219697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19198915596260751222813131 28798373394391126834219697)
              ·
                refine ⟨21598780045793345125664773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28798373394391126834219697 21598780045793345125664773)
                ·
                  refine ⟨4049771258586252211062145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21598780045793345125664773 4049771258586252211062145)
                  ·
                    refine ⟨3037328443939689158296609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4049771258586252211062145 3037328443939689158296609)
                    ·
                      refine ⟨2277996332954766868722457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3037328443939689158296609 2277996332954766868722457)
                      ·
                        rfl

theorem cell23_4436382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_4436382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436382 prefixEnd_4436382 := by exact prefixLift 4436382
  have htrace : WordTrace (prefixWord ++ tailWord_4436382) baseStart_4436382 baseEnd_4436382 := by
    simpa [prefixWord, tailWord_4436382, baseEnd_4436382] using wordTrace_append hprefix tailTrace_4436382
  have hstable : (prefixWord ++ tailWord_4436382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436382).length < 2 ^ (prefixWord ++ tailWord_4436382).sum := by decide
  have hdescent : baseEnd_4436382 < baseStart_4436382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436388 : List Nat := [2, 3, 1, 2, 1, 1, 5, 3, 5]
def baseStart_4436388 : Nat := 118140960795 + 4436388 * 2 ^ 59
def prefixEnd_4436388 : Nat := 4983230072969 + 3 ^ 40 * 4436388 * 2
def baseEnd_4436388 : Nat := 253111045982077093916381

theorem tailTrace_4436388 : CollatzResearch.WordTrace tailWord_4436388 prefixEnd_4436388 253111045982077093916381 := by
  unfold tailWord_4436388
  simp only [CollatzResearch.WordTrace]
  refine ⟨80904181725865712796970909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107872242301154283729294545 80904181725865712796970909)
  ·
    refine ⟨30339068147199642298864091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80904181725865712796970909 30339068147199642298864091)
    ·
      refine ⟨45508602220799463448296137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30339068147199642298864091 45508602220799463448296137)
      ·
        refine ⟨34131451665599597586222103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45508602220799463448296137 34131451665599597586222103)
        ·
          refine ⟨51197177498399396379333155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34131451665599597586222103 51197177498399396379333155)
          ·
            refine ⟨76795766247599094568999733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51197177498399396379333155 76795766247599094568999733)
            ·
              refine ⟨7199603085712415115843725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76795766247599094568999733 7199603085712415115843725)
              ·
                refine ⟨2699851157142155668441397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7199603085712415115843725 2699851157142155668441397)
                ·
                  refine ⟨253111045982077093916381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2699851157142155668441397 253111045982077093916381)
                  ·
                    rfl

theorem cell23_4436388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 3, 5].length) (baseStart_4436388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436388 prefixEnd_4436388 := by exact prefixLift 4436388
  have htrace : WordTrace (prefixWord ++ tailWord_4436388) baseStart_4436388 baseEnd_4436388 := by
    simpa [prefixWord, tailWord_4436388, baseEnd_4436388] using wordTrace_append hprefix tailTrace_4436388
  have hstable : (prefixWord ++ tailWord_4436388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436388).length < 2 ^ (prefixWord ++ tailWord_4436388).sum := by decide
  have hdescent : baseEnd_4436388 < baseStart_4436388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436401 : List Nat := [1, 2, 2, 4, 1, 2, 1, 1, 4, 5]
def baseStart_4436401 : Nat := 118140960795 + 4436401 * 2 ^ 59
def prefixEnd_4436401 : Nat := 4983230072969 + 3 ^ 40 * 4436401 * 2
def baseEnd_4436401 : Nat := 759335363029067431461623

theorem tailTrace_4436401 : CollatzResearch.WordTrace tailWord_4436401 prefixEnd_4436401 759335363029067431461623 := by
  unfold tailWord_4436401
  simp only [CollatzResearch.WordTrace]
  refine ⟨161808837600684328814165057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107872558400456219209443371 161808837600684328814165057)
  ·
    refine ⟨121356628200513246610623793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161808837600684328814165057 121356628200513246610623793)
    ·
      refine ⟨91017471150384934957967845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121356628200513246610623793 91017471150384934957967845)
      ·
        refine ⟨17065775840697175304618971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91017471150384934957967845 17065775840697175304618971)
        ·
          refine ⟨25598663761045762956928457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17065775840697175304618971 25598663761045762956928457)
          ·
            refine ⟨19198997820784322217696343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25598663761045762956928457 19198997820784322217696343)
            ·
              refine ⟨28798496731176483326544515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19198997820784322217696343 28798496731176483326544515)
              ·
                refine ⟨43197745096764724989816773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28798496731176483326544515 43197745096764724989816773)
                ·
                  refine ⟨8099577205643385935590645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43197745096764724989816773 8099577205643385935590645)
                  ·
                    refine ⟨759335363029067431461623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8099577205643385935590645 759335363029067431461623)
                    ·
                      rfl

theorem cell23_4436401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 5].length) (baseStart_4436401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436401 prefixEnd_4436401 := by exact prefixLift 4436401
  have htrace : WordTrace (prefixWord ++ tailWord_4436401) baseStart_4436401 baseEnd_4436401 := by
    simpa [prefixWord, tailWord_4436401, baseEnd_4436401] using wordTrace_append hprefix tailTrace_4436401
  have hstable : (prefixWord ++ tailWord_4436401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436401).length < 2 ^ (prefixWord ++ tailWord_4436401).sum := by decide
  have hdescent : baseEnd_4436401 < baseStart_4436401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436405 : List Nat := [1, 3, 3, 2, 4, 1, 1, 1, 7]
def baseStart_4436405 : Nat := 118140960795 + 4436405 * 2 ^ 59
def prefixEnd_4436405 : Nat := 4983230072969 + 3 ^ 40 * 4436405 * 2
def baseEnd_4436405 : Nat := 253112015889980030970539

theorem tailTrace_4436405 : CollatzResearch.WordTrace tailWord_4436405 prefixEnd_4436405 253112015889980030970539 := by
  unfold tailWord_4436405
  simp only [CollatzResearch.WordTrace]
  refine ⟨161808983492669837497310669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107872655661779891664873779 161808983492669837497310669)
  ·
    refine ⟨60678368809751189061491501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161808983492669837497310669 60678368809751189061491501)
    ·
      refine ⟨22754388303656695898059313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60678368809751189061491501 22754388303656695898059313)
      ·
        refine ⟨17065791227742521923544485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22754388303656695898059313 17065791227742521923544485)
        ·
          refine ⟨3199835855201722860664591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17065791227742521923544485 3199835855201722860664591)
          ·
            refine ⟨4799753782802584290996887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3199835855201722860664591 4799753782802584290996887)
            ·
              refine ⟨7199630674203876436495331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4799753782802584290996887 7199630674203876436495331)
              ·
                refine ⟨10799446011305814654742997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7199630674203876436495331 10799446011305814654742997)
                ·
                  refine ⟨253112015889980030970539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10799446011305814654742997 253112015889980030970539)
                  ·
                    rfl

theorem cell23_4436405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 7].length) (baseStart_4436405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436405 prefixEnd_4436405 := by exact prefixLift 4436405
  have htrace : WordTrace (prefixWord ++ tailWord_4436405) baseStart_4436405 baseEnd_4436405 := by
    simpa [prefixWord, tailWord_4436405, baseEnd_4436405] using wordTrace_append hprefix tailTrace_4436405
  have hstable : (prefixWord ++ tailWord_4436405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436405).length < 2 ^ (prefixWord ++ tailWord_4436405).sum := by decide
  have hdescent : baseEnd_4436405 < baseStart_4436405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436431 : List Nat := [1, 1, 2, 1, 1, 4, 1, 3, 5, 4]
def baseStart_4436431 : Nat := 118140960795 + 4436431 * 2 ^ 59
def prefixEnd_4436431 : Nat := 4983230072969 + 3 ^ 40 * 4436431 * 2
def baseEnd_4436431 : Nat := 759340497835612392336577

theorem tailTrace_4436431 : CollatzResearch.WordTrace tailWord_4436431 prefixEnd_4436431 759340497835612392336577 := by
  unfold tailWord_4436431
  simp only [CollatzResearch.WordTrace]
  refine ⟨161809931790575643937757147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107873287860383762625171431 161809931790575643937757147)
  ·
    refine ⟨242714897685863465906635721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161809931790575643937757147 242714897685863465906635721)
    ·
      refine ⟨182036173264397599429976791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242714897685863465906635721 182036173264397599429976791)
      ·
        refine ⟨273054259896596399144965187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182036173264397599429976791 273054259896596399144965187)
        ·
          refine ⟨409581389844894598717447781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273054259896596399144965187 409581389844894598717447781)
          ·
            refine ⟨76796510595917737259521459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 409581389844894598717447781 76796510595917737259521459)
            ·
              refine ⟨115194765893876605889282189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76796510595917737259521459 115194765893876605889282189)
              ·
                refine ⟨43198037210203727208480821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115194765893876605889282189 43198037210203727208480821)
                ·
                  refine ⟨4049815988456599425795077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43198037210203727208480821 4049815988456599425795077)
                  ·
                    refine ⟨759340497835612392336577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4049815988456599425795077 759340497835612392336577)
                    ·
                      rfl

theorem cell23_4436431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 5, 4].length) (baseStart_4436431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436431 prefixEnd_4436431 := by exact prefixLift 4436431
  have htrace : WordTrace (prefixWord ++ tailWord_4436431) baseStart_4436431 baseEnd_4436431 := by
    simpa [prefixWord, tailWord_4436431, baseEnd_4436431] using wordTrace_append hprefix tailTrace_4436431
  have hstable : (prefixWord ++ tailWord_4436431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436431).length < 2 ^ (prefixWord ++ tailWord_4436431).sum := by decide
  have hdescent : baseEnd_4436431 < baseStart_4436431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436465 : List Nat := [1, 2, 2, 2, 3, 1, 3, 4, 1, 4]
def baseStart_4436465 : Nat := 118140960795 + 4436465 * 2 ^ 59
def prefixEnd_4436465 : Nat := 4983230072969 + 3 ^ 40 * 4436465 * 2
def baseEnd_4436465 : Nat := 759346317283030014661525

theorem tailTrace_4436465 : CollatzResearch.WordTrace tailWord_4436465 prefixEnd_4436465 759346317283030014661525 := by
  unfold tailWord_4436465
  simp only [CollatzResearch.WordTrace]
  refine ⟨161811171872452467744494849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107874114581634978496329899 161811171872452467744494849)
  ·
    refine ⟨121358378904339350808371137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161811171872452467744494849 121358378904339350808371137)
    ·
      refine ⟨91018784178254513106278353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121358378904339350808371137 91018784178254513106278353)
      ·
        refine ⟨68264088133690884829708765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91018784178254513106278353 68264088133690884829708765)
        ·
          refine ⟨25599033050134081811140787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68264088133690884829708765 25599033050134081811140787)
          ·
            refine ⟨38398549575201122716711181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25599033050134081811140787 38398549575201122716711181)
            ·
              refine ⟨14399456090700421018766693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38398549575201122716711181 14399456090700421018766693)
              ·
                refine ⟨2699898017006328941018755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14399456090700421018766693 2699898017006328941018755)
                ·
                  refine ⟨4049847025509493411528133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2699898017006328941018755 4049847025509493411528133)
                  ·
                    refine ⟨759346317283030014661525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4049847025509493411528133 759346317283030014661525)
                    ·
                      rfl

theorem cell23_4436465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 4, 1, 4].length) (baseStart_4436465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436465 prefixEnd_4436465 := by exact prefixLift 4436465
  have htrace : WordTrace (prefixWord ++ tailWord_4436465) baseStart_4436465 baseEnd_4436465 := by
    simpa [prefixWord, tailWord_4436465, baseEnd_4436465] using wordTrace_append hprefix tailTrace_4436465
  have hstable : (prefixWord ++ tailWord_4436465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436465).length < 2 ^ (prefixWord ++ tailWord_4436465).sum := by decide
  have hdescent : baseEnd_4436465 < baseStart_4436465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436482 : List Nat := [3, 4, 1, 2, 2, 1, 1, 2, 3, 4]
def baseStart_4436482 : Nat := 118140960795 + 4436482 * 2 ^ 59
def prefixEnd_4436482 : Nat := 4983230072969 + 3 ^ 40 * 4436482 * 2
def baseEnd_4436482 : Nat := 759349227006738825823999

theorem tailTrace_4436482 : CollatzResearch.WordTrace tailWord_4436482 prefixEnd_4436482 759349227006738825823999 := by
  unfold tailWord_4436482
  simp only [CollatzResearch.WordTrace]
  refine ⟨40452947978347719911965925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107874527942260586431909133 40452947978347719911965925)
  ·
    refine ⟨7584927745940197483493611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40452947978347719911965925 7584927745940197483493611)
    ·
      refine ⟨11377391618910296225240417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7584927745940197483493611 11377391618910296225240417)
      ·
        refine ⟨8533043714182722168930313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11377391618910296225240417 8533043714182722168930313)
        ·
          refine ⟨6399782785637041626697735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8533043714182722168930313 6399782785637041626697735)
          ·
            refine ⟨9599674178455562440046603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6399782785637041626697735 9599674178455562440046603)
            ·
              refine ⟨14399511267683343660069905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9599674178455562440046603 14399511267683343660069905)
              ·
                refine ⟨10799633450762507745052429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14399511267683343660069905 10799633450762507745052429)
                ·
                  refine ⟨4049862544035940404394661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10799633450762507745052429 4049862544035940404394661)
                  ·
                    refine ⟨759349227006738825823999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4049862544035940404394661 759349227006738825823999)
                    ·
                      rfl

theorem cell23_4436482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_4436482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436482 prefixEnd_4436482 := by exact prefixLift 4436482
  have htrace : WordTrace (prefixWord ++ tailWord_4436482) baseStart_4436482 baseEnd_4436482 := by
    simpa [prefixWord, tailWord_4436482, baseEnd_4436482] using wordTrace_append hprefix tailTrace_4436482
  have hstable : (prefixWord ++ tailWord_4436482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436482).length < 2 ^ (prefixWord ++ tailWord_4436482).sum := by decide
  have hdescent : baseEnd_4436482 < baseStart_4436482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436512 : List Nat := [2, 1, 1, 6, 3, 1, 1, 2, 6]
def baseStart_4436512 : Nat := 118140960795 + 4436512 * 2 ^ 59
def prefixEnd_4436512 : Nat := 4983230072969 + 3 ^ 40 * 4436512 * 2
def baseEnd_4436512 : Nat := 253118120604427928899651

theorem tailTrace_4436512 : CollatzResearch.WordTrace tailWord_4436512 prefixEnd_4436512 253118120604427928899651 := by
  unfold tailWord_4436512
  simp only [CollatzResearch.WordTrace]
  refine ⟨80906443051641097385727895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107875257402188129847637193 80906443051641097385727895)
  ·
    refine ⟨121359664577461646078591843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80906443051641097385727895 121359664577461646078591843)
    ·
      refine ⟨182039496866192469117887765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121359664577461646078591843 182039496866192469117887765)
      ·
        refine ⟨8533101415602771989900989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 182039496866192469117887765 8533101415602771989900989)
        ·
          refine ⟨3199913030851039496212871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8533101415602771989900989 3199913030851039496212871)
          ·
            refine ⟨4799869546276559244319307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3199913030851039496212871 4799869546276559244319307)
            ·
              refine ⟨7199804319414838866478961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4799869546276559244319307 7199804319414838866478961)
              ·
                refine ⟨5399853239561129149859221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7199804319414838866478961 5399853239561129149859221)
                ·
                  refine ⟨253118120604427928899651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5399853239561129149859221 253118120604427928899651)
                  ·
                    rfl

theorem cell23_4436512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 6].length) (baseStart_4436512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436512 prefixEnd_4436512 := by exact prefixLift 4436512
  have htrace : WordTrace (prefixWord ++ tailWord_4436512) baseStart_4436512 baseEnd_4436512 := by
    simpa [prefixWord, tailWord_4436512, baseEnd_4436512] using wordTrace_append hprefix tailTrace_4436512
  have hstable : (prefixWord ++ tailWord_4436512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436512).length < 2 ^ (prefixWord ++ tailWord_4436512).sum := by decide
  have hdescent : baseEnd_4436512 < baseStart_4436512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436522 : List Nat := [3, 1, 4, 1, 1, 3, 2, 1, 3, 1, 3]
def baseStart_4436522 : Nat := 118140960795 + 4436522 * 2 ^ 59
def prefixEnd_4436522 : Nat := 4983230072969 + 3 ^ 40 * 4436522 * 2
def baseEnd_4436522 : Nat := 2278068220246396320971813

theorem tailTrace_4436522 : CollatzResearch.WordTrace tailWord_4436522 prefixEnd_4436522 2278068220246396320971813 := by
  unfold tailWord_4436522
  simp only [CollatzResearch.WordTrace]
  refine ⟨40453312708311491619829955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107875500555497310986213213 40453312708311491619829955)
  ·
    refine ⟨60679969062467237429744933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40453312708311491619829955 60679969062467237429744933)
    ·
      refine ⟨11377494199212607018077175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60679969062467237429744933 11377494199212607018077175)
      ·
        refine ⟨17066241298818910527115763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11377494199212607018077175 17066241298818910527115763)
        ·
          refine ⟨25599361948228365790673645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17066241298818910527115763 25599361948228365790673645)
          ·
            refine ⟨9599760730585637171502617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25599361948228365790673645 9599760730585637171502617)
            ·
              refine ⟨7199820547939227878626963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9599760730585637171502617 7199820547939227878626963)
              ·
                refine ⟨10799730821908841817940445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7199820547939227878626963 10799730821908841817940445)
                ·
                  refine ⟨4049899058215815681727667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10799730821908841817940445 4049899058215815681727667)
                  ·
                    refine ⟨6074848587323723522591501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4049899058215815681727667 6074848587323723522591501)
                    ·
                      refine ⟨2278068220246396320971813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6074848587323723522591501 2278068220246396320971813)
                      ·
                        rfl

theorem cell23_4436522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_4436522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436522 prefixEnd_4436522 := by exact prefixLift 4436522
  have htrace : WordTrace (prefixWord ++ tailWord_4436522) baseStart_4436522 baseEnd_4436522 := by
    simpa [prefixWord, tailWord_4436522, baseEnd_4436522] using wordTrace_append hprefix tailTrace_4436522
  have hstable : (prefixWord ++ tailWord_4436522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436522).length < 2 ^ (prefixWord ++ tailWord_4436522).sum := by decide
  have hdescent : baseEnd_4436522 < baseStart_4436522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436538 : List Nat := [3, 1, 1, 1, 3, 3, 3, 1, 1, 6]
def baseStart_4436538 : Nat := 118140960795 + 4436538 * 2 ^ 59
def prefixEnd_4436538 : Nat := 4983230072969 + 3 ^ 40 * 4436538 * 2
def baseEnd_4436538 : Nat := 759358811978956086123913

theorem tailTrace_4436538 : CollatzResearch.WordTrace tailWord_4436538 prefixEnd_4436538 759358811978956086123913 := by
  unfold tailWord_4436538
  simp only [CollatzResearch.WordTrace]
  refine ⟨40453458600297000302975567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107875889600792000807934845 40453458600297000302975567)
  ·
    refine ⟨60680187900445500454463351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40453458600297000302975567 60680187900445500454463351)
    ·
      refine ⟨91020281850668250681695027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60680187900445500454463351 91020281850668250681695027)
      ·
        refine ⟨136530422776002376022542541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91020281850668250681695027 136530422776002376022542541)
        ·
          refine ⟨51198908541000891008453453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136530422776002376022542541 51198908541000891008453453)
          ·
            refine ⟨19199590702875334128170045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51198908541000891008453453 19199590702875334128170045)
            ·
              refine ⟨7199846513578250298063767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19199590702875334128170045 7199846513578250298063767)
              ·
                refine ⟨10799769770367375447095651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7199846513578250298063767 10799769770367375447095651)
                ·
                  refine ⟨16199654655551063170643477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10799769770367375447095651 16199654655551063170643477)
                  ·
                    refine ⟨759358811978956086123913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16199654655551063170643477 759358811978956086123913)
                    ·
                      rfl

theorem cell23_4436538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 1, 6].length) (baseStart_4436538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436538 prefixEnd_4436538 := by exact prefixLift 4436538
  have htrace : WordTrace (prefixWord ++ tailWord_4436538) baseStart_4436538 baseEnd_4436538 := by
    simpa [prefixWord, tailWord_4436538, baseEnd_4436538] using wordTrace_append hprefix tailTrace_4436538
  have hstable : (prefixWord ++ tailWord_4436538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436538).length < 2 ^ (prefixWord ++ tailWord_4436538).sum := by decide
  have hdescent : baseEnd_4436538 < baseStart_4436538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436545 : List Nat := [1, 2, 5, 1, 1, 2, 1, 4, 1, 1, 4]
def baseStart_4436545 : Nat := 118140960795 + 4436545 * 2 ^ 59
def prefixEnd_4436545 : Nat := 4983230072969 + 3 ^ 40 * 4436545 * 2
def baseEnd_4436545 : Nat := 2278080030301449730984207

theorem tailTrace_4436545 : CollatzResearch.WordTrace tailWord_4436545 prefixEnd_4436545 2278080030301449730984207 := by
  unfold tailWord_4436545
  simp only [CollatzResearch.WordTrace]
  refine ⟨161814089712162641407407089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107876059808108427604938059 161814089712162641407407089)
  ·
    refine ⟨121360567284121981055555317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161814089712162641407407089 121360567284121981055555317)
    ·
      refine ⟨11377553182886435723958311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 121360567284121981055555317 11377553182886435723958311)
      ·
        refine ⟨17066329774329653585937467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11377553182886435723958311 17066329774329653585937467)
        ·
          refine ⟨25599494661494480378906201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17066329774329653585937467 25599494661494480378906201)
          ·
            refine ⟨19199620996120860284179651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25599494661494480378906201 19199620996120860284179651)
            ·
              refine ⟨28799431494181290426269477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19199620996120860284179651 28799431494181290426269477)
              ·
                refine ⟨5399893405158991954925527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28799431494181290426269477 5399893405158991954925527)
                ·
                  refine ⟨8099840107738487932388291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5399893405158991954925527 8099840107738487932388291)
                  ·
                    refine ⟨12149760161607731898582437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8099840107738487932388291 12149760161607731898582437)
                    ·
                      refine ⟨2278080030301449730984207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12149760161607731898582437 2278080030301449730984207)
                      ·
                        rfl

theorem cell23_4436545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_4436545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436545 prefixEnd_4436545 := by exact prefixLift 4436545
  have htrace : WordTrace (prefixWord ++ tailWord_4436545) baseStart_4436545 baseEnd_4436545 := by
    simpa [prefixWord, tailWord_4436545, baseEnd_4436545] using wordTrace_append hprefix tailTrace_4436545
  have hstable : (prefixWord ++ tailWord_4436545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436545).length < 2 ^ (prefixWord ++ tailWord_4436545).sum := by decide
  have hdescent : baseEnd_4436545 < baseStart_4436545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436558 : List Nat := [4, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4]
def baseStart_4436558 : Nat := 118140960795 + 4436558 * 2 ^ 59
def prefixEnd_4436558 : Nat := 4983230072969 + 3 ^ 40 * 4436558 * 2
def baseEnd_4436558 : Nat := 2278086705549958180121647

theorem tailTrace_4436558 : CollatzResearch.WordTrace tailWord_4436558 prefixEnd_4436558 2278086705549958180121647 := by
  unfold tailWord_4436558
  simp only [CollatzResearch.WordTrace]
  refine ⟨20226820482639443078453791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107876375907410363085086885 20226820482639443078453791)
  ·
    refine ⟨30340230723959164617680687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20226820482639443078453791 30340230723959164617680687)
    ·
      refine ⟨45510346085938746926521031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30340230723959164617680687 45510346085938746926521031)
      ·
        refine ⟨68265519128908120389781547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45510346085938746926521031 68265519128908120389781547)
        ·
          refine ⟨102398278693362180584672321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68265519128908120389781547 102398278693362180584672321)
          ·
            refine ⟨76798709020021635438504241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102398278693362180584672321 76798709020021635438504241)
            ·
              refine ⟨57599031765016226578878181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76798709020021635438504241 57599031765016226578878181)
              ·
                refine ⟨10799818455940542483539659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57599031765016226578878181 10799818455940542483539659)
                ·
                  refine ⟨16199727683910813725309489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10799818455940542483539659 16199727683910813725309489)
                  ·
                    refine ⟨12149795762933110293982117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16199727683910813725309489 12149795762933110293982117)
                    ·
                      refine ⟨2278086705549958180121647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12149795762933110293982117 2278086705549958180121647)
                      ·
                        rfl

theorem cell23_4436558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_4436558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436558 prefixEnd_4436558 := by exact prefixLift 4436558
  have htrace : WordTrace (prefixWord ++ tailWord_4436558) baseStart_4436558 baseEnd_4436558 := by
    simpa [prefixWord, tailWord_4436558, baseEnd_4436558] using wordTrace_append hprefix tailTrace_4436558
  have hstable : (prefixWord ++ tailWord_4436558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436558).length < 2 ^ (prefixWord ++ tailWord_4436558).sum := by decide
  have hdescent : baseEnd_4436558 < baseStart_4436558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436565 : List Nat := [1, 3, 2, 2, 1, 1, 4, 3, 1, 2, 3]
def baseStart_4436565 : Nat := 118140960795 + 4436565 * 2 ^ 59
def prefixEnd_4436565 : Nat := 4983230072969 + 3 ^ 40 * 4436565 * 2
def baseEnd_4436565 : Nat := 2278090299914539652734115

theorem tailTrace_4436565 : CollatzResearch.WordTrace tailWord_4436565 prefixEnd_4436565 2278090299914539652734115 := by
  unfold tailWord_4436565
  simp only [CollatzResearch.WordTrace]
  refine ⟨161814819172090184823135149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107876546114726789882090099 161814819172090184823135149)
  ·
    refine ⟨60680557189533819308675681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161814819172090184823135149 60680557189533819308675681)
    ·
      refine ⟨45510417892150364481506761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60680557189533819308675681 45510417892150364481506761)
      ·
        refine ⟨34132813419112773361130071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45510417892150364481506761 34132813419112773361130071)
        ·
          refine ⟨51199220128669160041695107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34132813419112773361130071 51199220128669160041695107)
          ·
            refine ⟨76798830193003740062542661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51199220128669160041695107 76798830193003740062542661)
            ·
              refine ⟨14399780661188201261726749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76798830193003740062542661 14399780661188201261726749)
              ·
                refine ⟨5399917747945575473147531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14399780661188201261726749 5399917747945575473147531)
                ·
                  refine ⟨8099876621918363209721297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5399917747945575473147531 8099876621918363209721297)
                  ·
                    refine ⟨6074907466438772407290973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8099876621918363209721297 6074907466438772407290973)
                    ·
                      refine ⟨2278090299914539652734115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6074907466438772407290973 2278090299914539652734115)
                      ·
                        rfl

theorem cell23_4436565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_4436565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436565 prefixEnd_4436565 := by exact prefixLift 4436565
  have htrace : WordTrace (prefixWord ++ tailWord_4436565) baseStart_4436565 baseEnd_4436565 := by
    simpa [prefixWord, tailWord_4436565, baseEnd_4436565] using wordTrace_append hprefix tailTrace_4436565
  have hstable : (prefixWord ++ tailWord_4436565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436565).length < 2 ^ (prefixWord ++ tailWord_4436565).sum := by decide
  have hdescent : baseEnd_4436565 < baseStart_4436565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436589 : List Nat := [1, 5, 1, 1, 3, 3, 2, 1, 2, 4]
def baseStart_4436589 : Nat := 118140960795 + 4436589 * 2 ^ 59
def prefixEnd_4436589 : Nat := 4983230072969 + 3 ^ 40 * 4436589 * 2
def baseEnd_4436589 : Nat := 759367541150082519611335

theorem tailTrace_4436589 : CollatzResearch.WordTrace tailWord_4436589 prefixEnd_4436589 759367541150082519611335 := by
  unfold tailWord_4436589
  simp only [CollatzResearch.WordTrace]
  refine ⟨161815694524003236922008821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107877129682668824614672547 161815694524003236922008821)
  ·
    refine ⟨15170221361625303461438327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 161815694524003236922008821 15170221361625303461438327)
    ·
      refine ⟨22755332042437955192157491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15170221361625303461438327 22755332042437955192157491)
      ·
        refine ⟨34132998063656932788236237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22755332042437955192157491 34132998063656932788236237)
        ·
          refine ⟨12799874273871349795588589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34132998063656932788236237 12799874273871349795588589)
          ·
            refine ⟨4799952852701756173345721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12799874273871349795588589 4799952852701756173345721)
            ·
              refine ⟨3599964639526317130009291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4799952852701756173345721 3599964639526317130009291)
              ·
                refine ⟨5399946959289475695013937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3599964639526317130009291 5399946959289475695013937)
                ·
                  refine ⟨4049960219467106771260453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5399946959289475695013937 4049960219467106771260453)
                  ·
                    refine ⟨759367541150082519611335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4049960219467106771260453 759367541150082519611335)
                    ·
                      rfl

theorem cell23_4436589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_4436589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436589 prefixEnd_4436589 := by exact prefixLift 4436589
  have htrace : WordTrace (prefixWord ++ tailWord_4436589) baseStart_4436589 baseEnd_4436589 := by
    simpa [prefixWord, tailWord_4436589, baseEnd_4436589] using wordTrace_append hprefix tailTrace_4436589
  have hstable : (prefixWord ++ tailWord_4436589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436589).length < 2 ^ (prefixWord ++ tailWord_4436589).sum := by decide
  have hdescent : baseEnd_4436589 < baseStart_4436589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436686 : List Nat := [4, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2]
def baseStart_4436686 : Nat := 118140960795 + 4436686 * 2 ^ 59
def prefixEnd_4436686 : Nat := 4983230072969 + 3 ^ 40 * 4436686 * 2
def baseEnd_4436686 : Nat := 2278152431073733679321059

theorem tailTrace_4436686 : CollatzResearch.WordTrace tailWord_4436686 prefixEnd_4436686 2278152431073733679321059 := by
  unfold tailWord_4436686
  simp only [CollatzResearch.WordTrace]
  refine ⟨20227404050581477811036239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107879488269767881658859941 20227404050581477811036239)
  ·
    refine ⟨30341106075872216716554359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20227404050581477811036239 30341106075872216716554359)
    ·
      refine ⟨45511659113808325074831539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30341106075872216716554359 45511659113808325074831539)
      ·
        refine ⟨68267488670712487612247309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45511659113808325074831539 68267488670712487612247309)
        ·
          refine ⟨25600308251517182854592741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68267488670712487612247309 25600308251517182854592741)
          ·
            refine ⟨4800057797159471785236139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25600308251517182854592741 4800057797159471785236139)
            ·
              refine ⟨7200086695739207677854209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4800057797159471785236139 7200086695739207677854209)
              ·
                refine ⟨5400065021804405758390657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7200086695739207677854209 5400065021804405758390657)
                ·
                  refine ⟨4050048766353304318792993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5400065021804405758390657 4050048766353304318792993)
                  ·
                    refine ⟨3037536574764978239094745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4050048766353304318792993 3037536574764978239094745)
                    ·
                      refine ⟨2278152431073733679321059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3037536574764978239094745 2278152431073733679321059)
                      ·
                        rfl

theorem cell23_4436686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2].length) (baseStart_4436686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436686 prefixEnd_4436686 := by exact prefixLift 4436686
  have htrace : WordTrace (prefixWord ++ tailWord_4436686) baseStart_4436686 baseEnd_4436686 := by
    simpa [prefixWord, tailWord_4436686, baseEnd_4436686] using wordTrace_append hprefix tailTrace_4436686
  have hstable : (prefixWord ++ tailWord_4436686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436686).length < 2 ^ (prefixWord ++ tailWord_4436686).sum := by decide
  have hdescent : baseEnd_4436686 < baseStart_4436686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436692 : List Nat := [2, 4, 1, 3, 2, 1, 2, 1, 7]
def baseStart_4436692 : Nat := 118140960795 + 4436692 * 2 ^ 59
def prefixEnd_4436692 : Nat := 4983230072969 + 3 ^ 40 * 4436692 * 2
def baseEnd_4436692 : Nat := 253128390217517850649559

theorem tailTrace_4436692 : CollatzResearch.WordTrace tailWord_4436692 prefixEnd_4436692 253128390217517850649559 := by
  unfold tailWord_4436692
  simp only [CollatzResearch.WordTrace]
  refine ⟨80909725621315042756504165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107879634161753390342005553 80909725621315042756504165)
  ·
    refine ⟨15170573553996570516844531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80909725621315042756504165 15170573553996570516844531)
    ·
      refine ⟨22755860330994855775266797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15170573553996570516844531 22755860330994855775266797)
      ·
        refine ⟨8533447624123070915725049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22755860330994855775266797 8533447624123070915725049)
        ·
          refine ⟨6400085718092303186793787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8533447624123070915725049 6400085718092303186793787)
          ·
            refine ⟨9600128577138454780190681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6400085718092303186793787 9600128577138454780190681)
            ·
              refine ⟨7200096432853841085143011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9600128577138454780190681 7200096432853841085143011)
              ·
                refine ⟨10800144649280761627714517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7200096432853841085143011 10800144649280761627714517)
                ·
                  refine ⟨253128390217517850649559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10800144649280761627714517 253128390217517850649559)
                  ·
                    rfl

theorem cell23_4436692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_4436692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436692 prefixEnd_4436692 := by exact prefixLift 4436692
  have htrace : WordTrace (prefixWord ++ tailWord_4436692) baseStart_4436692 baseEnd_4436692 := by
    simpa [prefixWord, tailWord_4436692, baseEnd_4436692] using wordTrace_append hprefix tailTrace_4436692
  have hstable : (prefixWord ++ tailWord_4436692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436692).length < 2 ^ (prefixWord ++ tailWord_4436692).sum := by decide
  have hdescent : baseEnd_4436692 < baseStart_4436692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436698 : List Nat := [3, 1, 1, 2, 2, 2, 2, 1, 1, 1, 7]
def baseStart_4436698 : Nat := 118140960795 + 4436698 * 2 ^ 59
def prefixEnd_4436698 : Nat := 4983230072969 + 3 ^ 40 * 4436698 * 2
def baseEnd_4436698 : Nat := 2278158592841587632371003

theorem tailTrace_4436698 : CollatzResearch.WordTrace tailWord_4436698 prefixEnd_4436698 2278158592841587632371003 := by
  unfold tailWord_4436698
  simp only [CollatzResearch.WordTrace]
  refine ⟨40454917520152087134431687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107879780053738899025151165 40454917520152087134431687)
  ·
    refine ⟨60682376280228130701647531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40454917520152087134431687 60682376280228130701647531)
    ·
      refine ⟨91023564420342196052471297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60682376280228130701647531 91023564420342196052471297)
      ·
        refine ⟨68267673315256647039353473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91023564420342196052471297 68267673315256647039353473)
        ·
          refine ⟨51200754986442485279515105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68267673315256647039353473 51200754986442485279515105)
          ·
            refine ⟨38400566239831863959636329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51200754986442485279515105 38400566239831863959636329)
            ·
              refine ⟨28800424679873897969727247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38400566239831863959636329 28800424679873897969727247)
              ·
                refine ⟨43200637019810846954590871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28800424679873897969727247 43200637019810846954590871)
                ·
                  refine ⟨64800955529716270431886307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43200637019810846954590871 64800955529716270431886307)
                  ·
                    refine ⟨97201433294574405647829461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 64800955529716270431886307 97201433294574405647829461)
                    ·
                      refine ⟨2278158592841587632371003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 97201433294574405647829461 2278158592841587632371003)
                      ·
                        rfl

theorem cell23_4436698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_4436698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436698 prefixEnd_4436698 := by exact prefixLift 4436698
  have htrace : WordTrace (prefixWord ++ tailWord_4436698) baseStart_4436698 baseEnd_4436698 := by
    simpa [prefixWord, tailWord_4436698, baseEnd_4436698] using wordTrace_append hprefix tailTrace_4436698
  have hstable : (prefixWord ++ tailWord_4436698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436698).length < 2 ^ (prefixWord ++ tailWord_4436698).sum := by decide
  have hdescent : baseEnd_4436698 < baseStart_4436698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436745 : List Nat := [1, 2, 1, 1, 3, 2, 3, 1, 4, 2, 3]
def baseStart_4436745 : Nat := 118140960795 + 4436745 * 2 ^ 59
def prefixEnd_4436745 : Nat := 4983230072969 + 3 ^ 40 * 4436745 * 2
def baseEnd_4436745 : Nat := 2278182726432348948483287

theorem tailTrace_4436745 : CollatzResearch.WordTrace tailWord_4436745 prefixEnd_4436745 2278182726432348948483287 := by
  unfold tailWord_4436745
  simp only [CollatzResearch.WordTrace]
  refine ⟨161821384311438075564687689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107880922874292050376458459 161821384311438075564687689)
  ·
    refine ⟨121366038233578556673515767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161821384311438075564687689 121366038233578556673515767)
    ·
      refine ⟨182049057350367835010273651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121366038233578556673515767 182049057350367835010273651)
      ·
        refine ⟨273073586025551752515410477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182049057350367835010273651 273073586025551752515410477)
        ·
          refine ⟨102402594759581907193278929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 273073586025551752515410477 102402594759581907193278929)
          ·
            refine ⟨76801946069686430394959197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102402594759581907193278929 76801946069686430394959197)
            ·
              refine ⟨28800729776132411398109699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76801946069686430394959197 28800729776132411398109699)
              ·
                refine ⟨43201094664198617097164549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28800729776132411398109699 43201094664198617097164549)
                ·
                  refine ⟨8100205249537240705718353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43201094664198617097164549 8100205249537240705718353)
                  ·
                    refine ⟨6075153937152930529288765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8100205249537240705718353 6075153937152930529288765)
                    ·
                      refine ⟨2278182726432348948483287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6075153937152930529288765 2278182726432348948483287)
                      ·
                        rfl

theorem cell23_4436745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 2, 3].length) (baseStart_4436745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436745 prefixEnd_4436745 := by exact prefixLift 4436745
  have htrace : WordTrace (prefixWord ++ tailWord_4436745) baseStart_4436745 baseEnd_4436745 := by
    simpa [prefixWord, tailWord_4436745, baseEnd_4436745] using wordTrace_append hprefix tailTrace_4436745
  have hstable : (prefixWord ++ tailWord_4436745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436745).length < 2 ^ (prefixWord ++ tailWord_4436745).sum := by decide
  have hdescent : baseEnd_4436745 < baseStart_4436745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436825 : List Nat := [1, 2, 1, 2, 2, 4, 1, 3, 1, 6]
def baseStart_4436825 : Nat := 118140960795 + 4436825 * 2 ^ 59
def prefixEnd_4436825 : Nat := 4983230072969 + 3 ^ 40 * 4436825 * 2
def baseEnd_4436825 : Nat := 759407934961569545160973

theorem tailTrace_4436825 : CollatzResearch.WordTrace tailWord_4436825 prefixEnd_4436825 759407934961569545160973 := by
  unfold tailWord_4436825
  simp only [CollatzResearch.WordTrace]
  refine ⟨161824302151148249227599929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107882868100765499485066619 161824302151148249227599929)
  ·
    refine ⟨121368226613361186920699947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161824302151148249227599929 121368226613361186920699947)
    ·
      refine ⟨182052339920041780381049921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121368226613361186920699947 182052339920041780381049921)
      ·
        refine ⟨136539254940031335285787441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182052339920041780381049921 136539254940031335285787441)
        ·
          refine ⟨102404441205023501464340581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136539254940031335285787441 102404441205023501464340581)
          ·
            refine ⟨19200832725941906524563859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102404441205023501464340581 19200832725941906524563859)
            ·
              refine ⟨28801249088912859786845789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19200832725941906524563859 28801249088912859786845789)
              ·
                refine ⟨10800468408342322420067171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28801249088912859786845789 10800468408342322420067171)
                ·
                  refine ⟨16200702612513483630100757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10800468408342322420067171 16200702612513483630100757)
                  ·
                    refine ⟨759407934961569545160973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16200702612513483630100757 759407934961569545160973)
                    ·
                      rfl

theorem cell23_4436825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 6].length) (baseStart_4436825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436825 prefixEnd_4436825 := by exact prefixLift 4436825
  have htrace : WordTrace (prefixWord ++ tailWord_4436825) baseStart_4436825 baseEnd_4436825 := by
    simpa [prefixWord, tailWord_4436825, baseEnd_4436825] using wordTrace_append hprefix tailTrace_4436825
  have hstable : (prefixWord ++ tailWord_4436825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436825).length < 2 ^ (prefixWord ++ tailWord_4436825).sum := by decide
  have hdescent : baseEnd_4436825 < baseStart_4436825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436832 : List Nat := [2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 4]
def baseStart_4436832 : Nat := 118140960795 + 4436832 * 2 ^ 59
def prefixEnd_4436832 : Nat := 4983230072969 + 3 ^ 40 * 4436832 * 2
def baseEnd_4436832 : Nat := 2278227399249290108095387

theorem tailTrace_4436832 : CollatzResearch.WordTrace tailWord_4436832 prefixEnd_4436832 2278227399249290108095387 := by
  unfold tailWord_4436832
  simp only [CollatzResearch.WordTrace]
  refine ⟨80912278731061444711552375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107883038308081926282069833 80912278731061444711552375)
  ·
    refine ⟨121368418096592167067328563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80912278731061444711552375 121368418096592167067328563)
    ·
      refine ⟨182052627144888250600992845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121368418096592167067328563 182052627144888250600992845)
      ·
        refine ⟨68269735179333093975372317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182052627144888250600992845 68269735179333093975372317)
        ·
          refine ⟨25601150692249910240764619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68269735179333093975372317 25601150692249910240764619)
          ·
            refine ⟨38401726038374865361146929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25601150692249910240764619 38401726038374865361146929)
            ·
              refine ⟨28801294528781149020860197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38401726038374865361146929 28801294528781149020860197)
              ·
                refine ⟨5400242724146465441411287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28801294528781149020860197 5400242724146465441411287)
                ·
                  refine ⟨8100364086219698162116931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5400242724146465441411287 8100364086219698162116931)
                  ·
                    refine ⟨12150546129329547243175397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8100364086219698162116931 12150546129329547243175397)
                    ·
                      refine ⟨2278227399249290108095387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12150546129329547243175397 2278227399249290108095387)
                      ·
                        rfl

theorem cell23_4436832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 4].length) (baseStart_4436832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436832 prefixEnd_4436832 := by exact prefixLift 4436832
  have htrace : WordTrace (prefixWord ++ tailWord_4436832) baseStart_4436832 baseEnd_4436832 := by
    simpa [prefixWord, tailWord_4436832, baseEnd_4436832] using wordTrace_append hprefix tailTrace_4436832
  have hstable : (prefixWord ++ tailWord_4436832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436832).length < 2 ^ (prefixWord ++ tailWord_4436832).sum := by decide
  have hdescent : baseEnd_4436832 < baseStart_4436832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436836 : List Nat := [2, 3, 1, 1, 4, 3, 1, 1, 2, 3, 2]
def baseStart_4436836 : Nat := 118140960795 + 4436836 * 2 ^ 59
def prefixEnd_4436836 : Nat := 4983230072969 + 3 ^ 40 * 4436836 * 2
def baseEnd_4436836 : Nat := 2278229453171908092445369

theorem tailTrace_4436836 : CollatzResearch.WordTrace tailWord_4436836 prefixEnd_4436836 2278229453171908092445369 := by
  unfold tailWord_4436836
  simp only [CollatzResearch.WordTrace]
  refine ⟨80912351677054199053125181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107883135569405598737500241 80912351677054199053125181)
  ·
    refine ⟨30342131878895324644921943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80912351677054199053125181 30342131878895324644921943)
    ·
      refine ⟨45513197818342986967382915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30342131878895324644921943 45513197818342986967382915)
      ·
        refine ⟨68269796727514480451074373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45513197818342986967382915 68269796727514480451074373)
        ·
          refine ⟨12800586886408965084576445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68269796727514480451074373 12800586886408965084576445)
          ·
            refine ⟨4800220082403361906716167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12800586886408965084576445 4800220082403361906716167)
            ·
              refine ⟨7200330123605042860074251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4800220082403361906716167 7200330123605042860074251)
              ·
                refine ⟨10800495185407564290111377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7200330123605042860074251 10800495185407564290111377)
                ·
                  refine ⟨8100371389055673217583533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10800495185407564290111377 8100371389055673217583533)
                  ·
                    refine ⟨3037639270895877456593825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8100371389055673217583533 3037639270895877456593825)
                    ·
                      refine ⟨2278229453171908092445369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3037639270895877456593825 2278229453171908092445369)
                      ·
                        rfl

theorem cell23_4436836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 2, 3, 2].length) (baseStart_4436836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436836 prefixEnd_4436836 := by exact prefixLift 4436836
  have htrace : WordTrace (prefixWord ++ tailWord_4436836) baseStart_4436836 baseEnd_4436836 := by
    simpa [prefixWord, tailWord_4436836, baseEnd_4436836] using wordTrace_append hprefix tailTrace_4436836
  have hstable : (prefixWord ++ tailWord_4436836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436836).length < 2 ^ (prefixWord ++ tailWord_4436836).sum := by decide
  have hdescent : baseEnd_4436836 < baseStart_4436836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436845 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 3, 1, 6]
def baseStart_4436845 : Nat := 118140960795 + 4436845 * 2 ^ 59
def prefixEnd_4436845 : Nat := 4983230072969 + 3 ^ 40 * 4436845 * 2
def baseEnd_4436845 : Nat := 2278234074497798557232827

theorem tailTrace_4436845 : CollatzResearch.WordTrace tailWord_4436845 prefixEnd_4436845 2278234074497798557232827 := by
  unfold tailWord_4436845
  simp only [CollatzResearch.WordTrace]
  refine ⟨161825031611075792643327989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107883354407383861762218659 161825031611075792643327989)
  ·
    refine ⟨15171096713538355560311999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 161825031611075792643327989 15171096713538355560311999)
    ·
      refine ⟨22756645070307533340467999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15171096713538355560311999 22756645070307533340467999)
      ·
        refine ⟨34134967605461300010701999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22756645070307533340467999 34134967605461300010701999)
        ·
          refine ⟨51202451408191950016052999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34134967605461300010701999 51202451408191950016052999)
          ·
            refine ⟨76803677112287925024079499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51202451408191950016052999 76803677112287925024079499)
            ·
              refine ⟨115205515668431887536119249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76803677112287925024079499 115205515668431887536119249)
              ·
                refine ⟨86404136751323915652089437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115205515668431887536119249 86404136751323915652089437)
                ·
                  refine ⟨32401551281746468369533539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86404136751323915652089437 32401551281746468369533539)
                  ·
                    refine ⟨48602326922619702554300309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32401551281746468369533539 48602326922619702554300309)
                    ·
                      refine ⟨2278234074497798557232827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48602326922619702554300309 2278234074497798557232827)
                      ·
                        rfl

theorem cell23_4436845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_4436845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436845 prefixEnd_4436845 := by exact prefixLift 4436845
  have htrace : WordTrace (prefixWord ++ tailWord_4436845) baseStart_4436845 baseEnd_4436845 := by
    simpa [prefixWord, tailWord_4436845, baseEnd_4436845] using wordTrace_append hprefix tailTrace_4436845
  have hstable : (prefixWord ++ tailWord_4436845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436845).length < 2 ^ (prefixWord ++ tailWord_4436845).sum := by decide
  have hdescent : baseEnd_4436845 < baseStart_4436845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436849 : List Nat := [1, 2, 2, 2, 1, 4, 4, 1, 1, 1, 4]
def baseStart_4436849 : Nat := 118140960795 + 4436849 * 2 ^ 59
def prefixEnd_4436849 : Nat := 4983230072969 + 3 ^ 40 * 4436849 * 2
def baseEnd_4436849 : Nat := 2278236128420416541582809

theorem tailTrace_4436849 : CollatzResearch.WordTrace tailWord_4436849 prefixEnd_4436849 2278236128420416541582809 := by
  unfold tailWord_4436849
  simp only [CollatzResearch.WordTrace]
  refine ⟨161825177503061301326473601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107883451668707534217649067 161825177503061301326473601)
  ·
    refine ⟨121368883127295975994855201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161825177503061301326473601 121368883127295975994855201)
    ·
      refine ⟨91026662345471981996141401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121368883127295975994855201 91026662345471981996141401)
      ·
        refine ⟨68269996759103986497106051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91026662345471981996141401 68269996759103986497106051)
        ·
          refine ⟨102404995138655979745659077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68269996759103986497106051 102404995138655979745659077)
          ·
            refine ⟨19200936588497996202311077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102404995138655979745659077 19200936588497996202311077)
            ·
              refine ⟨3600175610343374287933327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19200936588497996202311077 3600175610343374287933327)
              ·
                refine ⟨5400263415515061431899991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3600175610343374287933327 5400263415515061431899991)
                ·
                  refine ⟨8100395123272592147849987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5400263415515061431899991 8100395123272592147849987)
                  ·
                    refine ⟨12150592684908888221774981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8100395123272592147849987 12150592684908888221774981)
                    ·
                      refine ⟨2278236128420416541582809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12150592684908888221774981 2278236128420416541582809)
                      ·
                        rfl

theorem cell23_4436849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 1, 1, 4].length) (baseStart_4436849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436849 prefixEnd_4436849 := by exact prefixLift 4436849
  have htrace : WordTrace (prefixWord ++ tailWord_4436849) baseStart_4436849 baseEnd_4436849 := by
    simpa [prefixWord, tailWord_4436849, baseEnd_4436849] using wordTrace_append hprefix tailTrace_4436849
  have hstable : (prefixWord ++ tailWord_4436849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436849).length < 2 ^ (prefixWord ++ tailWord_4436849).sum := by decide
  have hdescent : baseEnd_4436849 < baseStart_4436849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436915 : List Nat := [1, 1, 1, 2, 3, 1, 2, 4, 2, 6]
def baseStart_4436915 : Nat := 118140960795 + 4436915 * 2 ^ 59
def prefixEnd_4436915 : Nat := 4983230072969 + 3 ^ 40 * 4436915 * 2
def baseEnd_4436915 : Nat := 759423339381204427785835

theorem tailTrace_4436915 : CollatzResearch.WordTrace tailWord_4436915 prefixEnd_4436915 759423339381204427785835 := by
  unfold tailWord_4436915
  simp only [CollatzResearch.WordTrace]
  refine ⟨161827584720822194598376199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107885056480548129732250799 161827584720822194598376199)
  ·
    refine ⟨242741377081233291897564299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161827584720822194598376199 242741377081233291897564299)
    ·
      refine ⟨364112065621849937846346449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242741377081233291897564299 364112065621849937846346449)
      ·
        refine ⟨273084049216387453384759837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 364112065621849937846346449 273084049216387453384759837)
        ·
          refine ⟨102406518456145295019284939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 273084049216387453384759837 102406518456145295019284939)
          ·
            refine ⟨153609777684217942528927409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102406518456145295019284939 153609777684217942528927409)
            ·
              refine ⟨115207333263163456896695557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153609777684217942528927409 115207333263163456896695557)
              ·
                refine ⟨21601374986843148168130417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 115207333263163456896695557 21601374986843148168130417)
                ·
                  refine ⟨16201031240132361126097813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21601374986843148168130417 16201031240132361126097813)
                  ·
                    refine ⟨759423339381204427785835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16201031240132361126097813 759423339381204427785835)
                    ·
                      rfl

theorem cell23_4436915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 6].length) (baseStart_4436915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436915 prefixEnd_4436915 := by exact prefixLift 4436915
  have htrace : WordTrace (prefixWord ++ tailWord_4436915) baseStart_4436915 baseEnd_4436915 := by
    simpa [prefixWord, tailWord_4436915, baseEnd_4436915] using wordTrace_append hprefix tailTrace_4436915
  have hstable : (prefixWord ++ tailWord_4436915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436915).length < 2 ^ (prefixWord ++ tailWord_4436915).sum := by decide
  have hdescent : baseEnd_4436915 < baseStart_4436915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436934 : List Nat := [6, 1, 3, 1, 2, 1, 1, 2, 1, 1, 4]
def baseStart_4436934 : Nat := 118140960795 + 4436934 * 2 ^ 59
def prefixEnd_4436934 : Nat := 4983230072969 + 3 ^ 40 * 4436934 * 2
def baseEnd_4436934 : Nat := 2278279774276048709019919

theorem tailTrace_4436934 : CollatzResearch.WordTrace tailWord_4436934 prefixEnd_4436934 2278279774276048709019919 := by
  unfold tailWord_4436934
  simp only [CollatzResearch.WordTrace]
  refine ⟨5057133678367292526353683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 107885518471835573895545237 5057133678367292526353683)
  ·
    refine ⟨7585700517550938789530525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5057133678367292526353683 7585700517550938789530525)
    ·
      refine ⟨2844637694081602046073947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7585700517550938789530525 2844637694081602046073947)
      ·
        refine ⟨4266956541122403069110921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2844637694081602046073947 4266956541122403069110921)
        ·
          refine ⟨3200217405841802301833191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4266956541122403069110921 3200217405841802301833191)
          ·
            refine ⟨4800326108762703452749787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3200217405841802301833191 4800326108762703452749787)
            ·
              refine ⟨7200489163144055179124681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4800326108762703452749787 7200489163144055179124681)
              ·
                refine ⟨5400366872358041384343511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7200489163144055179124681 5400366872358041384343511)
                ·
                  refine ⟨8100550308537062076515267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5400366872358041384343511 8100550308537062076515267)
                  ·
                    refine ⟨12150825462805593114772901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8100550308537062076515267 12150825462805593114772901)
                    ·
                      refine ⟨2278279774276048709019919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12150825462805593114772901 2278279774276048709019919)
                      ·
                        rfl

theorem cell23_4436934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_4436934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436934 prefixEnd_4436934 := by exact prefixLift 4436934
  have htrace : WordTrace (prefixWord ++ tailWord_4436934) baseStart_4436934 baseEnd_4436934 := by
    simpa [prefixWord, tailWord_4436934, baseEnd_4436934] using wordTrace_append hprefix tailTrace_4436934
  have hstable : (prefixWord ++ tailWord_4436934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436934).length < 2 ^ (prefixWord ++ tailWord_4436934).sum := by decide
  have hdescent : baseEnd_4436934 < baseStart_4436934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436942 : List Nat := [4, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5]
def baseStart_4436942 : Nat := 118140960795 + 4436942 * 2 ^ 59
def prefixEnd_4436942 : Nat := 4983230072969 + 3 ^ 40 * 4436942 * 2
def baseEnd_4436942 : Nat := 2278283882121284677719881

theorem tailTrace_4436942 : CollatzResearch.WordTrace tailWord_4436942 prefixEnd_4436942 2278283882121284677719881 := by
  unfold tailWord_4436942
  simp only [CollatzResearch.WordTrace]
  refine ⟨20228571186465547276201135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107885712994482918806406053 20228571186465547276201135)
  ·
    refine ⟨30342856779698320914301703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20228571186465547276201135 30342856779698320914301703)
    ·
      refine ⟨45514285169547481371452555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30342856779698320914301703 45514285169547481371452555)
      ·
        refine ⟨68271427754321222057178833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45514285169547481371452555 68271427754321222057178833)
        ·
          refine ⟨51203570815740916542884125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68271427754321222057178833 51203570815740916542884125)
          ·
            refine ⟨19201339055902843703581547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51203570815740916542884125 19201339055902843703581547)
            ·
              refine ⟨28802008583854265555372321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19201339055902843703581547 28802008583854265555372321)
              ·
                refine ⟨21601506437890699166529241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28802008583854265555372321 21601506437890699166529241)
                ·
                  refine ⟨16201129828418024374896931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21601506437890699166529241 16201129828418024374896931)
                  ·
                    refine ⟨24301694742627036562345397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16201129828418024374896931 24301694742627036562345397)
                    ·
                      refine ⟨2278283882121284677719881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24301694742627036562345397 2278283882121284677719881)
                      ·
                        rfl

theorem cell23_4436942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_4436942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436942 prefixEnd_4436942 := by exact prefixLift 4436942
  have htrace : WordTrace (prefixWord ++ tailWord_4436942) baseStart_4436942 baseEnd_4436942 := by
    simpa [prefixWord, tailWord_4436942, baseEnd_4436942] using wordTrace_append hprefix tailTrace_4436942
  have hstable : (prefixWord ++ tailWord_4436942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436942).length < 2 ^ (prefixWord ++ tailWord_4436942).sum := by decide
  have hdescent : baseEnd_4436942 < baseStart_4436942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436945 : List Nat := [1, 2, 2, 1, 2, 1, 4, 1, 9]
def baseStart_4436945 : Nat := 118140960795 + 4436945 * 2 ^ 59
def prefixEnd_4436945 : Nat := 4983230072969 + 3 ^ 40 * 4436945 * 2
def baseEnd_4436945 : Nat := 253142824729249796220263

theorem tailTrace_4436945 : CollatzResearch.WordTrace tailWord_4436945 prefixEnd_4436945 253142824729249796220263 := by
  unfold tailWord_4436945
  simp only [CollatzResearch.WordTrace]
  refine ⟨161828678910713509721968289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107885785940475673147978859 161828678910713509721968289)
  ·
    refine ⟨121371509183035132291476217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161828678910713509721968289 121371509183035132291476217)
    ·
      refine ⟨91028631887276349218607163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121371509183035132291476217 91028631887276349218607163)
      ·
        refine ⟨136542947830914523827910745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91028631887276349218607163 136542947830914523827910745)
        ·
          refine ⟨102407210873185892870933059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136542947830914523827910745 102407210873185892870933059)
          ·
            refine ⟨153610816309778839306399589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102407210873185892870933059 153610816309778839306399589)
            ·
              refine ⟨28802028058083532369949923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 153610816309778839306399589 28802028058083532369949923)
              ·
                refine ⟨43203042087125298554924885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28802028058083532369949923 43203042087125298554924885)
                ·
                  refine ⟨253142824729249796220263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43203042087125298554924885 253142824729249796220263)
                  ·
                    rfl

theorem cell23_4436945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 9].length) (baseStart_4436945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436945 prefixEnd_4436945 := by exact prefixLift 4436945
  have htrace : WordTrace (prefixWord ++ tailWord_4436945) baseStart_4436945 baseEnd_4436945 := by
    simpa [prefixWord, tailWord_4436945, baseEnd_4436945] using wordTrace_append hprefix tailTrace_4436945
  have hstable : (prefixWord ++ tailWord_4436945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436945).length < 2 ^ (prefixWord ++ tailWord_4436945).sum := by decide
  have hdescent : baseEnd_4436945 < baseStart_4436945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4436999 : List Nat := [1, 1, 4, 3, 1, 1, 1, 2, 2, 5, 2]
def baseStart_4436999 : Nat := 118140960795 + 4436999 * 2 ^ 59
def prefixEnd_4436999 : Nat := 4983230072969 + 3 ^ 40 * 4436999 * 2
def baseEnd_4436999 : Nat := 2278313150518590954707119

theorem tailTrace_4436999 : CollatzResearch.WordTrace tailWord_4436999 prefixEnd_4436999 2278313150518590954707119 := by
  unfold tailWord_4436999
  simp only [CollatzResearch.WordTrace]
  refine ⟨161830648452517876944434051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107887098968345251296289367 161830648452517876944434051)
  ·
    refine ⟨242745972678776815416651077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161830648452517876944434051 242745972678776815416651077)
    ·
      refine ⟨45514869877270652890622077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 242745972678776815416651077 45514869877270652890622077)
      ·
        refine ⟨17068076203976494833983279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45514869877270652890622077 17068076203976494833983279)
        ·
          refine ⟨25602114305964742250974919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17068076203976494833983279 25602114305964742250974919)
          ·
            refine ⟨38403171458947113376462379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25602114305964742250974919 38403171458947113376462379)
            ·
              refine ⟨57604757188420670064693569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38403171458947113376462379 57604757188420670064693569)
              ·
                refine ⟨43203567891315502548520177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57604757188420670064693569 43203567891315502548520177)
                ·
                  refine ⟨32402675918486626911390133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43203567891315502548520177 32402675918486626911390133)
                  ·
                    refine ⟨3037750867358121272942825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32402675918486626911390133 3037750867358121272942825)
                    ·
                      refine ⟨2278313150518590954707119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3037750867358121272942825 2278313150518590954707119)
                      ·
                        rfl

theorem cell23_4436999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_4436999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4436999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4436999 prefixEnd_4436999 := by exact prefixLift 4436999
  have htrace : WordTrace (prefixWord ++ tailWord_4436999) baseStart_4436999 baseEnd_4436999 := by
    simpa [prefixWord, tailWord_4436999, baseEnd_4436999] using wordTrace_append hprefix tailTrace_4436999
  have hstable : (prefixWord ++ tailWord_4436999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4436999).length < 2 ^ (prefixWord ++ tailWord_4436999).sum := by decide
  have hdescent : baseEnd_4436999 < baseStart_4436999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4436999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437029 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 4, 4, 2]
def baseStart_4437029 : Nat := 118140960795 + 4437029 * 2 ^ 59
def prefixEnd_4437029 : Nat := 4983230072969 + 3 ^ 40 * 4437029 * 2
def baseEnd_4437029 : Nat := 2278328554938225837331981

theorem tailTrace_4437029 : CollatzResearch.WordTrace tailWord_4437029 prefixEnd_4437029 2278328554938225837331981 := by
  unfold tailWord_4437029
  simp only [CollatzResearch.WordTrace]
  refine ⟨161831742642409192068026141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107887828428272794712017427 161831742642409192068026141)
  ·
    refine ⟨60686903490903447025509803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161831742642409192068026141 60686903490903447025509803)
    ·
      refine ⟨91030355236355170538264705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60686903490903447025509803 91030355236355170538264705)
      ·
        refine ⟨68272766427266377903698529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91030355236355170538264705 68272766427266377903698529)
        ·
          refine ⟨51204574820449783427773897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68272766427266377903698529 51204574820449783427773897)
          ·
            refine ⟨38403431115337337570830423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51204574820449783427773897 38403431115337337570830423)
            ·
              refine ⟨57605146673006006356245635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38403431115337337570830423 57605146673006006356245635)
              ·
                refine ⟨86407720009509009534368453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57605146673006006356245635 86407720009509009534368453)
                ·
                  refine ⟨16201447501782939287694085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86407720009509009534368453 16201447501782939287694085)
                  ·
                    refine ⟨3037771406584301116442641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16201447501782939287694085 3037771406584301116442641)
                    ·
                      refine ⟨2278328554938225837331981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3037771406584301116442641 2278328554938225837331981)
                      ·
                        rfl

theorem cell23_4437029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 4, 2].length) (baseStart_4437029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437029 prefixEnd_4437029 := by exact prefixLift 4437029
  have htrace : WordTrace (prefixWord ++ tailWord_4437029) baseStart_4437029 baseEnd_4437029 := by
    simpa [prefixWord, tailWord_4437029, baseEnd_4437029] using wordTrace_append hprefix tailTrace_4437029
  have hstable : (prefixWord ++ tailWord_4437029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437029).length < 2 ^ (prefixWord ++ tailWord_4437029).sum := by decide
  have hdescent : baseEnd_4437029 < baseStart_4437029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437042 : List Nat := [3, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6]
def baseStart_4437042 : Nat := 118140960795 + 4437042 * 2 ^ 59
def prefixEnd_4437042 : Nat := 4983230072969 + 3 ^ 40 * 4437042 * 2
def baseEnd_4437042 : Nat := 2278335230186734286469421

theorem tailTrace_4437042 : CollatzResearch.WordTrace tailWord_4437042 prefixEnd_4437042 2278335230186734286469421 := by
  unfold tailWord_4437042
  simp only [CollatzResearch.WordTrace]
  refine ⟨40458054197840523822062345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107888144527574730192166253 40458054197840523822062345)
  ·
    refine ⟨30343540648380392866546759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40458054197840523822062345 30343540648380392866546759)
    ·
      refine ⟨45515310972570589299820139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30343540648380392866546759 45515310972570589299820139)
      ·
        refine ⟨68272966458855883949730209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45515310972570589299820139 68272966458855883949730209)
        ·
          refine ⟨51204724844141912962297657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68272966458855883949730209 51204724844141912962297657)
          ·
            refine ⟨38403543633106434721723243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51204724844141912962297657 38403543633106434721723243)
            ·
              refine ⟨57605315449659652082584865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38403543633106434721723243 57605315449659652082584865)
              ·
                refine ⟨43203986587244739061938649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57605315449659652082584865 43203986587244739061938649)
                ·
                  refine ⟨32402989940433554296453987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43203986587244739061938649 32402989940433554296453987)
                  ·
                    refine ⟨48604484910650331444680981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32402989940433554296453987 48604484910650331444680981)
                    ·
                      refine ⟨2278335230186734286469421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48604484910650331444680981 2278335230186734286469421)
                      ·
                        rfl

theorem cell23_4437042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_4437042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437042 prefixEnd_4437042 := by exact prefixLift 4437042
  have htrace : WordTrace (prefixWord ++ tailWord_4437042) baseStart_4437042 baseEnd_4437042 := by
    simpa [prefixWord, tailWord_4437042, baseEnd_4437042] using wordTrace_append hprefix tailTrace_4437042
  have hstable : (prefixWord ++ tailWord_4437042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437042).length < 2 ^ (prefixWord ++ tailWord_4437042).sum := by decide
  have hdescent : baseEnd_4437042 < baseStart_4437042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437049 : List Nat := [1, 2, 1, 5, 2, 1, 1, 2, 1, 4, 3]
def baseStart_4437049 : Nat := 118140960795 + 4437049 * 2 ^ 59
def prefixEnd_4437049 : Nat := 4983230072969 + 3 ^ 40 * 4437049 * 2
def baseEnd_4437049 : Nat := 2278338824551315759081889

theorem tailTrace_4437049 : CollatzResearch.WordTrace tailWord_4437049 prefixEnd_4437049 2278338824551315759081889 := by
  unfold tailWord_4437049
  simp only [CollatzResearch.WordTrace]
  refine ⟨161832472102336735483754201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107888314734891156989169467 161832472102336735483754201)
  ·
    refine ⟨121374354076752551612815651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161832472102336735483754201 121374354076752551612815651)
    ·
      refine ⟨182061531115128827419223477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121374354076752551612815651 182061531115128827419223477)
      ·
        refine ⟨17068268542043327570552201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 182061531115128827419223477 17068268542043327570552201)
        ·
          refine ⟨12801201406532495677914151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17068268542043327570552201 12801201406532495677914151)
          ·
            refine ⟨19201802109798743516871227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12801201406532495677914151 19201802109798743516871227)
            ·
              refine ⟨28802703164698115275306841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19201802109798743516871227 28802703164698115275306841)
              ·
                refine ⟨21602027373523586456480131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28802703164698115275306841 21602027373523586456480131)
                ·
                  refine ⟨32403041060285379684720197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21602027373523586456480131 32403041060285379684720197)
                  ·
                    refine ⟨6075570198803508690885037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32403041060285379684720197 6075570198803508690885037)
                    ·
                      refine ⟨2278338824551315759081889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6075570198803508690885037 2278338824551315759081889)
                      ·
                        rfl

theorem cell23_4437049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_4437049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437049 prefixEnd_4437049 := by exact prefixLift 4437049
  have htrace : WordTrace (prefixWord ++ tailWord_4437049) baseStart_4437049 baseEnd_4437049 := by
    simpa [prefixWord, tailWord_4437049, baseEnd_4437049] using wordTrace_append hprefix tailTrace_4437049
  have hstable : (prefixWord ++ tailWord_4437049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437049).length < 2 ^ (prefixWord ++ tailWord_4437049).sum := by decide
  have hdescent : baseEnd_4437049 < baseStart_4437049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437069 : List Nat := [1, 6, 1, 1, 1, 2, 1, 2, 8]
def baseStart_4437069 : Nat := 118140960795 + 4437069 * 2 ^ 59
def prefixEnd_4437069 : Nat := 4983230072969 + 3 ^ 40 * 4437069 * 2
def baseEnd_4437069 : Nat := 253149899351600631203533

theorem tailTrace_4437069 : CollatzResearch.WordTrace tailWord_4437069 prefixEnd_4437069 253149899351600631203533 := by
  unfold tailWord_4437069
  simp only [CollatzResearch.WordTrace]
  refine ⟨161833201562264278899482261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107888801041509519266321507 161833201562264278899482261)
  ·
    refine ⟨7585931323231138073413231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 161833201562264278899482261 7585931323231138073413231)
    ·
      refine ⟨11378896984846707110119847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7585931323231138073413231 11378896984846707110119847)
      ·
        refine ⟨17068345477270060665179771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11378896984846707110119847 17068345477270060665179771)
        ·
          refine ⟨25602518215905090997769657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17068345477270060665179771 25602518215905090997769657)
          ·
            refine ⟨19201888661928818248327243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25602518215905090997769657 19201888661928818248327243)
            ·
              refine ⟨28802832992893227372490865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19201888661928818248327243 28802832992893227372490865)
              ·
                refine ⟨21602124744669920529368149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28802832992893227372490865 21602124744669920529368149)
                ·
                  refine ⟨253149899351600631203533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21602124744669920529368149 253149899351600631203533)
                  ·
                    rfl

theorem cell23_4437069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_4437069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437069 prefixEnd_4437069 := by exact prefixLift 4437069
  have htrace : WordTrace (prefixWord ++ tailWord_4437069) baseStart_4437069 baseEnd_4437069 := by
    simpa [prefixWord, tailWord_4437069, baseEnd_4437069] using wordTrace_append hprefix tailTrace_4437069
  have hstable : (prefixWord ++ tailWord_4437069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437069).length < 2 ^ (prefixWord ++ tailWord_4437069).sum := by decide
  have hdescent : baseEnd_4437069 < baseStart_4437069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437092 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 2, 1, 7]
def baseStart_4437092 : Nat := 118140960795 + 4437092 * 2 ^ 59
def prefixEnd_4437092 : Nat := 4983230072969 + 3 ^ 40 * 4437092 * 2
def baseEnd_4437092 : Nat := 2278360904219459090844191

theorem tailTrace_4437092 : CollatzResearch.WordTrace tailWord_4437092 prefixEnd_4437092 2278360904219459090844191 := by
  unfold tailWord_4437092
  simp only [CollatzResearch.WordTrace]
  refine ⟨80917020220590476913784765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107889360294120635885046353 80917020220590476913784765)
  ·
    refine ⟨30343882582721428842669287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80917020220590476913784765 30343882582721428842669287)
    ·
      refine ⟨45515823874082143264003931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30343882582721428842669287 45515823874082143264003931)
      ·
        refine ⟨68273735811123214896005897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45515823874082143264003931 68273735811123214896005897)
        ·
          refine ⟨51205301858342411172004423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68273735811123214896005897 51205301858342411172004423)
          ·
            refine ⟨76807952787513616758006635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51205301858342411172004423 76807952787513616758006635)
            ·
              refine ⟨115211929181270425137009953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76807952787513616758006635 115211929181270425137009953)
              ·
                refine ⟨86408946885952818852757465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115211929181270425137009953 86408946885952818852757465)
                ·
                  refine ⟨64806710164464614139568099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86408946885952818852757465 64806710164464614139568099)
                  ·
                    refine ⟨97210065246696921209352149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 64806710164464614139568099 97210065246696921209352149)
                    ·
                      refine ⟨2278360904219459090844191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 97210065246696921209352149 2278360904219459090844191)
                      ·
                        rfl

theorem cell23_4437092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_4437092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437092 prefixEnd_4437092 := by exact prefixLift 4437092
  have htrace : WordTrace (prefixWord ++ tailWord_4437092) baseStart_4437092 baseEnd_4437092 := by
    simpa [prefixWord, tailWord_4437092, baseEnd_4437092] using wordTrace_append hprefix tailTrace_4437092
  have hstable : (prefixWord ++ tailWord_4437092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437092).length < 2 ^ (prefixWord ++ tailWord_4437092).sum := by decide
  have hdescent : baseEnd_4437092 < baseStart_4437092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437106 : List Nat := [3, 2, 1, 2, 2, 1, 1, 2, 4, 3, 2]
def baseStart_4437106 : Nat := 118140960795 + 4437106 * 2 ^ 59
def prefixEnd_4437106 : Nat := 4983230072969 + 3 ^ 40 * 4437106 * 2
def baseEnd_4437106 : Nat := 2278368092948622036069127

theorem tailTrace_4437106 : CollatzResearch.WordTrace tailWord_4437106 prefixEnd_4437106 2278368092948622036069127 := by
  unfold tailWord_4437106
  simp only [CollatzResearch.WordTrace]
  refine ⟨40458637765782558554644793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107889700708753489479052781 40458637765782558554644793)
  ·
    refine ⟨30343978324336918915983595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40458637765782558554644793 30343978324336918915983595)
    ·
      refine ⟨45515967486505378373975393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30343978324336918915983595 45515967486505378373975393)
      ·
        refine ⟨34136975614879033780481545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45515967486505378373975393 34136975614879033780481545)
        ·
          refine ⟨25602731711159275335361159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34136975614879033780481545 25602731711159275335361159)
          ·
            refine ⟨38404097566738913003041739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25602731711159275335361159 38404097566738913003041739)
            ·
              refine ⟨57606146350108369504562609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38404097566738913003041739 57606146350108369504562609)
              ·
                refine ⟨43204609762581277128421957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57606146350108369504562609 43204609762581277128421957)
                ·
                  refine ⟨8100864330483989461579117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43204609762581277128421957 8100864330483989461579117)
                  ·
                    refine ⟨3037824123931496048092169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8100864330483989461579117 3037824123931496048092169)
                    ·
                      refine ⟨2278368092948622036069127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3037824123931496048092169 2278368092948622036069127)
                      ·
                        rfl

theorem cell23_4437106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_4437106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437106 prefixEnd_4437106 := by exact prefixLift 4437106
  have htrace : WordTrace (prefixWord ++ tailWord_4437106) baseStart_4437106 baseEnd_4437106 := by
    simpa [prefixWord, tailWord_4437106, baseEnd_4437106] using wordTrace_append hprefix tailTrace_4437106
  have hstable : (prefixWord ++ tailWord_4437106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437106).length < 2 ^ (prefixWord ++ tailWord_4437106).sum := by decide
  have hdescent : baseEnd_4437106 < baseStart_4437106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437129 : List Nat := [1, 2, 1, 1, 4, 4, 1, 2, 1, 6]
def baseStart_4437129 : Nat := 118140960795 + 4437129 * 2 ^ 59
def prefixEnd_4437129 : Nat := 4983230072969 + 3 ^ 40 * 4437129 * 2
def baseEnd_4437129 : Nat := 759459967667891815360507

theorem tailTrace_4437129 : CollatzResearch.WordTrace tailWord_4437129 prefixEnd_4437129 759459967667891815360507 := by
  unfold tailWord_4437129
  simp only [CollatzResearch.WordTrace]
  refine ⟨161835389942046909146666441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107890259961364606097777627 161835389942046909146666441)
  ·
    refine ⟨121376542456535181859999831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161835389942046909146666441 121376542456535181859999831)
    ·
      refine ⟨182064813684802772789999747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121376542456535181859999831 182064813684802772789999747)
      ·
        refine ⟨273097220527204159184999621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182064813684802772789999747 273097220527204159184999621)
        ·
          refine ⟨51205728848850779847187429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 273097220527204159184999621 51205728848850779847187429)
          ·
            refine ⟨9601074159159521221347643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51205728848850779847187429 9601074159159521221347643)
            ·
              refine ⟨14401611238739281832021465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9601074159159521221347643 14401611238739281832021465)
              ·
                refine ⟨10801208429054461374016099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14401611238739281832021465 10801208429054461374016099)
                ·
                  refine ⟨16201812643581692061024149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10801208429054461374016099 16201812643581692061024149)
                  ·
                    refine ⟨759459967667891815360507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16201812643581692061024149 759459967667891815360507)
                    ·
                      rfl

theorem cell23_4437129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 6].length) (baseStart_4437129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437129 prefixEnd_4437129 := by exact prefixLift 4437129
  have htrace : WordTrace (prefixWord ++ tailWord_4437129) baseStart_4437129 baseEnd_4437129 := by
    simpa [prefixWord, tailWord_4437129, baseEnd_4437129] using wordTrace_append hprefix tailTrace_4437129
  have hstable : (prefixWord ++ tailWord_4437129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437129).length < 2 ^ (prefixWord ++ tailWord_4437129).sum := by decide
  have hdescent : baseEnd_4437129 < baseStart_4437129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437136 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 7, 2, 2]
def baseStart_4437136 : Nat := 118140960795 + 4437136 * 2 ^ 59
def prefixEnd_4437136 : Nat := 4983230072969 + 3 ^ 40 * 4437136 * 2
def baseEnd_4437136 : Nat := 2278383497368256918693989

theorem tailTrace_4437136 : CollatzResearch.WordTrace tailWord_4437136 prefixEnd_4437136 2278383497368256918693989 := by
  unfold tailWord_4437136
  simp only [CollatzResearch.WordTrace]
  refine ⟨80917822626510774671085631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107890430168681032894780841 80917822626510774671085631)
  ·
    refine ⟨121376733939766162006628447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80917822626510774671085631 121376733939766162006628447)
    ·
      refine ⟨182065100909649243009942671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121376733939766162006628447 182065100909649243009942671)
      ·
        refine ⟨273097651364473864514914007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182065100909649243009942671 273097651364473864514914007)
        ·
          refine ⟨409646477046710796772371011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273097651364473864514914007 409646477046710796772371011)
          ·
            refine ⟨614469715570066195158556517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409646477046710796772371011 614469715570066195158556517)
            ·
              refine ⟨115213071669387411592229347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 614469715570066195158556517 115213071669387411592229347)
              ·
                refine ⟨172819607504081117388344021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115213071669387411592229347 172819607504081117388344021)
                ·
                  refine ⟨4050459550876901188789313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 172819607504081117388344021 4050459550876901188789313)
                  ·
                    refine ⟨3037844663157675891591985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4050459550876901188789313 3037844663157675891591985)
                    ·
                      refine ⟨2278383497368256918693989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3037844663157675891591985 2278383497368256918693989)
                      ·
                        rfl

theorem cell23_4437136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 7, 2, 2].length) (baseStart_4437136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437136 prefixEnd_4437136 := by exact prefixLift 4437136
  have htrace : WordTrace (prefixWord ++ tailWord_4437136) baseStart_4437136 baseEnd_4437136 := by
    simpa [prefixWord, tailWord_4437136, baseEnd_4437136] using wordTrace_append hprefix tailTrace_4437136
  have hstable : (prefixWord ++ tailWord_4437136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437136).length < 2 ^ (prefixWord ++ tailWord_4437136).sum := by decide
  have hdescent : baseEnd_4437136 < baseStart_4437136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437139 : List Nat := [1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 5]
def baseStart_4437139 : Nat := 118140960795 + 4437139 * 2 ^ 59
def prefixEnd_4437139 : Nat := 4983230072969 + 3 ^ 40 * 4437139 * 2
def baseEnd_4437139 : Nat := 2278385037810220406956475

theorem tailTrace_4437139 : CollatzResearch.WordTrace tailWord_4437139 prefixEnd_4437139 2278385037810220406956475 := by
  unfold tailWord_4437139
  simp only [CollatzResearch.WordTrace]
  refine ⟨161835754672010680854530471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107890503114673787236353647 161835754672010680854530471)
  ·
    refine ⟨242753632008016021281795707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161835754672010680854530471 242753632008016021281795707)
    ·
      refine ⟨364130448012024031922693561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242753632008016021281795707 364130448012024031922693561)
      ·
        refine ⟨273097836009018023942020171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 364130448012024031922693561 273097836009018023942020171)
        ·
          refine ⟨409646754013527035913030257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273097836009018023942020171 409646754013527035913030257)
          ·
            refine ⟨307235065510145276934772693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 409646754013527035913030257 307235065510145276934772693)
            ·
              refine ⟨7200821847894029928158735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 307235065510145276934772693 7200821847894029928158735)
              ·
                refine ⟨10801232771841044892238103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7200821847894029928158735 10801232771841044892238103)
                ·
                  refine ⟨16201849157761567338357155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10801232771841044892238103 16201849157761567338357155)
                  ·
                    refine ⟨24302773736642351007535733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16201849157761567338357155 24302773736642351007535733)
                    ·
                      refine ⟨2278385037810220406956475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24302773736642351007535733 2278385037810220406956475)
                      ·
                        rfl

theorem cell23_4437139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 5].length) (baseStart_4437139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437139 prefixEnd_4437139 := by exact prefixLift 4437139
  have htrace : WordTrace (prefixWord ++ tailWord_4437139) baseStart_4437139 baseEnd_4437139 := by
    simpa [prefixWord, tailWord_4437139, baseEnd_4437139] using wordTrace_append hprefix tailTrace_4437139
  have hstable : (prefixWord ++ tailWord_4437139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437139).length < 2 ^ (prefixWord ++ tailWord_4437139).sum := by decide
  have hdescent : baseEnd_4437139 < baseStart_4437139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437149 : List Nat := [1, 4, 2, 1, 1, 2, 1, 2, 3, 2, 4]
def baseStart_4437149 : Nat := 118140960795 + 4437149 * 2 ^ 59
def prefixEnd_4437149 : Nat := 4983230072969 + 3 ^ 40 * 4437149 * 2
def baseEnd_4437149 : Nat := 2278390172616765367831429

theorem tailTrace_4437149 : CollatzResearch.WordTrace tailWord_4437149 prefixEnd_4437149 2278390172616765367831429 := by
  unfold tailWord_4437149
  simp only [CollatzResearch.WordTrace]
  refine ⟨161836119401974452562394501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107890746267982968374929667 161836119401974452562394501)
  ·
    refine ⟨30344272387870209855448969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161836119401974452562394501 30344272387870209855448969)
    ·
      refine ⟨22758204290902657391586727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30344272387870209855448969 22758204290902657391586727)
      ·
        refine ⟨34137306436353986087380091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22758204290902657391586727 34137306436353986087380091)
        ·
          refine ⟨51205959654530979131070137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34137306436353986087380091 51205959654530979131070137)
          ·
            refine ⟨38404469740898234348302603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51205959654530979131070137 38404469740898234348302603)
            ·
              refine ⟨57606704611347351522453905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38404469740898234348302603 57606704611347351522453905)
              ·
                refine ⟨43205028458510513641840429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57606704611347351522453905 43205028458510513641840429)
                ·
                  refine ⟨16201885671941442615690161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43205028458510513641840429 16201885671941442615690161)
                  ·
                    refine ⟨12151414253956081961767621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16201885671941442615690161 12151414253956081961767621)
                    ·
                      refine ⟨2278390172616765367831429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12151414253956081961767621 2278390172616765367831429)
                      ·
                        rfl

theorem cell23_4437149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_4437149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437149 prefixEnd_4437149 := by exact prefixLift 4437149
  have htrace : WordTrace (prefixWord ++ tailWord_4437149) baseStart_4437149 baseEnd_4437149 := by
    simpa [prefixWord, tailWord_4437149, baseEnd_4437149] using wordTrace_append hprefix tailTrace_4437149
  have hstable : (prefixWord ++ tailWord_4437149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437149).length < 2 ^ (prefixWord ++ tailWord_4437149).sum := by decide
  have hdescent : baseEnd_4437149 < baseStart_4437149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437153 : List Nat := [1, 2, 3, 3, 1, 1, 2, 3, 3, 2, 2]
def baseStart_4437153 : Nat := 118140960795 + 4437153 * 2 ^ 59
def prefixEnd_4437153 : Nat := 4983230072969 + 3 ^ 40 * 4437153 * 2
def baseEnd_4437153 : Nat := 2278392226539383352181411

theorem tailTrace_4437153 : CollatzResearch.WordTrace tailWord_4437153 prefixEnd_4437153 2278392226539383352181411 := by
  unfold tailWord_4437153
  simp only [CollatzResearch.WordTrace]
  refine ⟨161836265293959961245540113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107890843529306640830360075 161836265293959961245540113)
  ·
    refine ⟨121377198970469970934155085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161836265293959961245540113 121377198970469970934155085)
    ·
      refine ⟨45516449613926239100308157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121377198970469970934155085 45516449613926239100308157)
      ·
        refine ⟨17068668605222339662615559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45516449613926239100308157 17068668605222339662615559)
        ·
          refine ⟨25603002907833509493923339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17068668605222339662615559 25603002907833509493923339)
          ·
            refine ⟨38404504361750264240885009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25603002907833509493923339 38404504361750264240885009)
            ·
              refine ⟨28803378271312698180663757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38404504361750264240885009 28803378271312698180663757)
              ·
                refine ⟨10801266851742261817748909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28803378271312698180663757 10801266851742261817748909)
                ·
                  refine ⟨4050475069403348181655841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10801266851742261817748909 4050475069403348181655841)
                  ·
                    refine ⟨3037856302052511136241881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4050475069403348181655841 3037856302052511136241881)
                    ·
                      refine ⟨2278392226539383352181411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3037856302052511136241881 2278392226539383352181411)
                      ·
                        rfl

theorem cell23_4437153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_4437153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437153 prefixEnd_4437153 := by exact prefixLift 4437153
  have htrace : WordTrace (prefixWord ++ tailWord_4437153) baseStart_4437153 baseEnd_4437153 := by
    simpa [prefixWord, tailWord_4437153, baseEnd_4437153] using wordTrace_append hprefix tailTrace_4437153
  have hstable : (prefixWord ++ tailWord_4437153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437153).length < 2 ^ (prefixWord ++ tailWord_4437153).sum := by decide
  have hdescent : baseEnd_4437153 < baseStart_4437153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437156 : List Nat := [2, 3, 1, 2, 3, 1, 1, 2, 3, 2, 3]
def baseStart_4437156 : Nat := 118140960795 + 4437156 * 2 ^ 59
def prefixEnd_4437156 : Nat := 4983230072969 + 3 ^ 40 * 4437156 * 2
def baseEnd_4437156 : Nat := 2278393766981346840443897

theorem tailTrace_4437156 : CollatzResearch.WordTrace tailWord_4437156 prefixEnd_4437156 2278393766981346840443897 := by
  unfold tailWord_4437156
  simp only [CollatzResearch.WordTrace]
  refine ⟨80918187356474546378949661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107890916475299395171932881 80918187356474546378949661)
  ·
    refine ⟨30344320258677954892106123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80918187356474546378949661 30344320258677954892106123)
    ·
      refine ⟨45516480388016932338159185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30344320258677954892106123 45516480388016932338159185)
      ·
        refine ⟨34137360291012699253619389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45516480388016932338159185 34137360291012699253619389)
        ·
          refine ⟨12801510109129762220107271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34137360291012699253619389 12801510109129762220107271)
          ·
            refine ⟨19202265163694643330160907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12801510109129762220107271 19202265163694643330160907)
            ·
              refine ⟨28803397745541964995241361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19202265163694643330160907 28803397745541964995241361)
              ·
                refine ⟨21602548309156473746431021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28803397745541964995241361 21602548309156473746431021)
                ·
                  refine ⟨8100955615933677654911633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21602548309156473746431021 8100955615933677654911633)
                  ·
                    refine ⟨6075716711950258241183725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8100955615933677654911633 6075716711950258241183725)
                    ·
                      refine ⟨2278393766981346840443897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6075716711950258241183725 2278393766981346840443897)
                      ·
                        rfl

theorem cell23_4437156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_4437156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437156 prefixEnd_4437156 := by exact prefixLift 4437156
  have htrace : WordTrace (prefixWord ++ tailWord_4437156) baseStart_4437156 baseEnd_4437156 := by
    simpa [prefixWord, tailWord_4437156, baseEnd_4437156] using wordTrace_append hprefix tailTrace_4437156
  have hstable : (prefixWord ++ tailWord_4437156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437156).length < 2 ^ (prefixWord ++ tailWord_4437156).sum := by decide
  have hdescent : baseEnd_4437156 < baseStart_4437156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437174 : List Nat := [5, 1, 3, 2, 1, 2, 1, 1, 2, 3, 2]
def baseStart_4437174 : Nat := 118140960795 + 4437174 * 2 ^ 59
def prefixEnd_4437174 : Nat := 4983230072969 + 3 ^ 40 * 4437174 * 2
def baseEnd_4437174 : Nat := 2278403009633127770018815

theorem tailTrace_4437174 : CollatzResearch.WordTrace tailWord_4437174 prefixEnd_4437174 2278403009633127770018815 := by
  unfold tailWord_4437174
  simp only [CollatzResearch.WordTrace]
  refine ⟨10114814451680242614503411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107891354151255921221369717 10114814451680242614503411)
  ·
    refine ⟨15172221677520363921755117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10114814451680242614503411 15172221677520363921755117)
    ·
      refine ⟨5689583129070136470658169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15172221677520363921755117 5689583129070136470658169)
      ·
        refine ⟨4267187346802602352993627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5689583129070136470658169 4267187346802602352993627)
        ·
          refine ⟨6400781020203903529490441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4267187346802602352993627 6400781020203903529490441)
          ·
            refine ⟨4800585765152927647117831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6400781020203903529490441 4800585765152927647117831)
            ·
              refine ⟨7200878647729391470676747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4800585765152927647117831 7200878647729391470676747)
              ·
                refine ⟨10801317971594087206015121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7200878647729391470676747 10801317971594087206015121)
                ·
                  refine ⟨8100988478695565404511341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10801317971594087206015121 8100988478695565404511341)
                  ·
                    refine ⟨3037870679510837026691753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8100988478695565404511341 3037870679510837026691753)
                    ·
                      refine ⟨2278403009633127770018815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3037870679510837026691753 2278403009633127770018815)
                      ·
                        rfl

theorem cell23_4437174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_4437174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437174 prefixEnd_4437174 := by exact prefixLift 4437174
  have htrace : WordTrace (prefixWord ++ tailWord_4437174) baseStart_4437174 baseEnd_4437174 := by
    simpa [prefixWord, tailWord_4437174, baseEnd_4437174] using wordTrace_append hprefix tailTrace_4437174
  have hstable : (prefixWord ++ tailWord_4437174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437174).length < 2 ^ (prefixWord ++ tailWord_4437174).sum := by decide
  have hdescent : baseEnd_4437174 < baseStart_4437174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437246 : List Nat := [4, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5]
def baseStart_4437246 : Nat := 118140960795 + 4437246 * 2 ^ 59
def prefixEnd_4437246 : Nat := 4983230072969 + 3 ^ 40 * 4437246 * 2
def baseEnd_4437246 : Nat := 2278439980240251488318483

theorem tailTrace_4437246 : CollatzResearch.WordTrace tailWord_4437246 prefixEnd_4437246 2278439980240251488318483 := by
  unfold tailWord_4437246
  simp only [CollatzResearch.WordTrace]
  refine ⟨20229957160327879766084449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107893104855082025419117061 20229957160327879766084449)
  ·
    refine ⟨15172467870245909824563337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20229957160327879766084449 15172467870245909824563337)
    ·
      refine ⟨11379350902684432368422503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15172467870245909824563337 11379350902684432368422503)
      ·
        refine ⟨17069026354026648552633755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11379350902684432368422503 17069026354026648552633755)
        ·
          refine ⟨25603539531039972828950633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17069026354026648552633755 25603539531039972828950633)
          ·
            refine ⟨19202654648279979621712975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25603539531039972828950633 19202654648279979621712975)
            ·
              refine ⟨28803981972419969432569463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19202654648279979621712975 28803981972419969432569463)
              ·
                refine ⟨43205972958629954148854195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28803981972419969432569463 43205972958629954148854195)
                ·
                  refine ⟨64808959437944931223281293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43205972958629954148854195 64808959437944931223281293)
                  ·
                    refine ⟨24303359789229349208730485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64808959437944931223281293 24303359789229349208730485)
                    ·
                      refine ⟨2278439980240251488318483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24303359789229349208730485 2278439980240251488318483)
                      ·
                        rfl

theorem cell23_4437246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_4437246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437246 prefixEnd_4437246 := by exact prefixLift 4437246
  have htrace : WordTrace (prefixWord ++ tailWord_4437246) baseStart_4437246 baseEnd_4437246 := by
    simpa [prefixWord, tailWord_4437246, baseEnd_4437246] using wordTrace_append hprefix tailTrace_4437246
  have hstable : (prefixWord ++ tailWord_4437246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437246).length < 2 ^ (prefixWord ++ tailWord_4437246).sum := by decide
  have hdescent : baseEnd_4437246 < baseStart_4437246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437276 : List Nat := [2, 2, 3, 1, 1, 1, 2, 3, 2, 3, 3]
def baseStart_4437276 : Nat := 118140960795 + 4437276 * 2 ^ 59
def prefixEnd_4437276 : Nat := 4983230072969 + 3 ^ 40 * 4437276 * 2
def baseEnd_4437276 : Nat := 2278455384659886370943345

theorem tailTrace_4437276 : CollatzResearch.WordTrace tailWord_4437276 prefixEnd_4437276 2278455384659886370943345 := by
  unfold tailWord_4437276
  simp only [CollatzResearch.WordTrace]
  refine ⟨80920375736257176626133841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107893834315009568834845121 80920375736257176626133841)
  ·
    refine ⟨60690281802192882469600381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80920375736257176626133841 60690281802192882469600381)
    ·
      refine ⟨22758855675822330926100143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60690281802192882469600381 22758855675822330926100143)
      ·
        refine ⟨34138283513733496389150215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22758855675822330926100143 34138283513733496389150215)
        ·
          refine ⟨51207425270600244583725323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34138283513733496389150215 51207425270600244583725323)
          ·
            refine ⟨76811137905900366875587985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51207425270600244583725323 76811137905900366875587985)
            ·
              refine ⟨57608353429425275156690989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76811137905900366875587985 57608353429425275156690989)
              ·
                refine ⟨21603132536034478183759121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57608353429425275156690989 21603132536034478183759121)
                ·
                  refine ⟨16202349402025858637819341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21603132536034478183759121 16202349402025858637819341)
                  ·
                    refine ⟨6075881025759696989182253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16202349402025858637819341 6075881025759696989182253)
                    ·
                      refine ⟨2278455384659886370943345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6075881025759696989182253 2278455384659886370943345)
                      ·
                        rfl

theorem cell23_4437276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_4437276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437276 prefixEnd_4437276 := by exact prefixLift 4437276
  have htrace : WordTrace (prefixWord ++ tailWord_4437276) baseStart_4437276 baseEnd_4437276 := by
    simpa [prefixWord, tailWord_4437276, baseEnd_4437276] using wordTrace_append hprefix tailTrace_4437276
  have hstable : (prefixWord ++ tailWord_4437276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437276).length < 2 ^ (prefixWord ++ tailWord_4437276).sum := by decide
  have hdescent : baseEnd_4437276 < baseStart_4437276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437277 : List Nat := [1, 4, 2, 3, 1, 2, 1, 3, 2, 2, 2]
def baseStart_4437277 : Nat := 118140960795 + 4437277 * 2 ^ 59
def prefixEnd_4437277 : Nat := 4983230072969 + 3 ^ 40 * 4437277 * 2
def baseEnd_4437277 : Nat := 2278455898140540867030841

theorem tailTrace_4437277 : CollatzResearch.WordTrace tailWord_4437277 prefixEnd_4437277 2278455898140540867030841 := by
  unfold tailWord_4437277
  simp only [CollatzResearch.WordTrace]
  refine ⟨161840787945510730423054085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107893858630340486948702723 161840787945510730423054085)
  ·
    refine ⟨30345147739783261954322641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161840787945510730423054085 30345147739783261954322641)
    ·
      refine ⟨22758860804837446465741981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30345147739783261954322641 22758860804837446465741981)
      ·
        refine ⟨8534572801814042424653243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22758860804837446465741981 8534572801814042424653243)
        ·
          refine ⟨12801859202721063636979865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8534572801814042424653243 12801859202721063636979865)
          ·
            refine ⟨9601394402040797727734899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12801859202721063636979865 9601394402040797727734899)
            ·
              refine ⟨14402091603061196591602349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9601394402040797727734899 14402091603061196591602349)
              ·
                refine ⟨5400784351147948721850881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14402091603061196591602349 5400784351147948721850881)
                ·
                  refine ⟨4050588263360961541388161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5400784351147948721850881 4050588263360961541388161)
                  ·
                    refine ⟨3037941197520721156041121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4050588263360961541388161 3037941197520721156041121)
                    ·
                      refine ⟨2278455898140540867030841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3037941197520721156041121 2278455898140540867030841)
                      ·
                        rfl

theorem cell23_4437277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_4437277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437277 prefixEnd_4437277 := by exact prefixLift 4437277
  have htrace : WordTrace (prefixWord ++ tailWord_4437277) baseStart_4437277 baseEnd_4437277 := by
    simpa [prefixWord, tailWord_4437277, baseEnd_4437277] using wordTrace_append hprefix tailTrace_4437277
  have hstable : (prefixWord ++ tailWord_4437277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437277).length < 2 ^ (prefixWord ++ tailWord_4437277).sum := by decide
  have hdescent : baseEnd_4437277 < baseStart_4437277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437296 : List Nat := [2, 1, 1, 1, 2, 2, 6, 1, 2, 5]
def baseStart_4437296 : Nat := 118140960795 + 4437296 * 2 ^ 59
def prefixEnd_4437296 : Nat := 4983230072969 + 3 ^ 40 * 4437296 * 2
def baseEnd_4437296 : Nat := 759488551424325430897751

theorem tailTrace_4437296 : CollatzResearch.WordTrace tailWord_4437296 prefixEnd_4437296 759488551424325430897751 := by
  unfold tailWord_4437296
  simp only [CollatzResearch.WordTrace]
  refine ⟨80920740466220948333997871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107894320621627931111997161 80920740466220948333997871)
  ·
    refine ⟨121381110699331422500996807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80920740466220948333997871 121381110699331422500996807)
    ·
      refine ⟨182071666048997133751495211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121381110699331422500996807 182071666048997133751495211)
      ·
        refine ⟨273107499073495700627242817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182071666048997133751495211 273107499073495700627242817)
        ·
          refine ⟨204830624305121775470432113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 273107499073495700627242817 204830624305121775470432113)
          ·
            refine ⟨153622968228841331602824085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204830624305121775470432113 153622968228841331602824085)
            ·
              refine ⟨7201076635726937418882379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 153622968228841331602824085 7201076635726937418882379)
              ·
                refine ⟨10801614953590406128323569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7201076635726937418882379 10801614953590406128323569)
                ·
                  refine ⟨8101211215192804596242677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10801614953590406128323569 8101211215192804596242677)
                  ·
                    refine ⟨759488551424325430897751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8101211215192804596242677 759488551424325430897751)
                    ·
                      rfl

theorem cell23_4437296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 2, 5].length) (baseStart_4437296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437296 prefixEnd_4437296 := by exact prefixLift 4437296
  have htrace : WordTrace (prefixWord ++ tailWord_4437296) baseStart_4437296 baseEnd_4437296 := by
    simpa [prefixWord, tailWord_4437296, baseEnd_4437296] using wordTrace_append hprefix tailTrace_4437296
  have hstable : (prefixWord ++ tailWord_4437296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437296).length < 2 ^ (prefixWord ++ tailWord_4437296).sum := by decide
  have hdescent : baseEnd_4437296 < baseStart_4437296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437313 : List Nat := [1, 2, 5, 2, 1, 1, 2, 2, 2, 5]
def baseStart_4437313 : Nat := 118140960795 + 4437313 * 2 ^ 59
def prefixEnd_4437313 : Nat := 4983230072969 + 3 ^ 40 * 4437313 * 2
def baseEnd_4437313 : Nat := 759491461148034242060225

theorem tailTrace_4437313 : CollatzResearch.WordTrace tailWord_4437313 prefixEnd_4437313 759491461148034242060225 := by
  unfold tailWord_4437313
  simp only [CollatzResearch.WordTrace]
  refine ⟨161842100973380308571364593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107894733982253539047576395 161842100973380308571364593)
  ·
    refine ⟨121381575730035231428523445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161842100973380308571364593 121381575730035231428523445)
    ·
      refine ⟨11379522724690802946424073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 121381575730035231428523445 11379522724690802946424073)
      ·
        refine ⟨8534642043518102209818055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11379522724690802946424073 8534642043518102209818055)
        ·
          refine ⟨12801963065277153314727083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8534642043518102209818055 12801963065277153314727083)
          ·
            refine ⟨19202944597915729972090625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12801963065277153314727083 19202944597915729972090625)
            ·
              refine ⟨14402208448436797479067969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19202944597915729972090625 14402208448436797479067969)
              ·
                refine ⟨10801656336327598109300977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14402208448436797479067969 10801656336327598109300977)
                ·
                  refine ⟨8101242252245698581975733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10801656336327598109300977 8101242252245698581975733)
                  ·
                    refine ⟨759491461148034242060225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8101242252245698581975733 759491461148034242060225)
                    ·
                      rfl

theorem cell23_4437313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_4437313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437313 prefixEnd_4437313 := by exact prefixLift 4437313
  have htrace : WordTrace (prefixWord ++ tailWord_4437313) baseStart_4437313 baseEnd_4437313 := by
    simpa [prefixWord, tailWord_4437313, baseEnd_4437313] using wordTrace_append hprefix tailTrace_4437313
  have hstable : (prefixWord ++ tailWord_4437313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437313).length < 2 ^ (prefixWord ++ tailWord_4437313).sum := by decide
  have hdescent : baseEnd_4437313 < baseStart_4437313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437333 : List Nat := [1, 3, 2, 2, 3, 1, 1, 1, 1, 6, 2]
def baseStart_4437333 : Nat := 118140960795 + 4437333 * 2 ^ 59
def prefixEnd_4437333 : Nat := 4983230072969 + 3 ^ 40 * 4437333 * 2
def baseEnd_4437333 : Nat := 2278484653057192647930583

theorem tailTrace_4437333 : CollatzResearch.WordTrace tailWord_4437333 prefixEnd_4437333 2278484653057192647930583 := by
  unfold tailWord_4437333
  simp only [CollatzResearch.WordTrace]
  refine ⟨161842830433307851987092653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107895220288871901324728435 161842830433307851987092653)
  ·
    refine ⟨60691061412490444495159745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161842830433307851987092653 60691061412490444495159745)
    ·
      refine ⟨45518296059367833371369809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60691061412490444495159745 45518296059367833371369809)
      ·
        refine ⟨34138722044525875028527357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45518296059367833371369809 34138722044525875028527357)
        ·
          refine ⟨12802020766697203135697759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34138722044525875028527357 12802020766697203135697759)
          ·
            refine ⟨19203031150045804703546639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12802020766697203135697759 19203031150045804703546639)
            ·
              refine ⟨28804546725068707055319959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19203031150045804703546639 28804546725068707055319959)
              ·
                refine ⟨43206820087603060582979939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28804546725068707055319959 43206820087603060582979939)
                ·
                  refine ⟨64810230131404590874469909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43206820087603060582979939 64810230131404590874469909)
                  ·
                    refine ⟨3037979537409590197240777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 64810230131404590874469909 3037979537409590197240777)
                    ·
                      refine ⟨2278484653057192647930583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3037979537409590197240777 2278484653057192647930583)
                      ·
                        rfl

theorem cell23_4437333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_4437333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437333 prefixEnd_4437333 := by exact prefixLift 4437333
  have htrace : WordTrace (prefixWord ++ tailWord_4437333) baseStart_4437333 baseEnd_4437333 := by
    simpa [prefixWord, tailWord_4437333, baseEnd_4437333] using wordTrace_append hprefix tailTrace_4437333
  have hstable : (prefixWord ++ tailWord_4437333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437333).length < 2 ^ (prefixWord ++ tailWord_4437333).sum := by decide
  have hdescent : baseEnd_4437333 < baseStart_4437333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437336 : List Nat := [2, 1, 2, 2, 1, 1, 4, 2, 1, 4, 3]
def baseStart_4437336 : Nat := 118140960795 + 4437336 * 2 ^ 59
def prefixEnd_4437336 : Nat := 4983230072969 + 3 ^ 40 * 4437336 * 2
def baseEnd_4437336 : Nat := 2278486193499156136193069

theorem tailTrace_4437336 : CollatzResearch.WordTrace tailWord_4437336 prefixEnd_4437336 2278486193499156136193069 := by
  unfold tailWord_4437336
  simp only [CollatzResearch.WordTrace]
  refine ⟨80921469926148491749725931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107895293234864655666301241 80921469926148491749725931)
  ·
    refine ⟨121382204889222737624588897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80921469926148491749725931 121382204889222737624588897)
    ·
      refine ⟨91036653666917053218441673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121382204889222737624588897 91036653666917053218441673)
      ·
        refine ⟨68277490250187789913831255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91036653666917053218441673 68277490250187789913831255)
        ·
          refine ⟨102416235375281684870746883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68277490250187789913831255 102416235375281684870746883)
          ·
            refine ⟨153624353062922527306120325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102416235375281684870746883 153624353062922527306120325)
            ·
              refine ⟨28804566199297973869897561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 153624353062922527306120325 28804566199297973869897561)
              ·
                refine ⟨21603424649473480402423171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28804566199297973869897561 21603424649473480402423171)
                ·
                  refine ⟨32405136974210220603634757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21603424649473480402423171 32405136974210220603634757)
                  ·
                    refine ⟨6075963182664416363181517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32405136974210220603634757 6075963182664416363181517)
                    ·
                      refine ⟨2278486193499156136193069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6075963182664416363181517 2278486193499156136193069)
                      ·
                        rfl

theorem cell23_4437336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_4437336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437336 prefixEnd_4437336 := by exact prefixLift 4437336
  have htrace : WordTrace (prefixWord ++ tailWord_4437336) baseStart_4437336 baseEnd_4437336 := by
    simpa [prefixWord, tailWord_4437336, baseEnd_4437336] using wordTrace_append hprefix tailTrace_4437336
  have hstable : (prefixWord ++ tailWord_4437336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437336).length < 2 ^ (prefixWord ++ tailWord_4437336).sum := by decide
  have hdescent : baseEnd_4437336 < baseStart_4437336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437360 : List Nat := [2, 1, 1, 1, 4, 2, 4, 3, 1, 4]
def baseStart_4437360 : Nat := 118140960795 + 4437360 * 2 ^ 59
def prefixEnd_4437360 : Nat := 4983230072969 + 3 ^ 40 * 4437360 * 2
def baseEnd_4437360 : Nat := 759499505678288014097653

theorem tailTrace_4437360 : CollatzResearch.WordTrace tailWord_4437360 prefixEnd_4437360 759499505678288014097653 := by
  unfold tailWord_4437360
  simp only [CollatzResearch.WordTrace]
  refine ⟨80921907602105017799162767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107895876802806690398883689 80921907602105017799162767)
  ·
    refine ⟨121382861403157526698744151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80921907602105017799162767 121382861403157526698744151)
    ·
      refine ⟨182074292104736290048116227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121382861403157526698744151 182074292104736290048116227)
      ·
        refine ⟨273111438157104435072174341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182074292104736290048116227 273111438157104435072174341)
        ·
          refine ⟨51208394654457081576032689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 273111438157104435072174341 51208394654457081576032689)
          ·
            refine ⟨38406295990842811182024517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51208394654457081576032689 38406295990842811182024517)
            ·
              refine ⟨7201180498283027096629597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38406295990842811182024517 7201180498283027096629597)
              ·
                refine ⟨2700442686856135161236099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7201180498283027096629597 2700442686856135161236099)
                ·
                  refine ⟨4050664030284202741854149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2700442686856135161236099 4050664030284202741854149)
                  ·
                    refine ⟨759499505678288014097653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4050664030284202741854149 759499505678288014097653)
                    ·
                      rfl

theorem cell23_4437360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 3, 1, 4].length) (baseStart_4437360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437360 prefixEnd_4437360 := by exact prefixLift 4437360
  have htrace : WordTrace (prefixWord ++ tailWord_4437360) baseStart_4437360 baseEnd_4437360 := by
    simpa [prefixWord, tailWord_4437360, baseEnd_4437360] using wordTrace_append hprefix tailTrace_4437360
  have hstable : (prefixWord ++ tailWord_4437360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437360).length < 2 ^ (prefixWord ++ tailWord_4437360).sum := by decide
  have hdescent : baseEnd_4437360 < baseStart_4437360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437393 : List Nat := [1, 2, 2, 1, 1, 1, 2, 4, 4, 3, 2]
def baseStart_4437393 : Nat := 118140960795 + 4437393 * 2 ^ 59
def prefixEnd_4437393 : Nat := 4983230072969 + 3 ^ 40 * 4437393 * 2
def baseEnd_4437393 : Nat := 2278515461896462413180307

theorem tailTrace_4437393 : CollatzResearch.WordTrace tailWord_4437393 prefixEnd_4437393 2278515461896462413180307 := by
  unfold tailWord_4437393
  simp only [CollatzResearch.WordTrace]
  refine ⟨161845018813090482234276833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107896679208726988156184555 161845018813090482234276833)
  ·
    refine ⟨121383764109817861675707625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161845018813090482234276833 121383764109817861675707625)
    ·
      refine ⟨91037823082363396256780719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121383764109817861675707625 91037823082363396256780719)
      ·
        refine ⟨136556734623545094385171079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91037823082363396256780719 136556734623545094385171079)
        ·
          refine ⟨204835101935317641577756619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136556734623545094385171079 204835101935317641577756619)
          ·
            refine ⟨307252652902976462366634929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204835101935317641577756619 307252652902976462366634929)
            ·
              refine ⟨230439489677232346774976197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 307252652902976462366634929 230439489677232346774976197)
              ·
                refine ⟨43207404314481065020308037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 230439489677232346774976197 43207404314481065020308037)
                ·
                  refine ⟨8101388308965199691307757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43207404314481065020308037 8101388308965199691307757)
                  ·
                    refine ⟨3038020615861949884240409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8101388308965199691307757 3038020615861949884240409)
                    ·
                      refine ⟨2278515461896462413180307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3038020615861949884240409 2278515461896462413180307)
                      ·
                        rfl

theorem cell23_4437393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 3, 2].length) (baseStart_4437393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437393 prefixEnd_4437393 := by exact prefixLift 4437393
  have htrace : WordTrace (prefixWord ++ tailWord_4437393) baseStart_4437393 baseEnd_4437393 := by
    simpa [prefixWord, tailWord_4437393, baseEnd_4437393] using wordTrace_append hprefix tailTrace_4437393
  have hstable : (prefixWord ++ tailWord_4437393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437393).length < 2 ^ (prefixWord ++ tailWord_4437393).sum := by decide
  have hdescent : baseEnd_4437393 < baseStart_4437393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437410 : List Nat := [3, 3, 1, 2, 1, 2, 2, 1, 1, 5, 2]
def baseStart_4437410 : Nat := 118140960795 + 4437410 * 2 ^ 59
def prefixEnd_4437410 : Nat := 4983230072969 + 3 ^ 40 * 4437410 * 2
def baseEnd_4437410 : Nat := 2278524191067588846667729

theorem tailTrace_4437410 : CollatzResearch.WordTrace tailWord_4437410 prefixEnd_4437410 2278524191067588846667729 := by
  unfold tailWord_4437410
  simp only [CollatzResearch.WordTrace]
  refine ⟨40461409713507223534411421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107897092569352596091763789 40461409713507223534411421)
  ·
    refine ⟨15173028642565208825404283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40461409713507223534411421 15173028642565208825404283)
    ·
      refine ⟨22759542963847813238106425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15173028642565208825404283 22759542963847813238106425)
      ·
        refine ⟨17069657222885859928579819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22759542963847813238106425 17069657222885859928579819)
        ·
          refine ⟨25604485834328789892869729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17069657222885859928579819 25604485834328789892869729)
          ·
            refine ⟨19203364375746592419652297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25604485834328789892869729 19203364375746592419652297)
            ·
              refine ⟨14402523281809944314739223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19203364375746592419652297 14402523281809944314739223)
              ·
                refine ⟨21603784922714916472108835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14402523281809944314739223 21603784922714916472108835)
                ·
                  refine ⟨32405677384072374708163253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21603784922714916472108835 32405677384072374708163253)
                  ·
                    refine ⟨3038032254756785128890305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32405677384072374708163253 3038032254756785128890305)
                    ·
                      refine ⟨2278524191067588846667729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3038032254756785128890305 2278524191067588846667729)
                      ·
                        rfl

theorem cell23_4437410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_4437410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437410 prefixEnd_4437410 := by exact prefixLift 4437410
  have htrace : WordTrace (prefixWord ++ tailWord_4437410) baseStart_4437410 baseEnd_4437410 := by
    simpa [prefixWord, tailWord_4437410, baseEnd_4437410] using wordTrace_append hprefix tailTrace_4437410
  have hstable : (prefixWord ++ tailWord_4437410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437410).length < 2 ^ (prefixWord ++ tailWord_4437410).sum := by decide
  have hdescent : baseEnd_4437410 < baseStart_4437410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437450 : List Nat := [3, 1, 2, 1, 2, 4, 1, 3, 2, 4]
def baseStart_4437450 : Nat := 118140960795 + 4437450 * 2 ^ 59
def prefixEnd_4437450 : Nat := 4983230072969 + 3 ^ 40 * 4437450 * 2
def baseEnd_4437450 : Nat := 759514910097922896722515

theorem tailTrace_4437450 : CollatzResearch.WordTrace tailWord_4437450 prefixEnd_4437450 759514910097922896722515 := by
  unfold tailWord_4437450
  simp only [CollatzResearch.WordTrace]
  refine ⟨40461774443470995242275451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107898065182589320646067869 40461774443470995242275451)
  ·
    refine ⟨60692661665206492863413177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40461774443470995242275451 60692661665206492863413177)
    ·
      refine ⟨45519496248904869647559883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60692661665206492863413177 45519496248904869647559883)
      ·
        refine ⟨68279244373357304471339825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45519496248904869647559883 68279244373357304471339825)
        ·
          refine ⟨51209433280017978353504869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68279244373357304471339825 51209433280017978353504869)
          ·
            refine ⟨9601768740003370941282163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51209433280017978353504869 9601768740003370941282163)
            ·
              refine ⟨14402653110005056411923245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9601768740003370941282163 14402653110005056411923245)
              ·
                refine ⟨5400994916251896154471217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14402653110005056411923245 5400994916251896154471217)
                ·
                  refine ⟨4050746187188922115853413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5400994916251896154471217 4050746187188922115853413)
                  ·
                    refine ⟨759514910097922896722515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4050746187188922115853413 759514910097922896722515)
                    ·
                      rfl

theorem cell23_4437450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_4437450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437450 prefixEnd_4437450 := by exact prefixLift 4437450
  have htrace : WordTrace (prefixWord ++ tailWord_4437450) baseStart_4437450 baseEnd_4437450 := by
    simpa [prefixWord, tailWord_4437450, baseEnd_4437450] using wordTrace_append hprefix tailTrace_4437450
  have hstable : (prefixWord ++ tailWord_4437450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437450).length < 2 ^ (prefixWord ++ tailWord_4437450).sum := by decide
  have hdescent : baseEnd_4437450 < baseStart_4437450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437473 : List Nat := [1, 2, 3, 1, 2, 3, 1, 1, 3, 3, 3]
def baseStart_4437473 : Nat := 118140960795 + 4437473 * 2 ^ 59
def prefixEnd_4437473 : Nat := 4983230072969 + 3 ^ 40 * 4437473 * 2
def baseEnd_4437473 : Nat := 2278556540348822100179939

theorem tailTrace_4437473 : CollatzResearch.WordTrace tailWord_4437473 prefixEnd_4437473 2278556540348822100179939 := by
  unfold tailWord_4437473
  simp only [CollatzResearch.WordTrace]
  refine ⟨161847936652800655897189073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107898624435200437264792715 161847936652800655897189073)
  ·
    refine ⟨121385952489600491922891805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161847936652800655897189073 121385952489600491922891805)
    ·
      refine ⟨45519732183600184471084427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121385952489600491922891805 45519732183600184471084427)
      ·
        refine ⟨68279598275400276706626641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45519732183600184471084427 68279598275400276706626641)
        ·
          refine ⟨51209698706550207529969981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68279598275400276706626641 51209698706550207529969981)
          ·
            refine ⟨19203637014956327823738743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51209698706550207529969981 19203637014956327823738743)
            ·
              refine ⟨28805455522434491735608115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19203637014956327823738743 28805455522434491735608115)
              ·
                refine ⟨43208183283651737603412173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28805455522434491735608115 43208183283651737603412173)
                ·
                  refine ⟨16203068731369401601279565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43208183283651737603412173 16203068731369401601279565)
                  ·
                    refine ⟨6076150774263525600479837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16203068731369401601279565 6076150774263525600479837)
                    ·
                      refine ⟨2278556540348822100179939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6076150774263525600479837 2278556540348822100179939)
                      ·
                        rfl

theorem cell23_4437473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_4437473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437473 prefixEnd_4437473 := by exact prefixLift 4437473
  have htrace : WordTrace (prefixWord ++ tailWord_4437473) baseStart_4437473 baseEnd_4437473 := by
    simpa [prefixWord, tailWord_4437473, baseEnd_4437473] using wordTrace_append hprefix tailTrace_4437473
  have hstable : (prefixWord ++ tailWord_4437473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437473).length < 2 ^ (prefixWord ++ tailWord_4437473).sum := by decide
  have hdescent : baseEnd_4437473 < baseStart_4437473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437476 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 4, 7]
def baseStart_4437476 : Nat := 118140960795 + 4437476 * 2 ^ 59
def prefixEnd_4437476 : Nat := 4983230072969 + 3 ^ 40 * 4437476 * 2
def baseEnd_4437476 : Nat := 759519360263595196147475

theorem tailTrace_4437476 : CollatzResearch.WordTrace tailWord_4437476 prefixEnd_4437476 759519360263595196147475 := by
  unfold tailWord_4437476
  simp only [CollatzResearch.WordTrace]
  refine ⟨80924023035894893704774141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107898697381193191606365521 80924023035894893704774141)
  ·
    refine ⟨30346508638460585139290303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80924023035894893704774141 30346508638460585139290303)
    ·
      refine ⟨45519762957690877708935455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30346508638460585139290303 45519762957690877708935455)
      ·
        refine ⟨68279644436536316563403183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45519762957690877708935455 68279644436536316563403183)
        ·
          refine ⟨102419466654804474845104775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68279644436536316563403183 102419466654804474845104775)
          ·
            refine ⟨153629199982206712267657163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102419466654804474845104775 153629199982206712267657163)
            ·
              refine ⟨230443799973310068401485745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153629199982206712267657163 230443799973310068401485745)
              ·
                refine ⟨172832849979982551301114309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 230443799973310068401485745 172832849979982551301114309)
                ·
                  refine ⟨32406159371246728368958933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 172832849979982551301114309 32406159371246728368958933)
                  ·
                    refine ⟨759519360263595196147475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32406159371246728368958933 759519360263595196147475)
                    ·
                      rfl

theorem cell23_4437476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_4437476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437476 prefixEnd_4437476 := by exact prefixLift 4437476
  have htrace : WordTrace (prefixWord ++ tailWord_4437476) baseStart_4437476 baseEnd_4437476 := by
    simpa [prefixWord, tailWord_4437476, baseEnd_4437476] using wordTrace_append hprefix tailTrace_4437476
  have hstable : (prefixWord ++ tailWord_4437476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437476).length < 2 ^ (prefixWord ++ tailWord_4437476).sum := by decide
  have hdescent : baseEnd_4437476 < baseStart_4437476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437500 : List Nat := [2, 2, 2, 1, 2, 1, 3, 2, 3, 3, 2]
def baseStart_4437500 : Nat := 118140960795 + 4437500 * 2 ^ 59
def prefixEnd_4437500 : Nat := 4983230072969 + 3 ^ 40 * 4437500 * 2
def baseEnd_4437500 : Nat := 2278570404326493494542315

theorem tailTrace_4437500 : CollatzResearch.WordTrace tailWord_4437500 prefixEnd_4437500 2278570404326493494542315 := by
  unfold tailWord_4437500
  simp only [CollatzResearch.WordTrace]
  refine ⟨80924460711851419754210977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107899280949135226338947969 80924460711851419754210977)
  ·
    refine ⟨60693345533888564815658233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80924460711851419754210977 60693345533888564815658233)
    ·
      refine ⟨45520009150416423611743675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60693345533888564815658233 45520009150416423611743675)
      ·
        refine ⟨68280013725624635417615513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45520009150416423611743675 68280013725624635417615513)
        ·
          refine ⟨51210010294218476563211635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68280013725624635417615513 51210010294218476563211635)
          ·
            refine ⟨76815015441327714844817453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51210010294218476563211635 76815015441327714844817453)
            ·
              refine ⟨28805630790497893066806545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76815015441327714844817453 28805630790497893066806545)
              ·
                refine ⟨21604223092873419800104909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28805630790497893066806545 21604223092873419800104909)
                ·
                  refine ⟨8101583659827532425039341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21604223092873419800104909 8101583659827532425039341)
                  ·
                    refine ⟨3038093872435324659389753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8101583659827532425039341 3038093872435324659389753)
                    ·
                      refine ⟨2278570404326493494542315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3038093872435324659389753 2278570404326493494542315)
                      ·
                        rfl

theorem cell23_4437500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 3, 3, 2].length) (baseStart_4437500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437500 prefixEnd_4437500 := by exact prefixLift 4437500
  have htrace : WordTrace (prefixWord ++ tailWord_4437500) baseStart_4437500 baseEnd_4437500 := by
    simpa [prefixWord, tailWord_4437500, baseEnd_4437500] using wordTrace_append hprefix tailTrace_4437500
  have hstable : (prefixWord ++ tailWord_4437500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437500).length < 2 ^ (prefixWord ++ tailWord_4437500).sum := by decide
  have hdescent : baseEnd_4437500 < baseStart_4437500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437533 : List Nat := [1, 4, 2, 2, 1, 1, 2, 1, 1, 3, 5]
def baseStart_4437533 : Nat := 118140960795 + 4437533 * 2 ^ 59
def prefixEnd_4437533 : Nat := 4983230072969 + 3 ^ 40 * 4437533 * 2
def baseEnd_4437533 : Nat := 2278587349188091865429663

theorem tailTrace_4437533 : CollatzResearch.WordTrace tailWord_4437533 prefixEnd_4437533 2278587349188091865429663 := by
  unfold tailWord_4437533
  simp only [CollatzResearch.WordTrace]
  refine ⟨161850125032583286144373253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107900083355055524096248835 161850125032583286144373253)
  ·
    refine ⟨30346898443609366152069985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161850125032583286144373253 30346898443609366152069985)
    ·
      refine ⟨22760173832707024614052489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30346898443609366152069985 22760173832707024614052489)
      ·
        refine ⟨17070130374530268460539367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22760173832707024614052489 17070130374530268460539367)
        ·
          refine ⟨25605195561795402690809051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17070130374530268460539367 25605195561795402690809051)
          ·
            refine ⟨38407793342693104036213577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25605195561795402690809051 38407793342693104036213577)
            ·
              refine ⟨28805845007019828027160183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38407793342693104036213577 28805845007019828027160183)
              ·
                refine ⟨43208767510529742040740275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28805845007019828027160183 43208767510529742040740275)
                ·
                  refine ⟨64813151265794613061110413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43208767510529742040740275 64813151265794613061110413)
                  ·
                    refine ⟨24304931724672979897916405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64813151265794613061110413 24304931724672979897916405)
                    ·
                      refine ⟨2278587349188091865429663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24304931724672979897916405 2278587349188091865429663)
                      ·
                        rfl

theorem cell23_4437533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_4437533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437533 prefixEnd_4437533 := by exact prefixLift 4437533
  have htrace : WordTrace (prefixWord ++ tailWord_4437533) baseStart_4437533 baseEnd_4437533 := by
    simpa [prefixWord, tailWord_4437533, baseEnd_4437533] using wordTrace_append hprefix tailTrace_4437533
  have hstable : (prefixWord ++ tailWord_4437533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437533).length < 2 ^ (prefixWord ++ tailWord_4437533).sum := by decide
  have hdescent : baseEnd_4437533 < baseStart_4437533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437564 : List Nat := [2, 2, 2, 2, 4, 2, 1, 1, 1, 4, 2]
def baseStart_4437564 : Nat := 118140960795 + 4437564 * 2 ^ 59
def prefixEnd_4437564 : Nat := 4983230072969 + 3 ^ 40 * 4437564 * 2
def baseEnd_4437564 : Nat := 2278603267088381244142021

theorem tailTrace_4437564 : CollatzResearch.WordTrace tailWord_4437564 prefixEnd_4437564 2278603267088381244142021 := by
  unfold tailWord_4437564
  simp only [CollatzResearch.WordTrace]
  refine ⟨80925627847735489219375873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107900837130313985625834497 80925627847735489219375873)
  ·
    refine ⟨60694220885801616914531905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80925627847735489219375873 60694220885801616914531905)
    ·
      refine ⟨45520665664351212685898929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60694220885801616914531905 45520665664351212685898929)
      ·
        refine ⟨34140499248263409514424197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45520665664351212685898929 34140499248263409514424197)
        ·
          refine ⟨6401343609049389283954537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34140499248263409514424197 6401343609049389283954537)
          ·
            refine ⟨4801007706787041962965903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6401343609049389283954537 4801007706787041962965903)
            ·
              refine ⟨7201511560180562944448855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4801007706787041962965903 7201511560180562944448855)
              ·
                refine ⟨10802267340270844416673283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7201511560180562944448855 10802267340270844416673283)
                ·
                  refine ⟨16203401010406266625009925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10802267340270844416673283 16203401010406266625009925)
                  ·
                    refine ⟨3038137689451174992189361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16203401010406266625009925 3038137689451174992189361)
                    ·
                      refine ⟨2278603267088381244142021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3038137689451174992189361 2278603267088381244142021)
                      ·
                        rfl

theorem cell23_4437564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_4437564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437564 prefixEnd_4437564 := by exact prefixLift 4437564
  have htrace : WordTrace (prefixWord ++ tailWord_4437564) baseStart_4437564 baseEnd_4437564 := by
    simpa [prefixWord, tailWord_4437564, baseEnd_4437564] using wordTrace_append hprefix tailTrace_4437564
  have hstable : (prefixWord ++ tailWord_4437564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437564).length < 2 ^ (prefixWord ++ tailWord_4437564).sum := by decide
  have hdescent : baseEnd_4437564 < baseStart_4437564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437583 : List Nat := [1, 1, 2, 1, 1, 2, 3, 5, 2, 5]
def baseStart_4437583 : Nat := 118140960795 + 4437583 * 2 ^ 59
def prefixEnd_4437583 : Nat := 4983230072969 + 3 ^ 40 * 4437583 * 2
def baseEnd_4437583 : Nat := 759537674406938889934811

theorem tailTrace_4437583 : CollatzResearch.WordTrace tailWord_4437583 prefixEnd_4437583 759537674406938889934811 := by
  unfold tailWord_4437583
  simp only [CollatzResearch.WordTrace]
  refine ⟨161851948682402144683693403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107901299121601429789128935 161851948682402144683693403)
  ·
    refine ⟨242777923023603217025540105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161851948682402144683693403 242777923023603217025540105)
    ·
      refine ⟨182083442267702412769155079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242777923023603217025540105 182083442267702412769155079)
      ·
        refine ⟨273125163401553619153732619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182083442267702412769155079 273125163401553619153732619)
        ·
          refine ⟨409687745102330428730598929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273125163401553619153732619 409687745102330428730598929)
          ·
            refine ⟨307265808826747821547949197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 409687745102330428730598929 307265808826747821547949197)
            ·
              refine ⟨115224678310030433080480949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 307265808826747821547949197 115224678310030433080480949)
              ·
                refine ⟨10802313591565353101295089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 115224678310030433080480949 10802313591565353101295089)
                ·
                  refine ⟨8101735193674014825971317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10802313591565353101295089 8101735193674014825971317)
                  ·
                    refine ⟨759537674406938889934811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8101735193674014825971317 759537674406938889934811)
                    ·
                      rfl

theorem cell23_4437583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 5].length) (baseStart_4437583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437583 prefixEnd_4437583 := by exact prefixLift 4437583
  have htrace : WordTrace (prefixWord ++ tailWord_4437583) baseStart_4437583 baseEnd_4437583 := by
    simpa [prefixWord, tailWord_4437583, baseEnd_4437583] using wordTrace_append hprefix tailTrace_4437583
  have hstable : (prefixWord ++ tailWord_4437583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437583).length < 2 ^ (prefixWord ++ tailWord_4437583).sum := by decide
  have hdescent : baseEnd_4437583 < baseStart_4437583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437610 : List Nat := [3, 1, 3, 2, 1, 3, 1, 1, 1, 2, 5]
def baseStart_4437610 : Nat := 118140960795 + 4437610 * 2 ^ 59
def prefixEnd_4437610 : Nat := 4983230072969 + 3 ^ 40 * 4437610 * 2
def baseEnd_4437610 : Nat := 2278626887198488064166809

theorem tailTrace_4437610 : CollatzResearch.WordTrace tailWord_4437610 prefixEnd_4437610 2278626887198488064166809 := by
  unfold tailWord_4437610
  simp only [CollatzResearch.WordTrace]
  refine ⟨40463233363326082073731571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107901955635536218863284189 40463233363326082073731571)
  ·
    refine ⟨60694850044989123110597357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40463233363326082073731571 60694850044989123110597357)
    ·
      refine ⟨22760568766870921166474009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60694850044989123110597357 22760568766870921166474009)
      ·
        refine ⟨17070426575153190874855507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22760568766870921166474009 17070426575153190874855507)
        ·
          refine ⟨25605639862729786312283261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17070426575153190874855507 25605639862729786312283261)
          ·
            refine ⟨9602114948523669867106223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25605639862729786312283261 9602114948523669867106223)
            ·
              refine ⟨14403172422785504800659335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9602114948523669867106223 14403172422785504800659335)
              ·
                refine ⟨21604758634178257200989003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14403172422785504800659335 21604758634178257200989003)
                ·
                  refine ⟨32407137951267385801483505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21604758634178257200989003 32407137951267385801483505)
                  ·
                    refine ⟨24305353463450539351112629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32407137951267385801483505 24305353463450539351112629)
                    ·
                      refine ⟨2278626887198488064166809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24305353463450539351112629 2278626887198488064166809)
                      ·
                        rfl

theorem cell23_4437610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_4437610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437610 prefixEnd_4437610 := by exact prefixLift 4437610
  have htrace : WordTrace (prefixWord ++ tailWord_4437610) baseStart_4437610 baseEnd_4437610 := by
    simpa [prefixWord, tailWord_4437610, baseEnd_4437610] using wordTrace_append hprefix tailTrace_4437610
  have hstable : (prefixWord ++ tailWord_4437610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437610).length < 2 ^ (prefixWord ++ tailWord_4437610).sum := by decide
  have hdescent : baseEnd_4437610 < baseStart_4437610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437664 : List Nat := [2, 1, 1, 4, 3, 2, 1, 4, 1, 4]
def baseStart_4437664 : Nat := 118140960795 + 4437664 * 2 ^ 59
def prefixEnd_4437664 : Nat := 4983230072969 + 3 ^ 40 * 4437664 * 2
def baseEnd_4437664 : Nat := 759551538384610284297187

theorem tailTrace_4437664 : CollatzResearch.WordTrace tailWord_4437664 prefixEnd_4437664 759551538384610284297187 := by
  unfold tailWord_4437664
  simp only [CollatzResearch.WordTrace]
  refine ⟨80927451497554347758696023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107903268663405797011594697 80927451497554347758696023)
  ·
    refine ⟨121391177246331521638044035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80927451497554347758696023 121391177246331521638044035)
    ·
      refine ⟨182086765869497282457066053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121391177246331521638044035 182086765869497282457066053)
      ·
        refine ⟨34141268600530740460699885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 182086765869497282457066053 34141268600530740460699885)
        ·
          refine ⟨12802975725199027672762457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34141268600530740460699885 12802975725199027672762457)
          ·
            refine ⟨9602231793899270754571843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12802975725199027672762457 9602231793899270754571843)
            ·
              refine ⟨14403347690848906131857765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9602231793899270754571843 14403347690848906131857765)
              ·
                refine ⟨2700627692034169899723331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14403347690848906131857765 2700627692034169899723331)
                ·
                  refine ⟨4050941538051254849584997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2700627692034169899723331 4050941538051254849584997)
                  ·
                    refine ⟨759551538384610284297187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4050941538051254849584997 759551538384610284297187)
                    ·
                      rfl

theorem cell23_4437664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 4, 1, 4].length) (baseStart_4437664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437664 prefixEnd_4437664 := by exact prefixLift 4437664
  have htrace : WordTrace (prefixWord ++ tailWord_4437664) baseStart_4437664 baseEnd_4437664 := by
    simpa [prefixWord, tailWord_4437664, baseEnd_4437664] using wordTrace_append hprefix tailTrace_4437664
  have hstable : (prefixWord ++ tailWord_4437664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437664).length < 2 ^ (prefixWord ++ tailWord_4437664).sum := by decide
  have hdescent : baseEnd_4437664 < baseStart_4437664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437683 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 7]
def baseStart_4437683 : Nat := 118140960795 + 4437683 * 2 ^ 59
def prefixEnd_4437683 : Nat := 4983230072969 + 3 ^ 40 * 4437683 * 2
def baseEnd_4437683 : Nat := 2278664371286266278553973

theorem tailTrace_4437683 : CollatzResearch.WordTrace tailWord_4437683 prefixEnd_4437683 2278664371286266278553973 := by
  unfold tailWord_4437683
  simp only [CollatzResearch.WordTrace]
  refine ⟨161855595982039861762333703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107903730654693241174889135 161855595982039861762333703)
  ·
    refine ⟨242783393973059792643500555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161855595982039861762333703 242783393973059792643500555)
    ·
      refine ⟨364175090959589688965250833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242783393973059792643500555 364175090959589688965250833)
      ·
        refine ⟨273131318219692266723938125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 364175090959589688965250833 273131318219692266723938125)
        ·
          refine ⟨102424244332384600021476797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 273131318219692266723938125 102424244332384600021476797)
          ·
            refine ⟨38409091624644225008053799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102424244332384600021476797 38409091624644225008053799)
            ·
              refine ⟨57613637436966337512080699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38409091624644225008053799 57613637436966337512080699)
              ·
                refine ⟨86420456155449506268121049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57613637436966337512080699 86420456155449506268121049)
                ·
                  refine ⟨64815342116587129701090787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86420456155449506268121049 64815342116587129701090787)
                  ·
                    refine ⟨97223013174880694551636181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 64815342116587129701090787 97223013174880694551636181)
                    ·
                      refine ⟨2278664371286266278553973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 97223013174880694551636181 2278664371286266278553973)
                      ·
                        rfl

theorem cell23_4437683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 7].length) (baseStart_4437683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437683 prefixEnd_4437683 := by exact prefixLift 4437683
  have htrace : WordTrace (prefixWord ++ tailWord_4437683) baseStart_4437683 baseEnd_4437683 := by
    simpa [prefixWord, tailWord_4437683, baseEnd_4437683] using wordTrace_append hprefix tailTrace_4437683
  have hstable : (prefixWord ++ tailWord_4437683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437683).length < 2 ^ (prefixWord ++ tailWord_4437683).sum := by decide
  have hdescent : baseEnd_4437683 < baseStart_4437683 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437687 : List Nat := [1, 1, 3, 1, 5, 1, 1, 1, 5, 1, 3]
def baseStart_4437687 : Nat := 118140960795 + 4437687 * 2 ^ 59
def prefixEnd_4437687 : Nat := 4983230072969 + 3 ^ 40 * 4437687 * 2
def baseEnd_4437687 : Nat := 2278666425208884262903955

theorem tailTrace_4437687 : CollatzResearch.WordTrace tailWord_4437687 prefixEnd_4437687 2278666425208884262903955 := by
  unfold tailWord_4437687
  simp only [CollatzResearch.WordTrace]
  refine ⟨161855741874025370445479315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107903827916016913630319543 161855741874025370445479315)
  ·
    refine ⟨242783612811038055668218973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161855741874025370445479315 242783612811038055668218973)
    ·
      refine ⟨91043854804139270875582115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 242783612811038055668218973 91043854804139270875582115)
      ·
        refine ⟨136565782206208906313373173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91043854804139270875582115 136565782206208906313373173)
        ·
          refine ⟨12803042081832084966878735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 136565782206208906313373173 12803042081832084966878735)
          ·
            refine ⟨19204563122748127450318103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12803042081832084966878735 19204563122748127450318103)
            ·
              refine ⟨28806844684122191175477155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19204563122748127450318103 28806844684122191175477155)
              ·
                refine ⟨43210267026183286763215733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28806844684122191175477155 43210267026183286763215733)
                ·
                  refine ⟨4050962533704683134051475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43210267026183286763215733 4050962533704683134051475)
                  ·
                    refine ⟨6076443800557024701077213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4050962533704683134051475 6076443800557024701077213)
                    ·
                      refine ⟨2278666425208884262903955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6076443800557024701077213 2278666425208884262903955)
                      ·
                        rfl

theorem cell23_4437687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 5, 1, 3].length) (baseStart_4437687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437687 prefixEnd_4437687 := by exact prefixLift 4437687
  have htrace : WordTrace (prefixWord ++ tailWord_4437687) baseStart_4437687 baseEnd_4437687 := by
    simpa [prefixWord, tailWord_4437687, baseEnd_4437687] using wordTrace_append hprefix tailTrace_4437687
  have hstable : (prefixWord ++ tailWord_4437687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437687).length < 2 ^ (prefixWord ++ tailWord_4437687).sum := by decide
  have hdescent : baseEnd_4437687 < baseStart_4437687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437690 : List Nat := [3, 1, 1, 1, 2, 4, 2, 1, 3, 5]
def baseStart_4437690 : Nat := 118140960795 + 4437690 * 2 ^ 59
def prefixEnd_4437690 : Nat := 4983230072969 + 3 ^ 40 * 4437690 * 2
def baseEnd_4437690 : Nat := 759555988550282583722147

theorem tailTrace_4437690 : CollatzResearch.WordTrace tailWord_4437690 prefixEnd_4437690 759555988550282583722147 := by
  unfold tailWord_4437690
  simp only [CollatzResearch.WordTrace]
  refine ⟨40463962823253625489459631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107903900862009667971892349 40463962823253625489459631)
  ·
    refine ⟨60695944234880438234189447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40463962823253625489459631 60695944234880438234189447)
    ·
      refine ⟨91043916352320657351284171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60695944234880438234189447 91043916352320657351284171)
      ·
        refine ⟨136565874528480986026926257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91043916352320657351284171 136565874528480986026926257)
        ·
          refine ⟨102424405896360739520194693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136565874528480986026926257 102424405896360739520194693)
          ·
            refine ⟨19204576105567638660036505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102424405896360739520194693 19204576105567638660036505)
            ·
              refine ⟨14403432079175728995027379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19204576105567638660036505 14403432079175728995027379)
              ·
                refine ⟨21605148118763593492541069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14403432079175728995027379 21605148118763593492541069)
                ·
                  refine ⟨8101930544536347559702901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21605148118763593492541069 8101930544536347559702901)
                  ·
                    refine ⟨759555988550282583722147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8101930544536347559702901 759555988550282583722147)
                    ·
                      rfl

theorem cell23_4437690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 3, 5].length) (baseStart_4437690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437690 prefixEnd_4437690 := by exact prefixLift 4437690
  have htrace : WordTrace (prefixWord ++ tailWord_4437690) baseStart_4437690 baseEnd_4437690 := by
    simpa [prefixWord, tailWord_4437690, baseEnd_4437690] using wordTrace_append hprefix tailTrace_4437690
  have hstable : (prefixWord ++ tailWord_4437690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437690).length < 2 ^ (prefixWord ++ tailWord_4437690).sum := by decide
  have hdescent : baseEnd_4437690 < baseStart_4437690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437747 : List Nat := [1, 1, 1, 2, 2, 3, 3, 4, 1, 2, 3]
def baseStart_4437747 : Nat := 118140960795 + 4437747 * 2 ^ 59
def prefixEnd_4437747 : Nat := 4983230072969 + 3 ^ 40 * 4437747 * 2
def baseEnd_4437747 : Nat := 2278697234048154028153679

theorem tailTrace_4437747 : CollatzResearch.WordTrace tailWord_4437747 prefixEnd_4437747 2278697234048154028153679 := by
  unfold tailWord_4437747
  simp only [CollatzResearch.WordTrace]
  refine ⟨161857930253808000692663495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107905286835872000461775663 161857930253808000692663495)
  ·
    refine ⟨242786895380712001038995243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161857930253808000692663495 242786895380712001038995243)
    ·
      refine ⟨364180343071068001558492865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242786895380712001038995243 364180343071068001558492865)
      ·
        refine ⟨273135257303301001168869649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 364180343071068001558492865 273135257303301001168869649)
        ·
          refine ⟨204851442977475750876652237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 273135257303301001168869649 204851442977475750876652237)
          ·
            refine ⟨76819291116553406578744589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 204851442977475750876652237 76819291116553406578744589)
            ·
              refine ⟨28807234168707527467029221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76819291116553406578744589 28807234168707527467029221)
              ·
                refine ⟨5401356406632661400067979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28807234168707527467029221 5401356406632661400067979)
                ·
                  refine ⟨8102034609948992100101969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5401356406632661400067979 8102034609948992100101969)
                  ·
                    refine ⟨6076525957461744075076477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8102034609948992100101969 6076525957461744075076477)
                    ·
                      refine ⟨2278697234048154028153679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6076525957461744075076477 2278697234048154028153679)
                      ·
                        rfl

theorem cell23_4437747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 2, 3].length) (baseStart_4437747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437747 prefixEnd_4437747 := by exact prefixLift 4437747
  have htrace : WordTrace (prefixWord ++ tailWord_4437747) baseStart_4437747 baseEnd_4437747 := by
    simpa [prefixWord, tailWord_4437747, baseEnd_4437747] using wordTrace_append hprefix tailTrace_4437747
  have hstable : (prefixWord ++ tailWord_4437747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437747).length < 2 ^ (prefixWord ++ tailWord_4437747).sum := by decide
  have hdescent : baseEnd_4437747 < baseStart_4437747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437764 : List Nat := [2, 3, 2, 2, 1, 2, 2, 3, 1, 2, 3]
def baseStart_4437764 : Nat := 118140960795 + 4437764 * 2 ^ 59
def prefixEnd_4437764 : Nat := 4983230072969 + 3 ^ 40 * 4437764 * 2
def baseEnd_4437764 : Nat := 2278705963219280461641101

theorem tailTrace_4437764 : CollatzResearch.WordTrace tailWord_4437764 prefixEnd_4437764 2278705963219280461641101 := by
  unfold tailWord_4437764
  simp only [CollatzResearch.WordTrace]
  refine ⟨80929275147373206298016173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107905700196497608397354897 80929275147373206298016173)
  ·
    refine ⟨30348478180264952361756065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80929275147373206298016173 30348478180264952361756065)
    ·
      refine ⟨22761358635198714271317049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30348478180264952361756065 22761358635198714271317049)
      ·
        refine ⟨17071018976399035703487787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22761358635198714271317049 17071018976399035703487787)
        ·
          refine ⟨25606528464598553555231681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17071018976399035703487787 25606528464598553555231681)
          ·
            refine ⟨19204896348448915166423761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25606528464598553555231681 19204896348448915166423761)
            ·
              refine ⟨14403672261336686374817821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19204896348448915166423761 14403672261336686374817821)
              ·
                refine ⟨5401377098001257390556683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14403672261336686374817821 5401377098001257390556683)
                ·
                  refine ⟨8102065647001886085835025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5401377098001257390556683 8102065647001886085835025)
                  ·
                    refine ⟨6076549235251414564376269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8102065647001886085835025 6076549235251414564376269)
                    ·
                      refine ⟨2278705963219280461641101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6076549235251414564376269 2278705963219280461641101)
                      ·
                        rfl

theorem cell23_4437764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_4437764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437764 prefixEnd_4437764 := by exact prefixLift 4437764
  have htrace : WordTrace (prefixWord ++ tailWord_4437764) baseStart_4437764 baseEnd_4437764 := by
    simpa [prefixWord, tailWord_4437764, baseEnd_4437764] using wordTrace_append hprefix tailTrace_4437764
  have hstable : (prefixWord ++ tailWord_4437764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437764).length < 2 ^ (prefixWord ++ tailWord_4437764).sum := by decide
  have hdescent : baseEnd_4437764 < baseStart_4437764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437767 : List Nat := [1, 1, 4, 4, 2, 2, 9]
def baseStart_4437767 : Nat := 118140960795 + 4437767 * 2 ^ 59
def prefixEnd_4437767 : Nat := 4983230072969 + 3 ^ 40 * 4437767 * 2
def baseEnd_4437767 : Nat := 28132191403225233949427

theorem tailTrace_4437767 : CollatzResearch.WordTrace tailWord_4437767 prefixEnd_4437767 28132191403225233949427 := by
  unfold tailWord_4437767
  simp only [CollatzResearch.WordTrace]
  refine ⟨161858659713735544108391555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107905773142490362738927703 161858659713735544108391555)
  ·
    refine ⟨242787989570603316162587333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161858659713735544108391555 242787989570603316162587333)
    ·
      refine ⟨45522748044488121780485125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 242787989570603316162587333 45522748044488121780485125)
      ·
        refine ⟨8535515258341522833840961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45522748044488121780485125 8535515258341522833840961)
        ·
          refine ⟨6401636443756142125380721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8535515258341522833840961 6401636443756142125380721)
          ·
            refine ⟨4801227332817106594035541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6401636443756142125380721 4801227332817106594035541)
            ·
              refine ⟨28132191403225233949427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4801227332817106594035541 28132191403225233949427)
              ·
                rfl

theorem cell23_4437767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 9].length) (baseStart_4437767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437767 prefixEnd_4437767 := by exact prefixLift 4437767
  have htrace : WordTrace (prefixWord ++ tailWord_4437767) baseStart_4437767 baseEnd_4437767 := by
    simpa [prefixWord, tailWord_4437767, baseEnd_4437767] using wordTrace_append hprefix tailTrace_4437767
  have hstable : (prefixWord ++ tailWord_4437767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437767).length < 2 ^ (prefixWord ++ tailWord_4437767).sum := by decide
  have hdescent : baseEnd_4437767 < baseStart_4437767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437778 : List Nat := [3, 2, 4, 1, 1, 1, 3, 1, 3, 2, 2]
def baseStart_4437778 : Nat := 118140960795 + 4437778 * 2 ^ 59
def prefixEnd_4437778 : Nat := 4983230072969 + 3 ^ 40 * 4437778 * 2
def baseEnd_4437778 : Nat := 2278713151948443406866037

theorem tailTrace_4437778 : CollatzResearch.WordTrace tailWord_4437778 prefixEnd_4437778 2278713151948443406866037 := by
  unfold tailWord_4437778
  simp only [CollatzResearch.WordTrace]
  refine ⟨40464765229173923246760497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107906040611130461991361325 40464765229173923246760497)
  ·
    refine ⟨30348573921880442435070373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40464765229173923246760497 30348573921880442435070373)
    ·
      refine ⟨5690357610352582956575695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30348573921880442435070373 5690357610352582956575695)
      ·
        refine ⟨8535536415528874434863543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5690357610352582956575695 8535536415528874434863543)
        ·
          refine ⟨12803304623293311652295315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8535536415528874434863543 12803304623293311652295315)
          ·
            refine ⟨19204956934939967478442973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12803304623293311652295315 19204956934939967478442973)
            ·
              refine ⟨7201858850602487804416115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19204956934939967478442973 7201858850602487804416115)
              ·
                refine ⟨10802788275903731706624173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7201858850602487804416115 10802788275903731706624173)
                ·
                  refine ⟨4051045603463899389984065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10802788275903731706624173 4051045603463899389984065)
                  ·
                    refine ⟨3038284202597924542488049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4051045603463899389984065 3038284202597924542488049)
                    ·
                      refine ⟨2278713151948443406866037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3038284202597924542488049 2278713151948443406866037)
                      ·
                        rfl

theorem cell23_4437778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_4437778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437778 prefixEnd_4437778 := by exact prefixLift 4437778
  have htrace : WordTrace (prefixWord ++ tailWord_4437778) baseStart_4437778 baseEnd_4437778 := by
    simpa [prefixWord, tailWord_4437778, baseEnd_4437778] using wordTrace_append hprefix tailTrace_4437778
  have hstable : (prefixWord ++ tailWord_4437778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437778).length < 2 ^ (prefixWord ++ tailWord_4437778).sum := by decide
  have hdescent : baseEnd_4437778 < baseStart_4437778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437787 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 5, 3, 2]
def baseStart_4437787 : Nat := 118140960795 + 4437787 * 2 ^ 59
def prefixEnd_4437787 : Nat := 4983230072969 + 3 ^ 40 * 4437787 * 2
def baseEnd_4437787 : Nat := 2278717773274333871653495

theorem tailTrace_4437787 : CollatzResearch.WordTrace tailWord_4437787 prefixEnd_4437787 2278717773274333871653495 := by
  unfold tailWord_4437787
  simp only [CollatzResearch.WordTrace]
  refine ⟨161859389173663087524119615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107906259449108725016079743 161859389173663087524119615)
  ·
    refine ⟨242789083760494631286179423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161859389173663087524119615 242789083760494631286179423)
    ·
      refine ⟨364183625640741946929269135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242789083760494631286179423 364183625640741946929269135)
      ·
        refine ⟨546275438461112920393903703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 364183625640741946929269135 546275438461112920393903703)
        ·
          refine ⟨819413157691669380590855555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 546275438461112920393903703 819413157691669380590855555)
          ·
            refine ⟨1229119736537504070886283333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 819413157691669380590855555 1229119736537504070886283333)
            ·
              refine ⟨230459950600782013291178125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1229119736537504070886283333 230459950600782013291178125)
              ·
                refine ⟨86422481475293254984191797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 230459950600782013291178125 86422481475293254984191797)
                ·
                  refine ⟨8102107638308742654767981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 86422481475293254984191797 8102107638308742654767981)
                  ·
                    refine ⟨3038290364365778495537993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8102107638308742654767981 3038290364365778495537993)
                    ·
                      refine ⟨2278717773274333871653495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3038290364365778495537993 2278717773274333871653495)
                      ·
                        rfl

theorem cell23_4437787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 3, 2].length) (baseStart_4437787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437787 prefixEnd_4437787 := by exact prefixLift 4437787
  have htrace : WordTrace (prefixWord ++ tailWord_4437787) baseStart_4437787 baseEnd_4437787 := by
    simpa [prefixWord, tailWord_4437787, baseEnd_4437787] using wordTrace_append hprefix tailTrace_4437787
  have hstable : (prefixWord ++ tailWord_4437787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437787).length < 2 ^ (prefixWord ++ tailWord_4437787).sum := by decide
  have hdescent : baseEnd_4437787 < baseStart_4437787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437804 : List Nat := [2, 2, 1, 1, 1, 6, 1, 1, 3, 3, 2]
def baseStart_4437804 : Nat := 118140960795 + 4437804 * 2 ^ 59
def prefixEnd_4437804 : Nat := 4983230072969 + 3 ^ 40 * 4437804 * 2
def baseEnd_4437804 : Nat := 2278726502445460305140917

theorem tailTrace_4437804 : CollatzResearch.WordTrace tailWord_4437804 prefixEnd_4437804 2278726502445460305140917 := by
  unfold tailWord_4437804
  simp only [CollatzResearch.WordTrace]
  refine ⟨80930004607300749713744233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107906672809734332951658977 80930004607300749713744233)
  ·
    refine ⟨60697503455475562285308175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80930004607300749713744233 60697503455475562285308175)
    ·
      refine ⟨91046255183213343427962263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60697503455475562285308175 91046255183213343427962263)
      ·
        refine ⟨136569382774820015141943395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91046255183213343427962263 136569382774820015141943395)
        ·
          refine ⟨204854074162230022712915093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136569382774820015141943395 204854074162230022712915093)
          ·
            refine ⟨9602534726354532314667895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 204854074162230022712915093 9602534726354532314667895)
            ·
              refine ⟨14403802089531798472001843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9602534726354532314667895 14403802089531798472001843)
              ·
                refine ⟨21605703134297697708002765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14403802089531798472001843 21605703134297697708002765)
                ·
                  refine ⟨8102138675361636640501037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21605703134297697708002765 8102138675361636640501037)
                  ·
                    refine ⟨3038302003260613740187889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8102138675361636640501037 3038302003260613740187889)
                    ·
                      refine ⟨2278726502445460305140917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3038302003260613740187889 2278726502445460305140917)
                      ·
                        rfl

theorem cell23_4437804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 3, 2].length) (baseStart_4437804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437804 prefixEnd_4437804 := by exact prefixLift 4437804
  have htrace : WordTrace (prefixWord ++ tailWord_4437804) baseStart_4437804 baseEnd_4437804 := by
    simpa [prefixWord, tailWord_4437804, baseEnd_4437804] using wordTrace_append hprefix tailTrace_4437804
  have hstable : (prefixWord ++ tailWord_4437804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437804).length < 2 ^ (prefixWord ++ tailWord_4437804).sum := by decide
  have hdescent : baseEnd_4437804 < baseStart_4437804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437840 : List Nat := [2, 1, 1, 1, 1, 4, 1, 5, 7]
def baseStart_4437840 : Nat := 118140960795 + 4437840 * 2 ^ 59
def prefixEnd_4437840 : Nat := 4983230072969 + 3 ^ 40 * 4437840 * 2
def baseEnd_4437840 : Nat := 253193887527669129365639

theorem tailTrace_4437840 : CollatzResearch.WordTrace tailWord_4437840 prefixEnd_4437840 253193887527669129365639 := by
  unfold tailWord_4437840
  simp only [CollatzResearch.WordTrace]
  refine ⟨80930661121235538787899487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107907548161647385050532649 80930661121235538787899487)
  ·
    refine ⟨121395991681853308181849231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80930661121235538787899487 121395991681853308181849231)
    ·
      refine ⟨182093987522779962272773847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121395991681853308181849231 182093987522779962272773847)
      ·
        refine ⟨273140981284169943409160771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182093987522779962272773847 273140981284169943409160771)
        ·
          refine ⟨409711471926254915113741157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273140981284169943409160771 409711471926254915113741157)
          ·
            refine ⟨76820900986172796583826467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 409711471926254915113741157 76820900986172796583826467)
            ·
              refine ⟨115231351479259194875739701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76820900986172796583826467 115231351479259194875739701)
              ·
                refine ⟨10802939201180549519600597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 115231351479259194875739701 10802939201180549519600597)
                ·
                  refine ⟨253193887527669129365639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10802939201180549519600597 253193887527669129365639)
                  ·
                    rfl

theorem cell23_4437840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 7].length) (baseStart_4437840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437840 prefixEnd_4437840 := by exact prefixLift 4437840
  have htrace : WordTrace (prefixWord ++ tailWord_4437840) baseStart_4437840 baseEnd_4437840 := by
    simpa [prefixWord, tailWord_4437840, baseEnd_4437840] using wordTrace_append hprefix tailTrace_4437840
  have hstable : (prefixWord ++ tailWord_4437840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437840).length < 2 ^ (prefixWord ++ tailWord_4437840).sum := by decide
  have hdescent : baseEnd_4437840 < baseStart_4437840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437902 : List Nat := [4, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2]
def baseStart_4437902 : Nat := 118140960795 + 4437902 * 2 ^ 59
def prefixEnd_4437902 : Nat := 4983230072969 + 3 ^ 40 * 4437902 * 2
def baseEnd_4437902 : Nat := 2278776823549600921715467

theorem tailTrace_4437902 : CollatzResearch.WordTrace tailWord_4437902 prefixEnd_4437902 2278776823549600921715467 := by
  unfold tailWord_4437902
  simp only [CollatzResearch.WordTrace]
  refine ⟨20232947946030807770569495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107909055712164308109703973 20232947946030807770569495)
  ·
    refine ⟨30349421919046211655854243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20232947946030807770569495 30349421919046211655854243)
    ·
      refine ⟨45524132878569317483781365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30349421919046211655854243 45524132878569317483781365)
      ·
        refine ⟨4267887457365873514104503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45524132878569317483781365 4267887457365873514104503)
        ·
          refine ⟨6401831186048810271156755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4267887457365873514104503 6401831186048810271156755)
          ·
            refine ⟨9602746779073215406735133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6401831186048810271156755 9602746779073215406735133)
            ·
              refine ⟨3601030042152455777525675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9602746779073215406735133 3601030042152455777525675)
              ·
                refine ⟨5401545063228683666288513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3601030042152455777525675 5401545063228683666288513)
                ·
                  refine ⟨4051158797421512749716385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5401545063228683666288513 4051158797421512749716385)
                  ·
                    refine ⟨3038369098066134562287289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4051158797421512749716385 3038369098066134562287289)
                    ·
                      refine ⟨2278776823549600921715467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3038369098066134562287289 2278776823549600921715467)
                      ·
                        rfl

theorem cell23_4437902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_4437902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437902 prefixEnd_4437902 := by exact prefixLift 4437902
  have htrace : WordTrace (prefixWord ++ tailWord_4437902) baseStart_4437902 baseEnd_4437902 := by
    simpa [prefixWord, tailWord_4437902, baseEnd_4437902] using wordTrace_append hprefix tailTrace_4437902
  have hstable : (prefixWord ++ tailWord_4437902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437902).length < 2 ^ (prefixWord ++ tailWord_4437902).sum := by decide
  have hdescent : baseEnd_4437902 < baseStart_4437902 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437944 : List Nat := [2, 1, 2, 1, 2, 3, 3, 2, 2, 2, 3]
def baseStart_4437944 : Nat := 118140960795 + 4437944 * 2 ^ 59
def prefixEnd_4437944 : Nat := 4983230072969 + 3 ^ 40 * 4437944 * 2
def baseEnd_4437944 : Nat := 2278798389737089757390273

theorem tailTrace_4437944 : CollatzResearch.WordTrace tailWord_4437944 prefixEnd_4437944 2278798389737089757390273 := by
  unfold tailWord_4437944
  simp only [CollatzResearch.WordTrace]
  refine ⟨80932557717047151668792443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107910076956062868891723257 80932557717047151668792443)
  ·
    refine ⟨121398836575570727503188665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80932557717047151668792443 121398836575570727503188665)
    ·
      refine ⟨91049127431678045627391499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121398836575570727503188665 91049127431678045627391499)
      ·
        refine ⟨136573691147517068441087249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91049127431678045627391499 136573691147517068441087249)
        ·
          refine ⟨102430268360637801330815437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136573691147517068441087249 102430268360637801330815437)
          ·
            refine ⟨38411350635239175499055789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102430268360637801330815437 38411350635239175499055789)
            ·
              refine ⟨14404256488214690812145921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38411350635239175499055789 14404256488214690812145921)
              ·
                refine ⟨10803192366161018109109441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14404256488214690812145921 10803192366161018109109441)
                ·
                  refine ⟨8102394274620763581832081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10803192366161018109109441 8102394274620763581832081)
                  ·
                    refine ⟨6076795705965572686374061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8102394274620763581832081 6076795705965572686374061)
                    ·
                      refine ⟨2278798389737089757390273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6076795705965572686374061 2278798389737089757390273)
                      ·
                        rfl

theorem cell23_4437944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 2, 2, 3].length) (baseStart_4437944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437944 prefixEnd_4437944 := by exact prefixLift 4437944
  have htrace : WordTrace (prefixWord ++ tailWord_4437944) baseStart_4437944 baseEnd_4437944 := by
    simpa [prefixWord, tailWord_4437944, baseEnd_4437944] using wordTrace_append hprefix tailTrace_4437944
  have hstable : (prefixWord ++ tailWord_4437944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437944).length < 2 ^ (prefixWord ++ tailWord_4437944).sum := by decide
  have hdescent : baseEnd_4437944 < baseStart_4437944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437957 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 2, 5, 3]
def baseStart_4437957 : Nat := 118140960795 + 4437957 * 2 ^ 59
def prefixEnd_4437957 : Nat := 4983230072969 + 3 ^ 40 * 4437957 * 2
def baseEnd_4437957 : Nat := 2278805064985598206527713

theorem tailTrace_4437957 : CollatzResearch.WordTrace tailWord_4437957 prefixEnd_4437957 2278805064985598206527713 := by
  unfold tailWord_4437957
  simp only [CollatzResearch.WordTrace]
  refine ⟨161865589583047206557808125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107910393055364804371872083 161865589583047206557808125)
  ·
    refine ⟨60699596093642702459178047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161865589583047206557808125 60699596093642702459178047)
    ·
      refine ⟨91049394140464053688767071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60699596093642702459178047 91049394140464053688767071)
      ·
        refine ⟨136574091210696080533150607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91049394140464053688767071 136574091210696080533150607)
        ·
          refine ⟨204861136816044120799725911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136574091210696080533150607 204861136816044120799725911)
          ·
            refine ⟨307291705224066181199588867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204861136816044120799725911 307291705224066181199588867)
            ·
              refine ⟨460937557836099271799383301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307291705224066181199588867 460937557836099271799383301)
              ·
                refine ⟨86425792094268613462384369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 460937557836099271799383301 86425792094268613462384369)
                ·
                  refine ⟨64819344070701460096788277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86425792094268613462384369 64819344070701460096788277)
                  ·
                    refine ⟨6076813506628261884073901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 64819344070701460096788277 6076813506628261884073901)
                    ·
                      refine ⟨2278805064985598206527713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6076813506628261884073901 2278805064985598206527713)
                      ·
                        rfl

theorem cell23_4437957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 5, 3].length) (baseStart_4437957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437957 prefixEnd_4437957 := by exact prefixLift 4437957
  have htrace : WordTrace (prefixWord ++ tailWord_4437957) baseStart_4437957 baseEnd_4437957 := by
    simpa [prefixWord, tailWord_4437957, baseEnd_4437957] using wordTrace_append hprefix tailTrace_4437957
  have hstable : (prefixWord ++ tailWord_4437957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437957).length < 2 ^ (prefixWord ++ tailWord_4437957).sum := by decide
  have hdescent : baseEnd_4437957 < baseStart_4437957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437964 : List Nat := [2, 2, 1, 4, 1, 3, 1, 3, 6]
def baseStart_4437964 : Nat := 118140960795 + 4437964 * 2 ^ 59
def prefixEnd_4437964 : Nat := 4983230072969 + 3 ^ 40 * 4437964 * 2
def baseEnd_4437964 : Nat := 253200962150019964348909

theorem tailTrace_4437964 : CollatzResearch.WordTrace tailWord_4437964 prefixEnd_4437964 253200962150019964348909 := by
  unfold tailWord_4437964
  simp only [CollatzResearch.WordTrace]
  refine ⟨80932922447010923376656473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107910563262681231168875297 80932922447010923376656473)
  ·
    refine ⟨60699691835258192532492355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80932922447010923376656473 60699691835258192532492355)
    ·
      refine ⟨91049537752887288798738533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60699691835258192532492355 91049537752887288798738533)
      ·
        refine ⟨17071788328666366649763475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91049537752887288798738533 17071788328666366649763475)
        ·
          refine ⟨25607682492999549974645213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17071788328666366649763475 25607682492999549974645213)
          ·
            refine ⟨9602880934874831240491955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25607682492999549974645213 9602880934874831240491955)
            ·
              refine ⟨14404321402312246860737933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9602880934874831240491955 14404321402312246860737933)
              ·
                refine ⟨5401620525867092572776725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14404321402312246860737933 5401620525867092572776725)
                ·
                  refine ⟨253200962150019964348909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5401620525867092572776725 253200962150019964348909)
                  ·
                    rfl

theorem cell23_4437964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 6].length) (baseStart_4437964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437964 prefixEnd_4437964 := by exact prefixLift 4437964
  have htrace : WordTrace (prefixWord ++ tailWord_4437964) baseStart_4437964 baseEnd_4437964 := by
    simpa [prefixWord, tailWord_4437964, baseEnd_4437964] using wordTrace_append hprefix tailTrace_4437964
  have hstable : (prefixWord ++ tailWord_4437964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437964).length < 2 ^ (prefixWord ++ tailWord_4437964).sum := by decide
  have hdescent : baseEnd_4437964 < baseStart_4437964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4437984 : List Nat := [2, 1, 1, 3, 1, 1, 1, 5, 1, 5, 2]
def baseStart_4437984 : Nat := 118140960795 + 4437984 * 2 ^ 59
def prefixEnd_4437984 : Nat := 4983230072969 + 3 ^ 40 * 4437984 * 2
def baseEnd_4437984 : Nat := 2278818928963269600890089

theorem tailTrace_4437984 : CollatzResearch.WordTrace tailWord_4437984 prefixEnd_4437984 2278818928963269600890089 := by
  unfold tailWord_4437984
  simp only [CollatzResearch.WordTrace]
  refine ⟨80933287176974695084520503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107911049569299593446027337 80933287176974695084520503)
  ·
    refine ⟨121399930765462042626780755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80933287176974695084520503 121399930765462042626780755)
    ·
      refine ⟨182099896148193063940171133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121399930765462042626780755 182099896148193063940171133)
      ·
        refine ⟨68287461055572398977564175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182099896148193063940171133 68287461055572398977564175)
        ·
          refine ⟨102431191583358598466346263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68287461055572398977564175 102431191583358598466346263)
          ·
            refine ⟨153646787375037897699519395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102431191583358598466346263 153646787375037897699519395)
            ·
              refine ⟨230470181062556846549279093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153646787375037897699519395 230470181062556846549279093)
              ·
                refine ⟨21606579474614704363994915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 230470181062556846549279093 21606579474614704363994915)
                ·
                  refine ⟨32409869211922056545992373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21606579474614704363994915 32409869211922056545992373)
                  ·
                    refine ⟨3038425238617692801186785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32409869211922056545992373 3038425238617692801186785)
                    ·
                      refine ⟨2278818928963269600890089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3038425238617692801186785 2278818928963269600890089)
                      ·
                        rfl

theorem cell23_4437984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 1, 5, 2].length) (baseStart_4437984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4437984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4437984 prefixEnd_4437984 := by exact prefixLift 4437984
  have htrace : WordTrace (prefixWord ++ tailWord_4437984) baseStart_4437984 baseEnd_4437984 := by
    simpa [prefixWord, tailWord_4437984, baseEnd_4437984] using wordTrace_append hprefix tailTrace_4437984
  have hstable : (prefixWord ++ tailWord_4437984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4437984).length < 2 ^ (prefixWord ++ tailWord_4437984).sum := by decide
  have hdescent : baseEnd_4437984 < baseStart_4437984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4437984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438024 : List Nat := [2, 1, 3, 2, 1, 2, 4, 1, 1, 6]
def baseStart_4438024 : Nat := 118140960795 + 4438024 * 2 ^ 59
def prefixEnd_4438024 : Nat := 4983230072969 + 3 ^ 40 * 4438024 * 2
def baseEnd_4438024 : Nat := 759613156063149814796635

theorem tailTrace_4438024 : CollatzResearch.WordTrace tailWord_4438024 prefixEnd_4438024 759613156063149814796635 := by
  unfold tailWord_4438024
  simp only [CollatzResearch.WordTrace]
  refine ⟨80934016636902238500248563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107912022182536318000331417 80934016636902238500248563)
  ·
    refine ⟨121401024955353357750372845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80934016636902238500248563 121401024955353357750372845)
    ·
      refine ⟨45525384358257509156389817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121401024955353357750372845 45525384358257509156389817)
      ·
        refine ⟨34144038268693131867292363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45525384358257509156389817 34144038268693131867292363)
        ·
          refine ⟨51216057403039697800938545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34144038268693131867292363 51216057403039697800938545)
          ·
            refine ⟨38412043052279773350703909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51216057403039697800938545 38412043052279773350703909)
            ·
              refine ⟨7202258072302457503256983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38412043052279773350703909 7202258072302457503256983)
              ·
                refine ⟨10803387108453686254885475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7202258072302457503256983 10803387108453686254885475)
                ·
                  refine ⟨16205080662680529382328213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10803387108453686254885475 16205080662680529382328213)
                  ·
                    refine ⟨759613156063149814796635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16205080662680529382328213 759613156063149814796635)
                    ·
                      rfl

theorem cell23_4438024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_4438024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438024 prefixEnd_4438024 := by exact prefixLift 4438024
  have htrace : WordTrace (prefixWord ++ tailWord_4438024) baseStart_4438024 baseEnd_4438024 := by
    simpa [prefixWord, tailWord_4438024, baseEnd_4438024] using wordTrace_append hprefix tailTrace_4438024
  have hstable : (prefixWord ++ tailWord_4438024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438024).length < 2 ^ (prefixWord ++ tailWord_4438024).sum := by decide
  have hdescent : baseEnd_4438024 < baseStart_4438024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438029 : List Nat := [1, 7, 1, 2, 2, 1, 1, 1, 2, 2, 3]
def baseStart_4438029 : Nat := 118140960795 + 4438029 * 2 ^ 59
def prefixEnd_4438029 : Nat := 4983230072969 + 3 ^ 40 * 4438029 * 2
def baseEnd_4438029 : Nat := 2278842035592721924827383

theorem tailTrace_4438029 : CollatzResearch.WordTrace tailWord_4438029 prefixEnd_4438029 2278842035592721924827383 := by
  unfold tailWord_4438029
  simp only [CollatzResearch.WordTrace]
  refine ⟨161868215638786362854429141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107912143759190908569619427 161868215638786362854429141)
  ·
    refine ⟨3793786304034055379400683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 161868215638786362854429141 3793786304034055379400683)
    ·
      refine ⟨5690679456051083069101025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3793786304034055379400683 5690679456051083069101025)
      ·
        refine ⟨4268009592038312301825769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5690679456051083069101025 4268009592038312301825769)
        ·
          refine ⟨3201007194028734226369327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4268009592038312301825769 3201007194028734226369327)
          ·
            refine ⟨4801510791043101339553991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3201007194028734226369327 4801510791043101339553991)
            ·
              refine ⟨7202266186564652009330987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4801510791043101339553991 7202266186564652009330987)
              ·
                refine ⟨10803399279846978013996481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7202266186564652009330987 10803399279846978013996481)
                ·
                  refine ⟨8102549459885233510497361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10803399279846978013996481 8102549459885233510497361)
                  ·
                    refine ⟨6076912094913925132873021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8102549459885233510497361 6076912094913925132873021)
                    ·
                      refine ⟨2278842035592721924827383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6076912094913925132873021 2278842035592721924827383)
                      ·
                        rfl

theorem cell23_4438029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_4438029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438029 prefixEnd_4438029 := by exact prefixLift 4438029
  have htrace : WordTrace (prefixWord ++ tailWord_4438029) baseStart_4438029 baseEnd_4438029 := by
    simpa [prefixWord, tailWord_4438029, baseEnd_4438029] using wordTrace_append hprefix tailTrace_4438029
  have hstable : (prefixWord ++ tailWord_4438029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438029).length < 2 ^ (prefixWord ++ tailWord_4438029).sum := by decide
  have hdescent : baseEnd_4438029 < baseStart_4438029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438051 : List Nat := [1, 1, 1, 4, 3, 1, 3, 3, 1, 2, 3]
def baseStart_4438051 : Nat := 118140960795 + 4438051 * 2 ^ 59
def prefixEnd_4438051 : Nat := 4983230072969 + 3 ^ 40 * 4438051 * 2
def baseEnd_4438051 : Nat := 2278853332167120838752281

theorem tailTrace_4438051 : CollatzResearch.WordTrace tailWord_4438051 prefixEnd_4438051 2278853332167120838752281 := by
  unfold tailWord_4438051
  simp only [CollatzResearch.WordTrace]
  refine ⟨161869018044706660611730007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107912678696471107074486671 161869018044706660611730007)
  ·
    refine ⟨242803527067059990917595011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161869018044706660611730007 242803527067059990917595011)
    ·
      refine ⟨364205290600589986376392517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242803527067059990917595011 364205290600589986376392517)
      ·
        refine ⟨68288491987610622445573597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 364205290600589986376392517 68288491987610622445573597)
        ·
          refine ⟨25608184495353983417090099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68288491987610622445573597 25608184495353983417090099)
          ·
            refine ⟨38412276743030975125635149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25608184495353983417090099 38412276743030975125635149)
            ·
              refine ⟨14404603778636615672113181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38412276743030975125635149 14404603778636615672113181)
              ·
                refine ⟨5401726416988730877042443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14404603778636615672113181 5401726416988730877042443)
                ·
                  refine ⟨8102589625483096315563665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5401726416988730877042443 8102589625483096315563665)
                  ·
                    refine ⟨6076942219112322236672749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8102589625483096315563665 6076942219112322236672749)
                    ·
                      refine ⟨2278853332167120838752281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6076942219112322236672749 2278853332167120838752281)
                      ·
                        rfl

theorem cell23_4438051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 2, 3].length) (baseStart_4438051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438051 prefixEnd_4438051 := by exact prefixLift 4438051
  have htrace : WordTrace (prefixWord ++ tailWord_4438051) baseStart_4438051 baseEnd_4438051 := by
    simpa [prefixWord, tailWord_4438051, baseEnd_4438051] using wordTrace_append hprefix tailTrace_4438051
  have hstable : (prefixWord ++ tailWord_4438051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438051).length < 2 ^ (prefixWord ++ tailWord_4438051).sum := by decide
  have hdescent : baseEnd_4438051 < baseStart_4438051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438058 : List Nat := [3, 1, 4, 1, 2, 1, 3, 2, 2, 4]
def baseStart_4438058 : Nat := 118140960795 + 4438058 * 2 ^ 59
def prefixEnd_4438058 : Nat := 4983230072969 + 3 ^ 40 * 4438058 * 2
def baseEnd_4438058 : Nat := 759618975510567437121583

theorem tailTrace_4438058 : CollatzResearch.WordTrace tailWord_4438058 prefixEnd_4438058 759618975510567437121583 := by
  unfold tailWord_4438058
  simp only [CollatzResearch.WordTrace]
  refine ⟨40467318338920325201808707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107912848903787533871489885 40467318338920325201808707)
  ·
    refine ⟨60700977508380487802713061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40467318338920325201808707 60700977508380487802713061)
    ·
      refine ⟨11381433282821341463008699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60700977508380487802713061 11381433282821341463008699)
      ·
        refine ⟨17072149924232012194513049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11381433282821341463008699 17072149924232012194513049)
        ·
          refine ⟨12804112443174009145884787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17072149924232012194513049 12804112443174009145884787)
          ·
            refine ⟨19206168664761013718827181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12804112443174009145884787 19206168664761013718827181)
            ·
              refine ⟨7202313249285380144560193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19206168664761013718827181 7202313249285380144560193)
              ·
                refine ⟨5401734936964035108420145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7202313249285380144560193 5401734936964035108420145)
                ·
                  refine ⟨4051301202723026331315109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5401734936964035108420145 4051301202723026331315109)
                  ·
                    refine ⟨759618975510567437121583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4051301202723026331315109 759618975510567437121583)
                    ·
                      rfl

theorem cell23_4438058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_4438058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438058 prefixEnd_4438058 := by exact prefixLift 4438058
  have htrace : WordTrace (prefixWord ++ tailWord_4438058) baseStart_4438058 baseEnd_4438058 := by
    simpa [prefixWord, tailWord_4438058, baseEnd_4438058] using wordTrace_append hprefix tailTrace_4438058
  have hstable : (prefixWord ++ tailWord_4438058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438058).length < 2 ^ (prefixWord ++ tailWord_4438058).sum := by decide
  have hdescent : baseEnd_4438058 < baseStart_4438058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438065 : List Nat := [1, 2, 2, 3, 1, 3, 2, 4, 1, 2, 2]
def baseStart_4438065 : Nat := 118140960795 + 4438065 * 2 ^ 59
def prefixEnd_4438065 : Nat := 4983230072969 + 3 ^ 40 * 4438065 * 2
def baseEnd_4438065 : Nat := 2278860520896283783977217

theorem tailTrace_4438065 : CollatzResearch.WordTrace tailWord_4438065 prefixEnd_4438065 2278860520896283783977217 := by
  unfold tailWord_4438065
  simp only [CollatzResearch.WordTrace]
  refine ⟨161869528666655941002739649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107913019111103960668493099 161869528666655941002739649)
  ·
    refine ⟨121402146499991955752054737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161869528666655941002739649 121402146499991955752054737)
    ·
      refine ⟨91051609874993966814041053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121402146499991955752054737 91051609874993966814041053)
      ·
        refine ⟨34144353703122737555265395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91051609874993966814041053 34144353703122737555265395)
        ·
          refine ⟨51216530554684106332898093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34144353703122737555265395 51216530554684106332898093)
          ·
            refine ⟨19206198958006539874836785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51216530554684106332898093 19206198958006539874836785)
            ·
              refine ⟨14404649218504904906127589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19206198958006539874836785 14404649218504904906127589)
              ·
                refine ⟨2700871728469669669898923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14404649218504904906127589 2700871728469669669898923)
                ·
                  refine ⟨4051307592704504504848385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2700871728469669669898923 4051307592704504504848385)
                  ·
                    refine ⟨3038480694528378378636289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4051307592704504504848385 3038480694528378378636289)
                    ·
                      refine ⟨2278860520896283783977217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3038480694528378378636289 2278860520896283783977217)
                      ·
                        rfl

theorem cell23_4438065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 4, 1, 2, 2].length) (baseStart_4438065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438065 prefixEnd_4438065 := by exact prefixLift 4438065
  have htrace : WordTrace (prefixWord ++ tailWord_4438065) baseStart_4438065 baseEnd_4438065 := by
    simpa [prefixWord, tailWord_4438065, baseEnd_4438065] using wordTrace_append hprefix tailTrace_4438065
  have hstable : (prefixWord ++ tailWord_4438065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438065).length < 2 ^ (prefixWord ++ tailWord_4438065).sum := by decide
  have hdescent : baseEnd_4438065 < baseStart_4438065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438067 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 1, 9]
def baseStart_4438067 : Nat := 118140960795 + 4438067 * 2 ^ 59
def prefixEnd_4438067 : Nat := 4983230072969 + 3 ^ 40 * 4438067 * 2
def baseEnd_4438067 : Nat := 759620515952530925384069

theorem tailTrace_4438067 : CollatzResearch.WordTrace tailWord_4438067 prefixEnd_4438067 759620515952530925384069 := by
  unfold tailWord_4438067
  simp only [CollatzResearch.WordTrace]
  refine ⟨161869601612648695344312455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107913067741765796896208303 161869601612648695344312455)
  ·
    refine ⟨242804402418973043016468683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161869601612648695344312455 242804402418973043016468683)
    ·
      refine ⟨364206603628459564524703025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242804402418973043016468683 364206603628459564524703025)
      ·
        refine ⟨273154952721344673393527269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 364206603628459564524703025 273154952721344673393527269)
        ·
          refine ⟨51216553635252126261286363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 273154952721344673393527269 51216553635252126261286363)
          ·
            refine ⟨76824830452878189391929545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51216553635252126261286363 76824830452878189391929545)
            ·
              refine ⟨57618622839658642043947159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76824830452878189391929545 57618622839658642043947159)
              ·
                refine ⟨86427934259487963065920739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57618622839658642043947159 86427934259487963065920739)
                ·
                  refine ⟨129641901389231944598881109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86427934259487963065920739 129641901389231944598881109)
                  ·
                    refine ⟨759620515952530925384069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 129641901389231944598881109 759620515952530925384069)
                    ·
                      rfl

theorem cell23_4438067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 9].length) (baseStart_4438067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438067 prefixEnd_4438067 := by exact prefixLift 4438067
  have htrace : WordTrace (prefixWord ++ tailWord_4438067) baseStart_4438067 baseEnd_4438067 := by
    simpa [prefixWord, tailWord_4438067, baseEnd_4438067] using wordTrace_append hprefix tailTrace_4438067
  have hstable : (prefixWord ++ tailWord_4438067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438067).length < 2 ^ (prefixWord ++ tailWord_4438067).sum := by decide
  have hdescent : baseEnd_4438067 < baseStart_4438067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438068 : List Nat := [2, 5, 1, 2, 2, 1, 1, 2, 1, 1, 5]
def baseStart_4438068 : Nat := 118140960795 + 4438068 * 2 ^ 59
def prefixEnd_4438068 : Nat := 4983230072969 + 3 ^ 40 * 4438068 * 2
def baseEnd_4438068 : Nat := 2278862061338247272239703

theorem tailTrace_4438068 : CollatzResearch.WordTrace tailWord_4438068 prefixEnd_4438068 2278862061338247272239703 := by
  unfold tailWord_4438068
  simp only [CollatzResearch.WordTrace]
  refine ⟨80934819042822536257549429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107913092057096715010065905 80934819042822536257549429)
  ·
    refine ⟨7587639285264612774145259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80934819042822536257549429 7587639285264612774145259)
    ·
      refine ⟨11381458927896919161217889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7587639285264612774145259 11381458927896919161217889)
      ·
        refine ⟨8536094195922689370913417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11381458927896919161217889 8536094195922689370913417)
        ·
          refine ⟨6402070646942017028185063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8536094195922689370913417 6402070646942017028185063)
          ·
            refine ⟨9603105970413025542277595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6402070646942017028185063 9603105970413025542277595)
            ·
              refine ⟨14404658955619538313416393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9603105970413025542277595 14404658955619538313416393)
              ·
                refine ⟨10803494216714653735062295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14404658955619538313416393 10803494216714653735062295)
                ·
                  refine ⟨16205241325071980602593443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10803494216714653735062295 16205241325071980602593443)
                  ·
                    refine ⟨24307861987607970903890165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16205241325071980602593443 24307861987607970903890165)
                    ·
                      refine ⟨2278862061338247272239703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24307861987607970903890165 2278862061338247272239703)
                      ·
                        rfl

theorem cell23_4438068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_4438068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438068 prefixEnd_4438068 := by exact prefixLift 4438068
  have htrace : WordTrace (prefixWord ++ tailWord_4438068) baseStart_4438068 baseEnd_4438068 := by
    simpa [prefixWord, tailWord_4438068, baseEnd_4438068] using wordTrace_append hprefix tailTrace_4438068
  have hstable : (prefixWord ++ tailWord_4438068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438068).length < 2 ^ (prefixWord ++ tailWord_4438068).sum := by decide
  have hdescent : baseEnd_4438068 < baseStart_4438068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438094 : List Nat := [4, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5]
def baseStart_4438094 : Nat := 118140960795 + 4438094 * 2 ^ 59
def prefixEnd_4438094 : Nat := 4983230072969 + 3 ^ 40 * 4438094 * 2
def baseEnd_4438094 : Nat := 2278875411835264170514583

theorem tailTrace_4438094 : CollatzResearch.WordTrace tailWord_4438094 prefixEnd_4438094 2278875411835264170514583 := by
  unfold tailWord_4438094
  simp only [CollatzResearch.WordTrace]
  refine ⟨20233823297943859869443167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107913724255700585970363557 20233823297943859869443167)
  ·
    refine ⟨30350734946915789804164751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20233823297943859869443167 30350734946915789804164751)
    ·
      refine ⟨45526102420373684706247127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30350734946915789804164751 45526102420373684706247127)
      ·
        refine ⟨68289153630560527059370691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45526102420373684706247127 68289153630560527059370691)
        ·
          refine ⟨102433730445840790589056037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68289153630560527059370691 102433730445840790589056037)
          ·
            refine ⟨19206324458595148235448007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102433730445840790589056037 19206324458595148235448007)
            ·
              refine ⟨28809486687892722353172011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19206324458595148235448007 28809486687892722353172011)
              ·
                refine ⟨43214230031839083529758017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28809486687892722353172011 43214230031839083529758017)
                ·
                  refine ⟨32410672523879312647318513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43214230031839083529758017 32410672523879312647318513)
                  ·
                    refine ⟨24308004392909484485488885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32410672523879312647318513 24308004392909484485488885)
                    ·
                      refine ⟨2278875411835264170514583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24308004392909484485488885 2278875411835264170514583)
                      ·
                        rfl

theorem cell23_4438094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_4438094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438094 prefixEnd_4438094 := by exact prefixLift 4438094
  have htrace : WordTrace (prefixWord ++ tailWord_4438094) baseStart_4438094 baseEnd_4438094 := by
    simpa [prefixWord, tailWord_4438094, baseEnd_4438094] using wordTrace_append hprefix tailTrace_4438094
  have hstable : (prefixWord ++ tailWord_4438094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438094).length < 2 ^ (prefixWord ++ tailWord_4438094).sum := by decide
  have hdescent : baseEnd_4438094 < baseStart_4438094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438181 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 1, 7, 2]
def baseStart_4438181 : Nat := 118140960795 + 4438181 * 2 ^ 59
def prefixEnd_4438181 : Nat := 4983230072969 + 3 ^ 40 * 4438181 * 2
def baseEnd_4438181 : Nat := 2278920084652205330126683

theorem tailTrace_4438181 : CollatzResearch.WordTrace tailWord_4438181 prefixEnd_4438181 2278920084652205330126683 := by
  unfold tailWord_4438181
  simp only [CollatzResearch.WordTrace]
  refine ⟨161873759534235692813962397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107915839689490461875974931 161873759534235692813962397)
  ·
    refine ⟨60702659825338384805235899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161873759534235692813962397 60702659825338384805235899)
    ·
      refine ⟨91053989738007577207853849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60702659825338384805235899 91053989738007577207853849)
      ·
        refine ⟨68290492303505682905890387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91053989738007577207853849 68290492303505682905890387)
        ·
          refine ⟨102435738455258524358835581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68290492303505682905890387 102435738455258524358835581)
          ·
            refine ⟨38413401920721946634563343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102435738455258524358835581 38413401920721946634563343)
            ·
              refine ⟨57620102881082919951845015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38413401920721946634563343 57620102881082919951845015)
              ·
                refine ⟨86430154321624379927767523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57620102881082919951845015 86430154321624379927767523)
                ·
                  refine ⟨129645231482436569891651285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86430154321624379927767523 129645231482436569891651285)
                  ·
                    refine ⟨3038560112869607106835577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 129645231482436569891651285 3038560112869607106835577)
                    ·
                      refine ⟨2278920084652205330126683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3038560112869607106835577 2278920084652205330126683)
                      ·
                        rfl

theorem cell23_4438181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 7, 2].length) (baseStart_4438181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438181 prefixEnd_4438181 := by exact prefixLift 4438181
  have htrace : WordTrace (prefixWord ++ tailWord_4438181) baseStart_4438181 baseEnd_4438181 := by
    simpa [prefixWord, tailWord_4438181, baseEnd_4438181] using wordTrace_append hprefix tailTrace_4438181
  have hstable : (prefixWord ++ tailWord_4438181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438181).length < 2 ^ (prefixWord ++ tailWord_4438181).sum := by decide
  have hdescent : baseEnd_4438181 < baseStart_4438181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438208 : List Nat := [2, 1, 1, 2, 5, 3, 1, 1, 2, 5]
def baseStart_4438208 : Nat := 118140960795 + 4438208 * 2 ^ 59
def prefixEnd_4438208 : Nat := 4983230072969 + 3 ^ 40 * 4438208 * 2
def baseEnd_4438208 : Nat := 759644649543292241496353

theorem tailTrace_4438208 : CollatzResearch.WordTrace tailWord_4438208 prefixEnd_4438208 759644649543292241496353 := by
  unfold tailWord_4438208
  simp only [CollatzResearch.WordTrace]
  refine ⟨80937372152568938212597639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107916496203425250950130185 80937372152568938212597639)
  ·
    refine ⟨121406058228853407318896459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80937372152568938212597639 121406058228853407318896459)
    ·
      refine ⟨182109087343280110978344689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121406058228853407318896459 182109087343280110978344689)
      ·
        refine ⟨136581815507460083233758517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182109087343280110978344689 136581815507460083233758517)
        ·
          refine ⟨12804545203824382803164861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 136581815507460083233758517 12804545203824382803164861)
          ·
            refine ⟨4801704451434143551186823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12804545203824382803164861 4801704451434143551186823)
            ·
              refine ⟨7202556677151215326780235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4801704451434143551186823 7202556677151215326780235)
              ·
                refine ⟨10803835015726822990170353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7202556677151215326780235 10803835015726822990170353)
                ·
                  refine ⟨8102876261795117242627765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10803835015726822990170353 8102876261795117242627765)
                  ·
                    refine ⟨759644649543292241496353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8102876261795117242627765 759644649543292241496353)
                    ·
                      rfl

theorem cell23_4438208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 2, 5].length) (baseStart_4438208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438208 prefixEnd_4438208 := by exact prefixLift 4438208
  have htrace : WordTrace (prefixWord ++ tailWord_4438208) baseStart_4438208 baseEnd_4438208 := by
    simpa [prefixWord, tailWord_4438208, baseEnd_4438208] using wordTrace_append hprefix tailTrace_4438208
  have hstable : (prefixWord ++ tailWord_4438208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438208).length < 2 ^ (prefixWord ++ tailWord_4438208).sum := by decide
  have hdescent : baseEnd_4438208 < baseStart_4438208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438224 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 4]
def baseStart_4438224 : Nat := 118140960795 + 4438224 * 2 ^ 59
def prefixEnd_4438224 : Nat := 4983230072969 + 3 ^ 40 * 4438224 * 2
def baseEnd_4438224 : Nat := 2278942164320348661888985

theorem tailTrace_4438224 : CollatzResearch.WordTrace tailWord_4438224 prefixEnd_4438224 2278942164320348661888985 := by
  unfold tailWord_4438224
  simp only [CollatzResearch.WordTrace]
  refine ⟨80937663936539955578888863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107916885248719940771851817 80937663936539955578888863)
  ·
    refine ⟨121406495904809933368333295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80937663936539955578888863 121406495904809933368333295)
    ·
      refine ⟨182109743857214900052499943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121406495904809933368333295 182109743857214900052499943)
      ·
        refine ⟨273164615785822350078749915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182109743857214900052499943 273164615785822350078749915)
        ·
          refine ⟨409746923678733525118124873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273164615785822350078749915 409746923678733525118124873)
          ·
            refine ⟨307310192759050143838593655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 409746923678733525118124873 307310192759050143838593655)
            ·
              refine ⟨460965289138575215757890483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307310192759050143838593655 460965289138575215757890483)
              ·
                refine ⟨691447933707862823636835725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 460965289138575215757890483 691447933707862823636835725)
                ·
                  refine ⟨259292975140448558863813397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 691447933707862823636835725 259292975140448558863813397)
                  ·
                    refine ⟨12154358209708526196741253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 259292975140448558863813397 12154358209708526196741253)
                    ·
                      refine ⟨2278942164320348661888985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12154358209708526196741253 2278942164320348661888985)
                      ·
                        rfl

theorem cell23_4438224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 4].length) (baseStart_4438224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438224 prefixEnd_4438224 := by exact prefixLift 4438224
  have htrace : WordTrace (prefixWord ++ tailWord_4438224) baseStart_4438224 baseEnd_4438224 := by
    simpa [prefixWord, tailWord_4438224, baseEnd_4438224] using wordTrace_append hprefix tailTrace_4438224
  have hstable : (prefixWord ++ tailWord_4438224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438224).length < 2 ^ (prefixWord ++ tailWord_4438224).sum := by decide
  have hdescent : baseEnd_4438224 < baseStart_4438224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438231 : List Nat := [1, 1, 3, 2, 1, 2, 1, 3, 4, 2, 3]
def baseStart_4438231 : Nat := 118140960795 + 4438231 * 2 ^ 59
def prefixEnd_4438231 : Nat := 4983230072969 + 3 ^ 40 * 4438231 * 2
def baseEnd_4438231 : Nat := 2278945758684930134501453

theorem tailTrace_4438231 : CollatzResearch.WordTrace tailWord_4438231 prefixEnd_4438231 2278945758684930134501453 := by
  unfold tailWord_4438231
  simp only [CollatzResearch.WordTrace]
  refine ⟨161875583184054551353282547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107917055456036367568855031 161875583184054551353282547)
  ·
    refine ⟨242813374776081827029923821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161875583184054551353282547 242813374776081827029923821)
    ·
      refine ⟨91055015541030685136221433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 242813374776081827029923821 91055015541030685136221433)
      ·
        refine ⟨68291261655773013852166075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91055015541030685136221433 68291261655773013852166075)
        ·
          refine ⟨102436892483659520778249113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68291261655773013852166075 102436892483659520778249113)
          ·
            refine ⟨76827669362744640583686835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102436892483659520778249113 76827669362744640583686835)
            ·
              refine ⟨115241504044116960875530253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76827669362744640583686835 115241504044116960875530253)
              ·
                refine ⟨43215564016543860328323845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115241504044116960875530253 43215564016543860328323845)
                ·
                  refine ⟨8102918253101973811560721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43215564016543860328323845 8102918253101973811560721)
                  ·
                    refine ⟨6077188689826480358670541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8102918253101973811560721 6077188689826480358670541)
                    ·
                      refine ⟨2278945758684930134501453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6077188689826480358670541 2278945758684930134501453)
                      ·
                        rfl

theorem cell23_4438231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_4438231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438231 prefixEnd_4438231 := by exact prefixLift 4438231
  have htrace : WordTrace (prefixWord ++ tailWord_4438231) baseStart_4438231 baseEnd_4438231 := by
    simpa [prefixWord, tailWord_4438231, baseEnd_4438231] using wordTrace_append hprefix tailTrace_4438231
  have hstable : (prefixWord ++ tailWord_4438231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438231).length < 2 ^ (prefixWord ++ tailWord_4438231).sum := by decide
  have hdescent : baseEnd_4438231 < baseStart_4438231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438264 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 2, 9]
def baseStart_4438264 : Nat := 118140960795 + 4438264 * 2 ^ 59
def prefixEnd_4438264 : Nat := 4983230072969 + 3 ^ 40 * 4438264 * 2
def baseEnd_4438264 : Nat := 759654234515509501796267

theorem tailTrace_4438264 : CollatzResearch.WordTrace tailWord_4438264 prefixEnd_4438264 759654234515509501796267 := by
  unfold tailWord_4438264
  simp only [CollatzResearch.WordTrace]
  refine ⟨80938393396467498994616923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107917857861956665326155897 80938393396467498994616923)
  ·
    refine ⟨121407590094701248491925385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80938393396467498994616923 121407590094701248491925385)
    ·
      refine ⟨91055692571025936368944039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121407590094701248491925385 91055692571025936368944039)
      ·
        refine ⟨136583538856538904553416059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91055692571025936368944039 136583538856538904553416059)
        ·
          refine ⟨204875308284808356830124089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136583538856538904553416059 204875308284808356830124089)
          ·
            refine ⟨153656481213606267622593067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204875308284808356830124089 153656481213606267622593067)
            ·
              refine ⟨230484721820409401433889601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153656481213606267622593067 230484721820409401433889601)
              ·
                refine ⟨172863541365307051075417201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 230484721820409401433889601 172863541365307051075417201)
                ·
                  refine ⟨129647656023980288306562901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 172863541365307051075417201 129647656023980288306562901)
                  ·
                    refine ⟨759654234515509501796267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 129647656023980288306562901 759654234515509501796267)
                    ·
                      rfl

theorem cell23_4438264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 2, 9].length) (baseStart_4438264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438264 prefixEnd_4438264 := by exact prefixLift 4438264
  have htrace : WordTrace (prefixWord ++ tailWord_4438264) baseStart_4438264 baseEnd_4438264 := by
    simpa [prefixWord, tailWord_4438264, baseEnd_4438264] using wordTrace_append hprefix tailTrace_4438264
  have hstable : (prefixWord ++ tailWord_4438264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438264).length < 2 ^ (prefixWord ++ tailWord_4438264).sum := by decide
  have hdescent : baseEnd_4438264 < baseStart_4438264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438295 : List Nat := [1, 1, 3, 4, 1, 2, 3, 1, 3, 1, 3]
def baseStart_4438295 : Nat := 118140960795 + 4438295 * 2 ^ 59
def prefixEnd_4438295 : Nat := 4983230072969 + 3 ^ 40 * 4438295 * 2
def baseEnd_4438295 : Nat := 2278978621446817884101159

theorem tailTrace_4438295 : CollatzResearch.WordTrace tailWord_4438295 prefixEnd_4438295 2278978621446817884101159 := by
  unfold tailWord_4438295
  simp only [CollatzResearch.WordTrace]
  refine ⟨161877917455822690283612339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107918611637215126855741559 161877917455822690283612339)
  ·
    refine ⟨242816876183734035425418509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161877917455822690283612339 242816876183734035425418509)
    ·
      refine ⟨91056328568900263284531941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 242816876183734035425418509 91056328568900263284531941)
      ·
        refine ⟨17073061606668799365849739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91056328568900263284531941 17073061606668799365849739)
        ·
          refine ⟨25609592410003199048774609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17073061606668799365849739 25609592410003199048774609)
          ·
            refine ⟨19207194307502399286580957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25609592410003199048774609 19207194307502399286580957)
            ·
              refine ⟨7202697865313399732467859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19207194307502399286580957 7202697865313399732467859)
              ·
                refine ⟨10804046797970099598701789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7202697865313399732467859 10804046797970099598701789)
                ·
                  refine ⟨4051517549238787349513171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10804046797970099598701789 4051517549238787349513171)
                  ·
                    refine ⟨6077276323858181024269757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4051517549238787349513171 6077276323858181024269757)
                    ·
                      refine ⟨2278978621446817884101159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6077276323858181024269757 2278978621446817884101159)
                      ·
                        rfl

theorem cell23_4438295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_4438295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438295 prefixEnd_4438295 := by exact prefixLift 4438295
  have htrace : WordTrace (prefixWord ++ tailWord_4438295) baseStart_4438295 baseEnd_4438295 := by
    simpa [prefixWord, tailWord_4438295, baseEnd_4438295] using wordTrace_append hprefix tailTrace_4438295
  have hstable : (prefixWord ++ tailWord_4438295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438295).length < 2 ^ (prefixWord ++ tailWord_4438295).sum := by decide
  have hdescent : baseEnd_4438295 < baseStart_4438295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438302 : List Nat := [4, 3, 2, 1, 1, 1, 4, 1, 6]
def baseStart_4438302 : Nat := 118140960795 + 4438302 * 2 ^ 59
def prefixEnd_4438302 : Nat := 4983230072969 + 3 ^ 40 * 4438302 * 2
def baseEnd_4438302 : Nat := 253220246201266595190403

theorem tailTrace_4438302 : CollatzResearch.WordTrace tailWord_4438302 prefixEnd_4438302 253220246201266595190403 := by
  unfold tailWord_4438302
  simp only [CollatzResearch.WordTrace]
  refine ⟨20234771595849666309889645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107918781844531553652744773 20234771595849666309889645)
  ·
    refine ⟨7588039348443624866208617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20234771595849666309889645 7588039348443624866208617)
    ·
      refine ⟨5691029511332718649656463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7588039348443624866208617 5691029511332718649656463)
      ·
        refine ⟨8536544266999077974484695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5691029511332718649656463 8536544266999077974484695)
        ·
          refine ⟨12804816400498616961727043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8536544266999077974484695 12804816400498616961727043)
          ·
            refine ⟨19207224600747925442590565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12804816400498616961727043 19207224600747925442590565)
            ·
              refine ⟨3601354612640236020485731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19207224600747925442590565 3601354612640236020485731)
              ·
                refine ⟨5402031918960354030728597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3601354612640236020485731 5402031918960354030728597)
                ·
                  refine ⟨253220246201266595190403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5402031918960354030728597 253220246201266595190403)
                  ·
                    rfl

theorem cell23_4438302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_4438302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438302 prefixEnd_4438302 := by exact prefixLift 4438302
  have htrace : WordTrace (prefixWord ++ tailWord_4438302) baseStart_4438302 baseEnd_4438302 := by
    simpa [prefixWord, tailWord_4438302, baseEnd_4438302] using wordTrace_append hprefix tailTrace_4438302
  have hstable : (prefixWord ++ tailWord_4438302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438302).length < 2 ^ (prefixWord ++ tailWord_4438302).sum := by decide
  have hdescent : baseEnd_4438302 < baseStart_4438302 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438322 : List Nat := [3, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2]
def baseStart_4438322 : Nat := 118140960795 + 4438322 * 2 ^ 59
def prefixEnd_4438322 : Nat := 4983230072969 + 3 ^ 40 * 4438322 * 2
def baseEnd_4438322 : Nat := 2278992485424489278463535

theorem tailTrace_4438322 : CollatzResearch.WordTrace tailWord_4438322 prefixEnd_4438322 2278992485424489278463535 := by
  unfold tailWord_4438322
  simp only [CollatzResearch.WordTrace]
  refine ⟨40469725556681218473711305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107919268151149915929896813 40469725556681218473711305)
  ·
    refine ⟨30352294167510913855283479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40469725556681218473711305 30352294167510913855283479)
    ·
      refine ⟨45528441251266370782925219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30352294167510913855283479 45528441251266370782925219)
      ·
        refine ⟨68292661876899556174387829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45528441251266370782925219 68292661876899556174387829)
        ·
          refine ⟨6402437050959333391348859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68292661876899556174387829 6402437050959333391348859)
          ·
            refine ⟨9603655576439000087023289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6402437050959333391348859 9603655576439000087023289)
            ·
              refine ⟨7202741682329250065267467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9603655576439000087023289 7202741682329250065267467)
              ·
                refine ⟨10804112523493875097901201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7202741682329250065267467 10804112523493875097901201)
                ·
                  refine ⟨8103084392620406323425901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10804112523493875097901201 8103084392620406323425901)
                  ·
                    refine ⟨3038656647232652371284713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8103084392620406323425901 3038656647232652371284713)
                    ·
                      refine ⟨2278992485424489278463535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3038656647232652371284713 2278992485424489278463535)
                      ·
                        rfl

theorem cell23_4438322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2].length) (baseStart_4438322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438322 prefixEnd_4438322 := by exact prefixLift 4438322
  have htrace : WordTrace (prefixWord ++ tailWord_4438322) baseStart_4438322 baseEnd_4438322 := by
    simpa [prefixWord, tailWord_4438322, baseEnd_4438322] using wordTrace_append hprefix tailTrace_4438322
  have hstable : (prefixWord ++ tailWord_4438322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438322).length < 2 ^ (prefixWord ++ tailWord_4438322).sum := by decide
  have hdescent : baseEnd_4438322 < baseStart_4438322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438335 : List Nat := [1, 1, 2, 2, 4, 1, 5, 1, 1, 1, 4]
def baseStart_4438335 : Nat := 118140960795 + 4438335 * 2 ^ 59
def prefixEnd_4438335 : Nat := 4983230072969 + 3 ^ 40 * 4438335 * 2
def baseEnd_4438335 : Nat := 2278999160672997727600975

theorem tailTrace_4438335 : CollatzResearch.WordTrace tailWord_4438335 prefixEnd_4438335 2278999160672997727600975 := by
  unfold tailWord_4438335
  simp only [CollatzResearch.WordTrace]
  refine ⟨161879376375677777115068459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107919584250451851410045639 161879376375677777115068459)
  ·
    refine ⟨242819064563516665672602689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161879376375677777115068459 242819064563516665672602689)
    ·
      refine ⟨182114298422637499254452017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242819064563516665672602689 182114298422637499254452017)
      ·
        refine ⟨136585723816978124440839013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182114298422637499254452017 136585723816978124440839013)
        ·
          refine ⟨25609823215683398332657315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136585723816978124440839013 25609823215683398332657315)
          ·
            refine ⟨38414734823525097498985973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25609823215683398332657315 38414734823525097498985973)
            ·
              refine ⟨3601381389705477890529935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38414734823525097498985973 3601381389705477890529935)
              ·
                refine ⟨5402072084558216835794903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3601381389705477890529935 5402072084558216835794903)
                ·
                  refine ⟨8103108126837325253692355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5402072084558216835794903 8103108126837325253692355)
                  ·
                    refine ⟨12154662190255987880538533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8103108126837325253692355 12154662190255987880538533)
                    ·
                      refine ⟨2278999160672997727600975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12154662190255987880538533 2278999160672997727600975)
                      ·
                        rfl

theorem cell23_4438335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 1, 1, 4].length) (baseStart_4438335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438335 prefixEnd_4438335 := by exact prefixLift 4438335
  have htrace : WordTrace (prefixWord ++ tailWord_4438335) baseStart_4438335 baseEnd_4438335 := by
    simpa [prefixWord, tailWord_4438335, baseEnd_4438335] using wordTrace_append hprefix tailTrace_4438335
  have hstable : (prefixWord ++ tailWord_4438335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438335).length < 2 ^ (prefixWord ++ tailWord_4438335).sum := by decide
  have hdescent : baseEnd_4438335 < baseStart_4438335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438371 : List Nat := [1, 1, 1, 5, 2, 1, 1, 2, 2, 7]
def baseStart_4438371 : Nat := 118140960795 + 4438371 * 2 ^ 59
def prefixEnd_4438371 : Nat := 4983230072969 + 3 ^ 40 * 4438371 * 2
def baseEnd_4438371 : Nat := 759672548658853195583603

theorem tailTrace_4438371 : CollatzResearch.WordTrace tailWord_4438371 prefixEnd_4438371 759672548658853195583603 := by
  unfold tailWord_4438371
  simp only [CollatzResearch.WordTrace]
  refine ⟨161880689403547355263378967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107920459602364903508919311 161880689403547355263378967)
  ·
    refine ⟨242821034105321032895068451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161880689403547355263378967 242821034105321032895068451)
    ·
      refine ⟨364231551157981549342602677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242821034105321032895068451 364231551157981549342602677)
      ·
        refine ⟨34146707921060770250869001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 364231551157981549342602677 34146707921060770250869001)
        ·
          refine ⟨25610030940795577688151751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34146707921060770250869001 25610030940795577688151751)
          ·
            refine ⟨38415046411193366532227627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25610030940795577688151751 38415046411193366532227627)
            ·
              refine ⟨57622569616790049798341441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38415046411193366532227627 57622569616790049798341441)
              ·
                refine ⟨43216927212592537348756081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57622569616790049798341441 43216927212592537348756081)
                ·
                  refine ⟨32412695409444403011567061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43216927212592537348756081 32412695409444403011567061)
                  ·
                    refine ⟨759672548658853195583603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32412695409444403011567061 759672548658853195583603)
                    ·
                      rfl

theorem cell23_4438371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 7].length) (baseStart_4438371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438371 prefixEnd_4438371 := by exact prefixLift 4438371
  have htrace : WordTrace (prefixWord ++ tailWord_4438371) baseStart_4438371 baseEnd_4438371 := by
    simpa [prefixWord, tailWord_4438371, baseEnd_4438371] using wordTrace_append hprefix tailTrace_4438371
  have hstable : (prefixWord ++ tailWord_4438371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438371).length < 2 ^ (prefixWord ++ tailWord_4438371).sum := by decide
  have hdescent : baseEnd_4438371 < baseStart_4438371 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438389 : List Nat := [1, 3, 4, 1, 2, 3, 2, 1, 1, 2, 3]
def baseStart_4438389 : Nat := 118140960795 + 4438389 * 2 ^ 59
def prefixEnd_4438389 : Nat := 4983230072969 + 3 ^ 40 * 4438389 * 2
def baseEnd_4438389 : Nat := 2279026888628340516325727

theorem tailTrace_4438389 : CollatzResearch.WordTrace tailWord_4438389 prefixEnd_4438389 2279026888628340516325727 := by
  unfold tailWord_4438389
  simp only [CollatzResearch.WordTrace]
  refine ⟨161881345917482144337534221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107920897278321429558356147 161881345917482144337534221)
  ·
    refine ⟨60705504719055804126575333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161881345917482144337534221 60705504719055804126575333)
    ·
      refine ⟨11382282134822963273732875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60705504719055804126575333 11382282134822963273732875)
      ·
        refine ⟨17073423202234444910599313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11382282134822963273732875 17073423202234444910599313)
        ·
          refine ⟨12805067401675833682949485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17073423202234444910599313 12805067401675833682949485)
          ·
            refine ⟨4801900275628437631106057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12805067401675833682949485 4801900275628437631106057)
            ·
              refine ⟨3601425206721328223329543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4801900275628437631106057 3601425206721328223329543)
              ·
                refine ⟨5402137810081992334994315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3601425206721328223329543 5402137810081992334994315)
                ·
                  refine ⟨8103206715122988502491473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5402137810081992334994315 8103206715122988502491473)
                  ·
                    refine ⟨6077405036342241376868605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8103206715122988502491473 6077405036342241376868605)
                    ·
                      refine ⟨2279026888628340516325727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6077405036342241376868605 2279026888628340516325727)
                      ·
                        rfl

theorem cell23_4438389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_4438389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438389 prefixEnd_4438389 := by exact prefixLift 4438389
  have htrace : WordTrace (prefixWord ++ tailWord_4438389) baseStart_4438389 baseEnd_4438389 := by
    simpa [prefixWord, tailWord_4438389, baseEnd_4438389] using wordTrace_append hprefix tailTrace_4438389
  have hstable : (prefixWord ++ tailWord_4438389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438389).length < 2 ^ (prefixWord ++ tailWord_4438389).sum := by decide
  have hdescent : baseEnd_4438389 < baseStart_4438389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438391 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 4]
def baseStart_4438391 : Nat := 118140960795 + 4438391 * 2 ^ 59
def prefixEnd_4438391 : Nat := 4983230072969 + 3 ^ 40 * 4438391 * 2
def baseEnd_4438391 : Nat := 2279027915589649508500717

theorem tailTrace_4438391 : CollatzResearch.WordTrace tailWord_4438391 prefixEnd_4438391 2279027915589649508500717 := by
  unfold tailWord_4438391
  simp only [CollatzResearch.WordTrace]
  refine ⟨161881418863474898679107027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107920945908983265786071351 161881418863474898679107027)
  ·
    refine ⟨242822128295212348018660541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161881418863474898679107027 242822128295212348018660541)
    ·
      refine ⟨91058298110704630506997703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 242822128295212348018660541 91058298110704630506997703)
      ·
        refine ⟨136587447166056945760496555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91058298110704630506997703 136587447166056945760496555)
        ·
          refine ⟨204881170749085418640744833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136587447166056945760496555 204881170749085418640744833)
          ·
            refine ⟨153660878061814063980558625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204881170749085418640744833 153660878061814063980558625)
            ·
              refine ⟨115245658546360547985418969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153660878061814063980558625 115245658546360547985418969)
              ·
                refine ⟨86434243909770410989064227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115245658546360547985418969 86434243909770410989064227)
                ·
                  refine ⟨129651365864655616483596341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86434243909770410989064227 129651365864655616483596341)
                  ·
                    refine ⟨12154815549811464045337157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 129651365864655616483596341 12154815549811464045337157)
                    ·
                      refine ⟨2279027915589649508500717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12154815549811464045337157 2279027915589649508500717)
                      ·
                        rfl

theorem cell23_4438391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_4438391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438391 prefixEnd_4438391 := by exact prefixLift 4438391
  have htrace : WordTrace (prefixWord ++ tailWord_4438391) baseStart_4438391 baseEnd_4438391 := by
    simpa [prefixWord, tailWord_4438391, baseEnd_4438391] using wordTrace_append hprefix tailTrace_4438391
  have hstable : (prefixWord ++ tailWord_4438391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438391).length < 2 ^ (prefixWord ++ tailWord_4438391).sum := by decide
  have hdescent : baseEnd_4438391 < baseStart_4438391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438429 : List Nat := [1, 4, 2, 1, 4, 1, 2, 2, 1, 3, 2]
def baseStart_4438429 : Nat := 118140960795 + 4438429 * 2 ^ 59
def prefixEnd_4438429 : Nat := 4983230072969 + 3 ^ 40 * 4438429 * 2
def baseEnd_4438429 : Nat := 2279047427854520359825543

theorem tailTrace_4438429 : CollatzResearch.WordTrace tailWord_4438429 prefixEnd_4438429 2279047427854520359825543 := by
  unfold tailWord_4438429
  simp only [CollatzResearch.WordTrace]
  refine ⟨161882804837337231168990341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107921869891558154112660227 161882804837337231168990341)
  ·
    refine ⟨30353025907000730844185689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161882804837337231168990341 30353025907000730844185689)
    ·
      refine ⟨22764769430250548133139267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30353025907000730844185689 22764769430250548133139267)
      ·
        refine ⟨34147154145375822199708901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22764769430250548133139267 34147154145375822199708901)
        ·
          refine ⟨6402591402257966662445419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34147154145375822199708901 6402591402257966662445419)
          ·
            refine ⟨9603887103386949993668129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6402591402257966662445419 9603887103386949993668129)
            ·
              refine ⟨7202915327540212495251097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9603887103386949993668129 7202915327540212495251097)
              ·
                refine ⟨5402186495655159371438323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7202915327540212495251097 5402186495655159371438323)
                ·
                  refine ⟨8103279743482739057157485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5402186495655159371438323 8103279743482739057157485)
                  ·
                    refine ⟨3038729903806027146434057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8103279743482739057157485 3038729903806027146434057)
                    ·
                      refine ⟨2279047427854520359825543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3038729903806027146434057 2279047427854520359825543)
                      ·
                        rfl

theorem cell23_4438429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_4438429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438429 prefixEnd_4438429 := by exact prefixLift 4438429
  have htrace : WordTrace (prefixWord ++ tailWord_4438429) baseStart_4438429 baseEnd_4438429 := by
    simpa [prefixWord, tailWord_4438429, baseEnd_4438429] using wordTrace_append hprefix tailTrace_4438429
  have hstable : (prefixWord ++ tailWord_4438429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438429).length < 2 ^ (prefixWord ++ tailWord_4438429).sum := by decide
  have hdescent : baseEnd_4438429 < baseStart_4438429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438451 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 6]
def baseStart_4438451 : Nat := 118140960795 + 4438451 * 2 ^ 59
def prefixEnd_4438451 : Nat := 4983230072969 + 3 ^ 40 * 4438451 * 2
def baseEnd_4438451 : Nat := 2279058724428919273750441

theorem tailTrace_4438451 : CollatzResearch.WordTrace tailWord_4438451 prefixEnd_4438451 2279058724428919273750441 := by
  unfold tailWord_4438451
  simp only [CollatzResearch.WordTrace]
  refine ⟨161883607243257528926291207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107922404828838352617527471 161883607243257528926291207)
  ·
    refine ⟨242825410864886293389436811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161883607243257528926291207 242825410864886293389436811)
    ·
      refine ⟨364238116297329440084155217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242825410864886293389436811 364238116297329440084155217)
      ·
        refine ⟨273178587222997080063116413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 364238116297329440084155217 273178587222997080063116413)
        ·
          refine ⟨102441970208623905023668655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 273178587222997080063116413 102441970208623905023668655)
          ·
            refine ⟨153662955312935857535502983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102441970208623905023668655 153662955312935857535502983)
            ·
              refine ⟨230494432969403786303254475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153662955312935857535502983 230494432969403786303254475)
              ·
                refine ⟨345741649454105679454881713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 230494432969403786303254475 345741649454105679454881713)
                ·
                  refine ⟨259306237090579259591161285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 345741649454105679454881713 259306237090579259591161285)
                  ·
                    refine ⟨48619919454483611173342741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 259306237090579259591161285 48619919454483611173342741)
                    ·
                      refine ⟨2279058724428919273750441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48619919454483611173342741 2279058724428919273750441)
                      ·
                        rfl

theorem cell23_4438451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 6].length) (baseStart_4438451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438451 prefixEnd_4438451 := by exact prefixLift 4438451
  have htrace : WordTrace (prefixWord ++ tailWord_4438451) baseStart_4438451 baseEnd_4438451 := by
    simpa [prefixWord, tailWord_4438451, baseEnd_4438451] using wordTrace_append hprefix tailTrace_4438451
  have hstable : (prefixWord ++ tailWord_4438451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438451).length < 2 ^ (prefixWord ++ tailWord_4438451).sum := by decide
  have hdescent : baseEnd_4438451 < baseStart_4438451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438458 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 4, 3, 3]
def baseStart_4438458 : Nat := 118140960795 + 4438458 * 2 ^ 59
def prefixEnd_4438458 : Nat := 4983230072969 + 3 ^ 40 * 4438458 * 2
def baseEnd_4438458 : Nat := 2279062318793500746362909

theorem tailTrace_4438458 : CollatzResearch.WordTrace tailWord_4438458 prefixEnd_4438458 2279062318793500746362909 := by
  unfold tailWord_4438458
  simp only [CollatzResearch.WordTrace]
  refine ⟨40470965638558042280449007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107922575036154779414530685 40470965638558042280449007)
  ·
    refine ⟨60706448457837063420673511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40470965638558042280449007 60706448457837063420673511)
    ·
      refine ⟨91059672686755595131010267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60706448457837063420673511 91059672686755595131010267)
      ·
        refine ⟨136589509030133392696515401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91059672686755595131010267 136589509030133392696515401)
        ·
          refine ⟨102442131772600044522386551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136589509030133392696515401 102442131772600044522386551)
          ·
            refine ⟨153663197658900066783579827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102442131772600044522386551 153663197658900066783579827)
            ·
              refine ⟨230494796488350100175369741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153663197658900066783579827 230494796488350100175369741)
              ·
                refine ⟨86435548683131287565763653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 230494796488350100175369741 86435548683131287565763653)
                ·
                  refine ⟨16206665378087116418580685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86435548683131287565763653 16206665378087116418580685)
                  ·
                    refine ⟨6077499516782668656967757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16206665378087116418580685 6077499516782668656967757)
                    ·
                      refine ⟨2279062318793500746362909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6077499516782668656967757 2279062318793500746362909)
                      ·
                        rfl

theorem cell23_4438458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 4, 3, 3].length) (baseStart_4438458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438458 prefixEnd_4438458 := by exact prefixLift 4438458
  have htrace : WordTrace (prefixWord ++ tailWord_4438458) baseStart_4438458 baseEnd_4438458 := by
    simpa [prefixWord, tailWord_4438458, baseEnd_4438458] using wordTrace_append hprefix tailTrace_4438458
  have hstable : (prefixWord ++ tailWord_4438458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438458).length < 2 ^ (prefixWord ++ tailWord_4438458).sum := by decide
  have hdescent : baseEnd_4438458 < baseStart_4438458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438478 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 6, 5]
def baseStart_4438478 : Nat := 118140960795 + 4438478 * 2 ^ 59
def prefixEnd_4438478 : Nat := 4983230072969 + 3 ^ 40 * 4438478 * 2
def baseEnd_4438478 : Nat := 759690862802196889370939

theorem tailTrace_4438478 : CollatzResearch.WordTrace tailWord_4438478 prefixEnd_4438478 759690862802196889370939 := by
  unfold tailWord_4438478
  simp only [CollatzResearch.WordTrace]
  refine ⟨20235574001769964067190511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107923061342773141691682725 20235574001769964067190511)
  ·
    refine ⟨30353361002654946100785767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20235574001769964067190511 30353361002654946100785767)
    ·
      refine ⟨45530041503982419151178651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30353361002654946100785767 45530041503982419151178651)
      ·
        refine ⟨68295062255973628726767977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45530041503982419151178651 68295062255973628726767977)
        ·
          refine ⟨51221296691980221545075983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68295062255973628726767977 51221296691980221545075983)
          ·
            refine ⟨76831945037970332317613975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51221296691980221545075983 76831945037970332317613975)
            ·
              refine ⟨115247917556955498476420963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76831945037970332317613975 115247917556955498476420963)
              ·
                refine ⟨172871876335433247714631445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115247917556955498476420963 172871876335433247714631445)
                ·
                  refine ⟨8103369203223433486623349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 172871876335433247714631445 8103369203223433486623349)
                  ·
                    refine ⟨759690862802196889370939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8103369203223433486623349 759690862802196889370939)
                    ·
                      rfl

theorem cell23_4438478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_4438478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438478 prefixEnd_4438478 := by exact prefixLift 4438478
  have htrace : WordTrace (prefixWord ++ tailWord_4438478) baseStart_4438478 baseEnd_4438478 := by
    simpa [prefixWord, tailWord_4438478, baseEnd_4438478] using wordTrace_append hprefix tailTrace_4438478
  have hstable : (prefixWord ++ tailWord_4438478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438478).length < 2 ^ (prefixWord ++ tailWord_4438478).sum := by decide
  have hdescent : baseEnd_4438478 < baseStart_4438478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438495 : List Nat := [1, 1, 2, 3, 3, 3, 2, 1, 2, 5]
def baseStart_4438495 : Nat := 118140960795 + 4438495 * 2 ^ 59
def prefixEnd_4438495 : Nat := 4983230072969 + 3 ^ 40 * 4438495 * 2
def baseEnd_4438495 : Nat := 759693772525905700533413

theorem tailTrace_4438495 : CollatzResearch.WordTrace tailWord_4438495 prefixEnd_4438495 759693772525905700533413 := by
  unfold tailWord_4438495
  simp only [CollatzResearch.WordTrace]
  refine ⟨161885212055098124440892939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107923474703398749627261959 161885212055098124440892939)
  ·
    refine ⟨242827818082647186661339409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161885212055098124440892939 242827818082647186661339409)
    ·
      refine ⟨182120863561985389996004557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242827818082647186661339409 182120863561985389996004557)
      ·
        refine ⟨68295323835744521248501709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182120863561985389996004557 68295323835744521248501709)
        ·
          refine ⟨25610746438404195468188141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68295323835744521248501709 25610746438404195468188141)
          ·
            refine ⟨9604029914401573300570553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25610746438404195468188141 9604029914401573300570553)
            ·
              refine ⟨7203022435801179975427915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9604029914401573300570553 7203022435801179975427915)
              ·
                refine ⟨10804533653701769963141873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7203022435801179975427915 10804533653701769963141873)
                ·
                  refine ⟨8103400240276327472356405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10804533653701769963141873 8103400240276327472356405)
                  ·
                    refine ⟨759693772525905700533413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8103400240276327472356405 759693772525905700533413)
                    ·
                      rfl

theorem cell23_4438495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 5].length) (baseStart_4438495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438495 prefixEnd_4438495 := by exact prefixLift 4438495
  have htrace : WordTrace (prefixWord ++ tailWord_4438495) baseStart_4438495 baseEnd_4438495 := by
    simpa [prefixWord, tailWord_4438495, baseEnd_4438495] using wordTrace_append hprefix tailTrace_4438495
  have hstable : (prefixWord ++ tailWord_4438495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438495).length < 2 ^ (prefixWord ++ tailWord_4438495).sum := by decide
  have hdescent : baseEnd_4438495 < baseStart_4438495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438515 : List Nat := [1, 1, 1, 2, 2, 2, 4, 2, 2, 4, 2]
def baseStart_4438515 : Nat := 118140960795 + 4438515 * 2 ^ 59
def prefixEnd_4438515 : Nat := 4983230072969 + 3 ^ 40 * 4438515 * 2
def baseEnd_4438515 : Nat := 2279091587190807023350147

theorem tailTrace_4438515 : CollatzResearch.WordTrace tailWord_4438515 prefixEnd_4438515 2279091587190807023350147 := by
  unfold tailWord_4438515
  simp only [CollatzResearch.WordTrace]
  refine ⟨161885941515025667856620999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107923961010017111904413999 161885941515025667856620999)
  ·
    refine ⟨242828912272538501784931499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161885941515025667856620999 242828912272538501784931499)
    ·
      refine ⟨364243368408807752677397249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242828912272538501784931499 364243368408807752677397249)
      ·
        refine ⟨273182526306605814508047937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 364243368408807752677397249 273182526306605814508047937)
        ·
          refine ⟨204886894729954360881035953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 273182526306605814508047937 204886894729954360881035953)
          ·
            refine ⟨153665171047465770660776965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204886894729954360881035953 153665171047465770660776965)
            ·
              refine ⟨28812219571399831998895681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 153665171047465770660776965 28812219571399831998895681)
              ·
                refine ⟨21609164678549873999171761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28812219571399831998895681 21609164678549873999171761)
                ·
                  refine ⟨16206873508912405499378821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21609164678549873999171761 16206873508912405499378821)
                  ·
                    refine ⟨3038788782921076031133529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16206873508912405499378821 3038788782921076031133529)
                    ·
                      refine ⟨2279091587190807023350147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3038788782921076031133529 2279091587190807023350147)
                      ·
                        rfl

theorem cell23_4438515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 4, 2].length) (baseStart_4438515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438515 prefixEnd_4438515 := by exact prefixLift 4438515
  have htrace : WordTrace (prefixWord ++ tailWord_4438515) baseStart_4438515 baseEnd_4438515 := by
    simpa [prefixWord, tailWord_4438515, baseEnd_4438515] using wordTrace_append hprefix tailTrace_4438515
  have hstable : (prefixWord ++ tailWord_4438515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438515).length < 2 ^ (prefixWord ++ tailWord_4438515).sum := by decide
  have hdescent : baseEnd_4438515 < baseStart_4438515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438525 : List Nat := [1, 4, 1, 1, 1, 3, 2, 3, 3, 4]
def baseStart_4438525 : Nat := 118140960795 + 4438525 * 2 ^ 59
def prefixEnd_4438525 : Nat := 4983230072969 + 3 ^ 40 * 4438525 * 2
def baseEnd_4438525 : Nat := 759698907332450661408367

theorem tailTrace_4438525 : CollatzResearch.WordTrace tailWord_4438525 prefixEnd_4438525 759698907332450661408367 := by
  unfold tailWord_4438525
  simp only [CollatzResearch.WordTrace]
  refine ⟨161886306244989439564485029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107924204163326293042990019 161886306244989439564485029)
  ·
    refine ⟨30353682420935519918340943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161886306244989439564485029 30353682420935519918340943)
    ·
      refine ⟨45530523631403279877511415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30353682420935519918340943 45530523631403279877511415)
      ·
        refine ⟨68295785447104919816267123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45530523631403279877511415 68295785447104919816267123)
        ·
          refine ⟨102443678170657379724400685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68295785447104919816267123 102443678170657379724400685)
          ·
            refine ⟨38416379313996517396650257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102443678170657379724400685 38416379313996517396650257)
            ·
              refine ⟨28812284485497388047487693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38416379313996517396650257 28812284485497388047487693)
              ·
                refine ⟨10804606682061520517807885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28812284485497388047487693 10804606682061520517807885)
                ·
                  refine ⟨4051727505773070194177957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10804606682061520517807885 4051727505773070194177957)
                  ·
                    refine ⟨759698907332450661408367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4051727505773070194177957 759698907332450661408367)
                    ·
                      rfl

theorem cell23_4438525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_4438525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438525 prefixEnd_4438525 := by exact prefixLift 4438525
  have htrace : WordTrace (prefixWord ++ tailWord_4438525) baseStart_4438525 baseEnd_4438525 := by
    simpa [prefixWord, tailWord_4438525, baseEnd_4438525] using wordTrace_append hprefix tailTrace_4438525
  have hstable : (prefixWord ++ tailWord_4438525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438525).length < 2 ^ (prefixWord ++ tailWord_4438525).sum := by decide
  have hdescent : baseEnd_4438525 < baseStart_4438525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438532 : List Nat := [2, 3, 2, 3, 1, 1, 1, 1, 1, 6, 2]
def baseStart_4438532 : Nat := 118140960795 + 4438532 * 2 ^ 59
def prefixEnd_4438532 : Nat := 4983230072969 + 3 ^ 40 * 4438532 * 2
def baseEnd_4438532 : Nat := 2279100316361933456837569

theorem tailTrace_4438532 : CollatzResearch.WordTrace tailWord_4438532 prefixEnd_4438532 2279100316361933456837569 := by
  unfold tailWord_4438532
  simp only [CollatzResearch.WordTrace]
  refine ⟨80943280777982039879994925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107924374370642719839993233 80943280777982039879994925)
  ·
    refine ⟨30353730291743264954998097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80943280777982039879994925 30353730291743264954998097)
    ·
      refine ⟨22765297718807448716248573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30353730291743264954998097 22765297718807448716248573)
      ·
        refine ⟨8536986644552793268593215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22765297718807448716248573 8536986644552793268593215)
        ·
          refine ⟨12805479966829189902889823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8536986644552793268593215 12805479966829189902889823)
          ·
            refine ⟨19208219950243784854334735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12805479966829189902889823 19208219950243784854334735)
            ·
              refine ⟨28812329925365677281502103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19208219950243784854334735 28812329925365677281502103)
              ·
                refine ⟨43218494888048515922253155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28812329925365677281502103 43218494888048515922253155)
                ·
                  refine ⟨64827742332072773883379733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43218494888048515922253155 64827742332072773883379733)
                  ·
                    refine ⟨3038800421815911275783425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 64827742332072773883379733 3038800421815911275783425)
                    ·
                      refine ⟨2279100316361933456837569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3038800421815911275783425 2279100316361933456837569)
                      ·
                        rfl

theorem cell23_4438532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_4438532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438532 prefixEnd_4438532 := by exact prefixLift 4438532
  have htrace : WordTrace (prefixWord ++ tailWord_4438532) baseStart_4438532 baseEnd_4438532 := by
    simpa [prefixWord, tailWord_4438532, baseEnd_4438532] using wordTrace_append hprefix tailTrace_4438532
  have hstable : (prefixWord ++ tailWord_4438532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438532).length < 2 ^ (prefixWord ++ tailWord_4438532).sum := by decide
  have hdescent : baseEnd_4438532 < baseStart_4438532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438542 : List Nat := [4, 1, 1, 2, 3, 2, 1, 2, 3, 4]
def baseStart_4438542 : Nat := 118140960795 + 4438542 * 2 ^ 59
def prefixEnd_4438542 : Nat := 4983230072969 + 3 ^ 40 * 4438542 * 2
def baseEnd_4438542 : Nat := 759701817056159472570841

theorem tailTrace_4438542 : CollatzResearch.WordTrace tailWord_4438542 prefixEnd_4438542 759701817056159472570841 := by
  unfold tailWord_4438542
  simp only [CollatzResearch.WordTrace]
  refine ⟨20235865785740981433481735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107924617523951900978569253 20235865785740981433481735)
  ·
    refine ⟨30353798678611472150222603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20235865785740981433481735 30353798678611472150222603)
    ·
      refine ⟨45530698017917208225333905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30353798678611472150222603 45530698017917208225333905)
      ·
        refine ⟨34148023513437906169000429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45530698017917208225333905 34148023513437906169000429)
        ·
          refine ⟨12805508817539214813375161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34148023513437906169000429 12805508817539214813375161)
          ·
            refine ⟨9604131613154411110031371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12805508817539214813375161 9604131613154411110031371)
            ·
              refine ⟨14406197419731616665047057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9604131613154411110031371 14406197419731616665047057)
              ·
                refine ⟨10804648064798712498785293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14406197419731616665047057 10804648064798712498785293)
                ·
                  refine ⟨4051743024299517187044485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10804648064798712498785293 4051743024299517187044485)
                  ·
                    refine ⟨759701817056159472570841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4051743024299517187044485 759701817056159472570841)
                    ·
                      rfl

theorem cell23_4438542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_4438542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438542 prefixEnd_4438542 := by exact prefixLift 4438542
  have htrace : WordTrace (prefixWord ++ tailWord_4438542) baseStart_4438542 baseEnd_4438542 := by
    simpa [prefixWord, tailWord_4438542, baseEnd_4438542] using wordTrace_append hprefix tailTrace_4438542
  have hstable : (prefixWord ++ tailWord_4438542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438542).length < 2 ^ (prefixWord ++ tailWord_4438542).sum := by decide
  have hdescent : baseEnd_4438542 < baseStart_4438542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438552 : List Nat := [2, 1, 2, 3, 3, 1, 3, 1, 2, 2, 3]
def baseStart_4438552 : Nat := 118140960795 + 4438552 * 2 ^ 59
def prefixEnd_4438552 : Nat := 4983230072969 + 3 ^ 40 * 4438552 * 2
def baseEnd_4438552 : Nat := 2279110585975023378587477

theorem tailTrace_4438552 : CollatzResearch.WordTrace tailWord_4438552 prefixEnd_4438552 2279110585975023378587477 := by
  unfold tailWord_4438552
  simp only [CollatzResearch.WordTrace]
  refine ⟨80943645507945811587858955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107924860677261082117145273 80943645507945811587858955)
  ·
    refine ⟨121415468261918717381788433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80943645507945811587858955 121415468261918717381788433)
    ·
      refine ⟨91061601196439038036341325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121415468261918717381788433 91061601196439038036341325)
      ·
        refine ⟨34148100448664639263627997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91061601196439038036341325 34148100448664639263627997)
        ·
          refine ⟨12805537668249239723860499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34148100448664639263627997 12805537668249239723860499)
          ·
            refine ⟨19208306502373859585790749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12805537668249239723860499 19208306502373859585790749)
            ·
              refine ⟨7203114938390197344671531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19208306502373859585790749 7203114938390197344671531)
              ·
                refine ⟨10804672407585296017007297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7203114938390197344671531 10804672407585296017007297)
                ·
                  refine ⟨8103504305688972012755473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10804672407585296017007297 8103504305688972012755473)
                  ·
                    refine ⟨6077628229266729009566605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8103504305688972012755473 6077628229266729009566605)
                    ·
                      refine ⟨2279110585975023378587477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6077628229266729009566605 2279110585975023378587477)
                      ·
                        rfl

theorem cell23_4438552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_4438552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438552 prefixEnd_4438552 := by exact prefixLift 4438552
  have htrace : WordTrace (prefixWord ++ tailWord_4438552) baseStart_4438552 baseEnd_4438552 := by
    simpa [prefixWord, tailWord_4438552, baseEnd_4438552] using wordTrace_append hprefix tailTrace_4438552
  have hstable : (prefixWord ++ tailWord_4438552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438552).length < 2 ^ (prefixWord ++ tailWord_4438552).sum := by decide
  have hdescent : baseEnd_4438552 < baseStart_4438552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438602 : List Nat := [3, 1, 2, 1, 1, 5, 2, 2, 1, 5]
def baseStart_4438602 : Nat := 118140960795 + 4438602 * 2 ^ 59
def prefixEnd_4438602 : Nat := 4983230072969 + 3 ^ 40 * 4438602 * 2
def baseEnd_4438602 : Nat := 759712086669249394320749

theorem tailTrace_4438602 : CollatzResearch.WordTrace tailWord_4438602 prefixEnd_4438602 759712086669249394320749 := by
  unfold tailWord_4438602
  simp only [CollatzResearch.WordTrace]
  refine ⟨40472278666427620428759515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107926076443806987810025373 40472278666427620428759515)
  ·
    refine ⟨60708417999641430643139273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40472278666427620428759515 60708417999641430643139273)
    ·
      refine ⟨45531313499731072982354455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60708417999641430643139273 45531313499731072982354455)
      ·
        refine ⟨68296970249596609473531683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45531313499731072982354455 68296970249596609473531683)
        ·
          refine ⟨102445455374394914210297525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68296970249596609473531683 102445455374394914210297525)
          ·
            refine ⟨9604261441349523207215393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102445455374394914210297525 9604261441349523207215393)
            ·
              refine ⟨7203196081012142405411545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9604261441349523207215393 7203196081012142405411545)
              ·
                refine ⟨5402397060759106804058659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7203196081012142405411545 5402397060759106804058659)
                ·
                  refine ⟨8103595591138660206087989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5402397060759106804058659 8103595591138660206087989)
                  ·
                    refine ⟨759712086669249394320749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8103595591138660206087989 759712086669249394320749)
                    ·
                      rfl

theorem cell23_4438602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_4438602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438602 prefixEnd_4438602 := by exact prefixLift 4438602
  have htrace : WordTrace (prefixWord ++ tailWord_4438602) baseStart_4438602 baseEnd_4438602 := by
    simpa [prefixWord, tailWord_4438602, baseEnd_4438602] using wordTrace_append hprefix tailTrace_4438602
  have hstable : (prefixWord ++ tailWord_4438602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438602).length < 2 ^ (prefixWord ++ tailWord_4438602).sum := by decide
  have hdescent : baseEnd_4438602 < baseStart_4438602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438615 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 6, 4]
def baseStart_4438615 : Nat := 118140960795 + 4438615 * 2 ^ 59
def prefixEnd_4438615 : Nat := 4983230072969 + 3 ^ 40 * 4438615 * 2
def baseEnd_4438615 : Nat := 759714311752085544033229

theorem tailTrace_4438615 : CollatzResearch.WordTrace tailWord_4438615 prefixEnd_4438615 759714311752085544033229 := by
  unfold tailWord_4438615
  simp only [CollatzResearch.WordTrace]
  refine ⟨161889588814663384935261299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107926392543108923290174199 161889588814663384935261299)
  ·
    refine ⟨242834383221995077402891949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161889588814663384935261299 242834383221995077402891949)
    ·
      refine ⟨91062893708248154026084481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 242834383221995077402891949 91062893708248154026084481)
      ·
        refine ⟨68297170281186115519563361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91062893708248154026084481 68297170281186115519563361)
        ·
          refine ⟨51222877710889586639672521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68297170281186115519563361 51222877710889586639672521)
          ·
            refine ⟨38417158283167189979754391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51222877710889586639672521 38417158283167189979754391)
            ·
              refine ⟨57625737424750784969631587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38417158283167189979754391 57625737424750784969631587)
              ·
                refine ⟨86438606137126177454447381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57625737424750784969631587 86438606137126177454447381)
                ·
                  refine ⟨4051809662677789568177221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 86438606137126177454447381 4051809662677789568177221)
                  ·
                    refine ⟨759714311752085544033229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4051809662677789568177221 759714311752085544033229)
                    ·
                      rfl

theorem cell23_4438615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 6, 4].length) (baseStart_4438615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438615 prefixEnd_4438615 := by exact prefixLift 4438615
  have htrace : WordTrace (prefixWord ++ tailWord_4438615) baseStart_4438615 baseEnd_4438615 := by
    simpa [prefixWord, tailWord_4438615, baseEnd_4438615] using wordTrace_append hprefix tailTrace_4438615
  have hstable : (prefixWord ++ tailWord_4438615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438615).length < 2 ^ (prefixWord ++ tailWord_4438615).sum := by decide
  have hdescent : baseEnd_4438615 < baseStart_4438615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438625 : List Nat := [1, 2, 3, 1, 1, 4, 1, 3, 1, 1, 5]
def baseStart_4438625 : Nat := 118140960795 + 4438625 * 2 ^ 59
def prefixEnd_4438625 : Nat := 4983230072969 + 3 ^ 40 * 4438625 * 2
def baseEnd_4438625 : Nat := 2279148070062801592974641

theorem tailTrace_4438625 : CollatzResearch.WordTrace tailWord_4438625 prefixEnd_4438625 2279148070062801592974641 := by
  unfold tailWord_4438625
  simp only [CollatzResearch.WordTrace]
  refine ⟨161889953544627156643125329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107926635696418104428750219 161889953544627156643125329)
  ·
    refine ⟨121417465158470367482343997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161889953544627156643125329 121417465158470367482343997)
    ·
      refine ⟨45531549434426387805878999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121417465158470367482343997 45531549434426387805878999)
      ·
        refine ⟨68297324151639581708818499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45531549434426387805878999 68297324151639581708818499)
        ·
          refine ⟨102445986227459372563227749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68297324151639581708818499 102445986227459372563227749)
          ·
            refine ⟨19208622417648632355605203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102445986227459372563227749 19208622417648632355605203)
            ·
              refine ⟨28812933626472948533407805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19208622417648632355605203 28812933626472948533407805)
              ·
                refine ⟨10804850109927355700027927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28812933626472948533407805 10804850109927355700027927)
                ·
                  refine ⟨16207275164891033550041891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10804850109927355700027927 16207275164891033550041891)
                  ·
                    refine ⟨24310912747336550325062837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16207275164891033550041891 24310912747336550325062837)
                    ·
                      refine ⟨2279148070062801592974641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24310912747336550325062837 2279148070062801592974641)
                      ·
                        rfl

theorem cell23_4438625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_4438625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438625 prefixEnd_4438625 := by exact prefixLift 4438625
  have htrace : WordTrace (prefixWord ++ tailWord_4438625) baseStart_4438625 baseEnd_4438625 := by
    simpa [prefixWord, tailWord_4438625, baseEnd_4438625] using wordTrace_append hprefix tailTrace_4438625
  have hstable : (prefixWord ++ tailWord_4438625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438625).length < 2 ^ (prefixWord ++ tailWord_4438625).sum := by decide
  have hdescent : baseEnd_4438625 < baseStart_4438625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438639 : List Nat := [1, 1, 2, 1, 3, 2, 5, 1, 3, 2, 2]
def baseStart_4438639 : Nat := 118140960795 + 4438639 * 2 ^ 59
def prefixEnd_4438639 : Nat := 4983230072969 + 3 ^ 40 * 4438639 * 2
def baseEnd_4438639 : Nat := 2279155258791964538199577

theorem tailTrace_4438639 : CollatzResearch.WordTrace tailWord_4438639 prefixEnd_4438639 2279155258791964538199577 := by
  unfold tailWord_4438639
  simp only [CollatzResearch.WordTrace]
  refine ⟨161890464166576437034134971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107926976111050958022756647 161890464166576437034134971)
  ·
    refine ⟨242835696249864655551202457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161890464166576437034134971 242835696249864655551202457)
    ·
      refine ⟨182126772187398491663401843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242835696249864655551202457 182126772187398491663401843)
      ·
        refine ⟨273190158281097737495102765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182126772187398491663401843 273190158281097737495102765)
        ·
          refine ⟨102446309355411651560663537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 273190158281097737495102765 102446309355411651560663537)
          ·
            refine ⟨76834732016558738670497653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102446309355411651560663537 76834732016558738670497653)
            ·
              refine ⟨7203256126552381750359155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76834732016558738670497653 7203256126552381750359155)
              ·
                refine ⟨10804884189828572625538733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7203256126552381750359155 10804884189828572625538733)
                ·
                  refine ⟨4051831571185714734577025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10804884189828572625538733 4051831571185714734577025)
                  ·
                    refine ⟨3038873678389286050932769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4051831571185714734577025 3038873678389286050932769)
                    ·
                      refine ⟨2279155258791964538199577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3038873678389286050932769 2279155258791964538199577)
                      ·
                        rfl

theorem cell23_4438639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 3, 2, 2].length) (baseStart_4438639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438639 prefixEnd_4438639 := by exact prefixLift 4438639
  have htrace : WordTrace (prefixWord ++ tailWord_4438639) baseStart_4438639 baseEnd_4438639 := by
    simpa [prefixWord, tailWord_4438639, baseEnd_4438639] using wordTrace_append hprefix tailTrace_4438639
  have hstable : (prefixWord ++ tailWord_4438639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438639).length < 2 ^ (prefixWord ++ tailWord_4438639).sum := by decide
  have hdescent : baseEnd_4438639 < baseStart_4438639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438649 : List Nat := [1, 2, 1, 3, 3, 2, 4, 1, 2, 4]
def baseStart_4438649 : Nat := 118140960795 + 4438649 * 2 ^ 59
def prefixEnd_4438649 : Nat := 4983230072969 + 3 ^ 40 * 4438649 * 2
def baseEnd_4438649 : Nat := 759720131199503166358177

theorem tailTrace_4438649 : CollatzResearch.WordTrace tailWord_4438649 prefixEnd_4438649 759720131199503166358177 := by
  unfold tailWord_4438649
  simp only [CollatzResearch.WordTrace]
  refine ⟨161890828896540208741999001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107927219264360139161332667 161890828896540208741999001)
  ·
    refine ⟨121418121672405156556499251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161890828896540208741999001 121418121672405156556499251)
    ·
      refine ⟨182127182508607734834748877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121418121672405156556499251 182127182508607734834748877)
      ·
        refine ⟨68297693440727900563030829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182127182508607734834748877 68297693440727900563030829)
        ·
          refine ⟨25611635040272962711136561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68297693440727900563030829 25611635040272962711136561)
          ·
            refine ⟨19208726280204722033352421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25611635040272962711136561 19208726280204722033352421)
            ·
              refine ⟨3601636177538385381253579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19208726280204722033352421 3601636177538385381253579)
              ·
                refine ⟨5402454266307578071880369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3601636177538385381253579 5402454266307578071880369)
                ·
                  refine ⟨4051840699730683553910277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5402454266307578071880369 4051840699730683553910277)
                  ·
                    refine ⟨759720131199503166358177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4051840699730683553910277 759720131199503166358177)
                    ·
                      rfl

theorem cell23_4438649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 2, 4].length) (baseStart_4438649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438649 prefixEnd_4438649 := by exact prefixLift 4438649
  have htrace : WordTrace (prefixWord ++ tailWord_4438649) baseStart_4438649 baseEnd_4438649 := by
    simpa [prefixWord, tailWord_4438649, baseEnd_4438649] using wordTrace_append hprefix tailTrace_4438649
  have hstable : (prefixWord ++ tailWord_4438649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438649).length < 2 ^ (prefixWord ++ tailWord_4438649).sum := by decide
  have hdescent : baseEnd_4438649 < baseStart_4438649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438685 : List Nat := [1, 4, 2, 1, 1, 1, 2, 2, 2, 2, 5]
def baseStart_4438685 : Nat := 118140960795 + 4438685 * 2 ^ 59
def prefixEnd_4438685 : Nat := 4983230072969 + 3 ^ 40 * 4438685 * 2
def baseEnd_4438685 : Nat := 2279178878902071358224365

theorem tailTrace_4438685 : CollatzResearch.WordTrace tailWord_4438685 prefixEnd_4438685 2279178878902071358224365 := by
  unfold tailWord_4438685
  simp only [CollatzResearch.WordTrace]
  refine ⟨161892141924409786890309509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107928094616273191260206339 161892141924409786890309509)
  ·
    refine ⟨30354776610826835041933033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161892141924409786890309509 30354776610826835041933033)
    ·
      refine ⟨22766082458120126281449775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30354776610826835041933033 22766082458120126281449775)
      ·
        refine ⟨34149123687180189422174663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22766082458120126281449775 34149123687180189422174663)
        ·
          refine ⟨51223685530770284133261995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34149123687180189422174663 51223685530770284133261995)
          ·
            refine ⟨76835528296155426199892993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51223685530770284133261995 76835528296155426199892993)
            ·
              refine ⟨57626646222116569649919745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76835528296155426199892993 57626646222116569649919745)
              ·
                refine ⟨43219984666587427237439809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57626646222116569649919745 43219984666587427237439809)
                ·
                  refine ⟨32414988499940570428079857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43219984666587427237439809 32414988499940570428079857)
                  ·
                    refine ⟨24311241374955427821059893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32414988499940570428079857 24311241374955427821059893)
                    ·
                      refine ⟨2279178878902071358224365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24311241374955427821059893 2279178878902071358224365)
                      ·
                        rfl

theorem cell23_4438685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_4438685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438685 prefixEnd_4438685 := by exact prefixLift 4438685
  have htrace : WordTrace (prefixWord ++ tailWord_4438685) baseStart_4438685 baseEnd_4438685 := by
    simpa [prefixWord, tailWord_4438685, baseEnd_4438685] using wordTrace_append hprefix tailTrace_4438685
  have hstable : (prefixWord ++ tailWord_4438685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438685).length < 2 ^ (prefixWord ++ tailWord_4438685).sum := by decide
  have hdescent : baseEnd_4438685 < baseStart_4438685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438725 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 6, 2, 4]
def baseStart_4438725 : Nat := 118140960795 + 4438725 * 2 ^ 59
def prefixEnd_4438725 : Nat := 4983230072969 + 3 ^ 40 * 4438725 * 2
def baseEnd_4438725 : Nat := 2279199418128251201724181

theorem tailTrace_4438725 : CollatzResearch.WordTrace tailWord_4438725 prefixEnd_4438725 2279199418128251201724181 := by
  unfold tailWord_4438725
  simp only [CollatzResearch.WordTrace]
  refine ⟨161893600844264873721765629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107929067229509915814510419 161893600844264873721765629)
  ·
    refine ⟨60710100316599327645662111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161893600844264873721765629 60710100316599327645662111)
    ·
      refine ⟨91065150474898991468493167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60710100316599327645662111 91065150474898991468493167)
      ·
        refine ⟨136597725712348487202739751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91065150474898991468493167 136597725712348487202739751)
        ·
          refine ⟨204896588568522730804109627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136597725712348487202739751 204896588568522730804109627)
          ·
            refine ⟨307344882852784096206164441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204896588568522730804109627 307344882852784096206164441)
            ·
              refine ⟨230508662139588072154623331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 307344882852784096206164441 230508662139588072154623331)
              ·
                refine ⟨345762993209382108231934997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 230508662139588072154623331 345762993209382108231934997)
                ·
                  refine ⟨16207640306689786323371953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 345762993209382108231934997 16207640306689786323371953)
                  ·
                    refine ⟨12155730230017339742528965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16207640306689786323371953 12155730230017339742528965)
                    ·
                      refine ⟨2279199418128251201724181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12155730230017339742528965 2279199418128251201724181)
                      ·
                        rfl

theorem cell23_4438725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_4438725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438725 prefixEnd_4438725 := by exact prefixLift 4438725
  have htrace : WordTrace (prefixWord ++ tailWord_4438725) baseStart_4438725 baseEnd_4438725 := by
    simpa [prefixWord, tailWord_4438725, baseEnd_4438725] using wordTrace_append hprefix tailTrace_4438725
  have hstable : (prefixWord ++ tailWord_4438725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438725).length < 2 ^ (prefixWord ++ tailWord_4438725).sum := by decide
  have hdescent : baseEnd_4438725 < baseStart_4438725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438740 : List Nat := [2, 4, 1, 3, 3, 1, 1, 2, 2, 1, 3]
def baseStart_4438740 : Nat := 118140960795 + 4438740 * 2 ^ 59
def prefixEnd_4438740 : Nat := 4983230072969 + 3 ^ 40 * 4438740 * 2
def baseEnd_4438740 : Nat := 2279207120338068643036613

theorem tailTrace_4438740 : CollatzResearch.WordTrace tailWord_4438740 prefixEnd_4438740 2279207120338068643036613 := by
  unfold tailWord_4438740
  simp only [CollatzResearch.WordTrace]
  refine ⟨80947073969605265641780837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107929431959473687522374449 80947073969605265641780837)
  ·
    refine ⟨15177576369300987307833907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80947073969605265641780837 15177576369300987307833907)
    ·
      refine ⟨22766364553951480961750861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15177576369300987307833907 22766364553951480961750861)
      ·
        refine ⟨8537386707731805360656573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22766364553951480961750861 8537386707731805360656573)
        ·
          refine ⟨3201520015399427010246215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8537386707731805360656573 3201520015399427010246215)
          ·
            refine ⟨4802280023099140515369323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3201520015399427010246215 4802280023099140515369323)
            ·
              refine ⟨7203420034648710773053985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4802280023099140515369323 7203420034648710773053985)
              ·
                refine ⟨5402565025986533079790489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7203420034648710773053985 5402565025986533079790489)
                ·
                  refine ⟨4051923769489899809842867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5402565025986533079790489 4051923769489899809842867)
                  ·
                    refine ⟨6077885654234849714764301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4051923769489899809842867 6077885654234849714764301)
                    ·
                      refine ⟨2279207120338068643036613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6077885654234849714764301 2279207120338068643036613)
                      ·
                        rfl

theorem cell23_4438740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_4438740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438740 prefixEnd_4438740 := by exact prefixLift 4438740
  have htrace : WordTrace (prefixWord ++ tailWord_4438740) baseStart_4438740 baseEnd_4438740 := by
    simpa [prefixWord, tailWord_4438740, baseEnd_4438740] using wordTrace_append hprefix tailTrace_4438740
  have hstable : (prefixWord ++ tailWord_4438740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438740).length < 2 ^ (prefixWord ++ tailWord_4438740).sum := by decide
  have hdescent : baseEnd_4438740 < baseStart_4438740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438775 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 5]
def baseStart_4438775 : Nat := 118140960795 + 4438775 * 2 ^ 59
def prefixEnd_4438775 : Nat := 4983230072969 + 3 ^ 40 * 4438775 * 2
def baseEnd_4438775 : Nat := 2279225092160976006098951

theorem tailTrace_4438775 : CollatzResearch.WordTrace tailWord_4438775 prefixEnd_4438775 2279225092160976006098951 := by
  unfold tailWord_4438775
  simp only [CollatzResearch.WordTrace]
  refine ⟨161895424494083732261085779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107930282996055821507390519 161895424494083732261085779)
  ·
    refine ⟨242843136741125598391628669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161895424494083732261085779 242843136741125598391628669)
    ·
      refine ⟨91066176277922099396860751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 242843136741125598391628669 91066176277922099396860751)
      ·
        refine ⟨136599264416883149095291127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91066176277922099396860751 136599264416883149095291127)
        ·
          refine ⟨204898896625324723642936691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136599264416883149095291127 204898896625324723642936691)
          ·
            refine ⟨307348344937987085464405037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204898896625324723642936691 307348344937987085464405037)
            ·
              refine ⟨115255629351745157049151889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 307348344937987085464405037 115255629351745157049151889)
              ·
                refine ⟨86441722013808867786863917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115255629351745157049151889 86441722013808867786863917)
                ·
                  refine ⟨32415645755178325420073969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86441722013808867786863917 32415645755178325420073969)
                  ·
                    refine ⟨24311734316383744065055477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32415645755178325420073969 24311734316383744065055477)
                    ·
                      refine ⟨2279225092160976006098951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24311734316383744065055477 2279225092160976006098951)
                      ·
                        rfl

theorem cell23_4438775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_4438775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438775 prefixEnd_4438775 := by exact prefixLift 4438775
  have htrace : WordTrace (prefixWord ++ tailWord_4438775) baseStart_4438775 baseEnd_4438775 := by
    simpa [prefixWord, tailWord_4438775, baseEnd_4438775] using wordTrace_append hprefix tailTrace_4438775
  have hstable : (prefixWord ++ tailWord_4438775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438775).length < 2 ^ (prefixWord ++ tailWord_4438775).sum := by decide
  have hdescent : baseEnd_4438775 < baseStart_4438775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438786 : List Nat := [3, 4, 1, 1, 1, 2, 3, 3, 5]
def baseStart_4438786 : Nat := 118140960795 + 4438786 * 2 ^ 59
def prefixEnd_4438786 : Nat := 4983230072969 + 3 ^ 40 * 4438786 * 2
def baseEnd_4438786 : Nat := 253247860049797273673489

theorem tailTrace_4438786 : CollatzResearch.WordTrace tailWord_4438786 prefixEnd_4438786 253247860049797273673489 := by
  unfold tailWord_4438786
  simp only [CollatzResearch.WordTrace]
  refine ⟨40473956424260970284934053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107930550464695920759824141 40473956424260970284934053)
  ·
    refine ⟨7588866829548931928425135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40473956424260970284934053 7588866829548931928425135)
    ·
      refine ⟨11383300244323397892637703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7588866829548931928425135 11383300244323397892637703)
      ·
        refine ⟨17074950366485096838956555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11383300244323397892637703 17074950366485096838956555)
        ·
          refine ⟨25612425549727645258434833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17074950366485096838956555 25612425549727645258434833)
          ·
            refine ⟨19209319162295733943826125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25612425549727645258434833 19209319162295733943826125)
            ·
              refine ⟨7203494685860900228934797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19209319162295733943826125 7203494685860900228934797)
              ·
                refine ⟨2701310507197837585850549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7203494685860900228934797 2701310507197837585850549)
                ·
                  refine ⟨253247860049797273673489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2701310507197837585850549 253247860049797273673489)
                  ·
                    rfl

theorem cell23_4438786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_4438786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438786 prefixEnd_4438786 := by exact prefixLift 4438786
  have htrace : WordTrace (prefixWord ++ tailWord_4438786) baseStart_4438786 baseEnd_4438786 := by
    simpa [prefixWord, tailWord_4438786, baseEnd_4438786] using wordTrace_append hprefix tailTrace_4438786
  have hstable : (prefixWord ++ tailWord_4438786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438786).length < 2 ^ (prefixWord ++ tailWord_4438786).sum := by decide
  have hdescent : baseEnd_4438786 < baseStart_4438786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438839 : List Nat := [1, 1, 3, 1, 2, 1, 6, 1, 2, 2, 3]
def baseStart_4438839 : Nat := 118140960795 + 4438839 * 2 ^ 59
def prefixEnd_4438839 : Nat := 4983230072969 + 3 ^ 40 * 4438839 * 2
def baseEnd_4438839 : Nat := 2279257954922863755698657

theorem tailTrace_4438839 : CollatzResearch.WordTrace tailWord_4438839 prefixEnd_4438839 2279257954922863755698657 := by
  unfold tailWord_4438839
  simp only [CollatzResearch.WordTrace]
  refine ⟨161897758765851871191415571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107931839177234580794277047 161897758765851871191415571)
  ·
    refine ⟨242846638148777806787123357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161897758765851871191415571 242846638148777806787123357)
    ·
      refine ⟨91067489305791677545171259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 242846638148777806787123357 91067489305791677545171259)
      ·
        refine ⟨136601233958687516317756889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91067489305791677545171259 136601233958687516317756889)
        ·
          refine ⟨102450925469015637238317667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136601233958687516317756889 102450925469015637238317667)
          ·
            refine ⟨153676388203523455857476501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102450925469015637238317667 153676388203523455857476501)
            ·
              refine ⟨7203580697040161993319211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 153676388203523455857476501 7203580697040161993319211)
              ·
                refine ⟨10805371045560242989978817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7203580697040161993319211 10805371045560242989978817)
                ·
                  refine ⟨8104028284170182242484113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10805371045560242989978817 8104028284170182242484113)
                  ·
                    refine ⟨6078021213127636681863085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8104028284170182242484113 6078021213127636681863085)
                    ·
                      refine ⟨2279257954922863755698657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6078021213127636681863085 2279257954922863755698657)
                      ·
                        rfl

theorem cell23_4438839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 2, 3].length) (baseStart_4438839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438839 prefixEnd_4438839 := by exact prefixLift 4438839
  have htrace : WordTrace (prefixWord ++ tailWord_4438839) baseStart_4438839 baseEnd_4438839 := by
    simpa [prefixWord, tailWord_4438839, baseEnd_4438839] using wordTrace_append hprefix tailTrace_4438839
  have hstable : (prefixWord ++ tailWord_4438839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438839).length < 2 ^ (prefixWord ++ tailWord_4438839).sum := by decide
  have hdescent : baseEnd_4438839 < baseStart_4438839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438879 : List Nat := [1, 1, 2, 3, 1, 3, 2, 2, 1, 5, 2]
def baseStart_4438879 : Nat := 118140960795 + 4438879 * 2 ^ 59
def prefixEnd_4438879 : Nat := 4983230072969 + 3 ^ 40 * 4438879 * 2
def baseEnd_4438879 : Nat := 2279278494149043599198473

theorem tailTrace_4438879 : CollatzResearch.WordTrace tailWord_4438879 prefixEnd_4438879 2279278494149043599198473 := by
  unfold tailWord_4438879
  simp only [CollatzResearch.WordTrace]
  refine ⟨161899217685706958022871691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107932811790471305348581127 161899217685706958022871691)
  ·
    refine ⟨242848826528560437034307537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161899217685706958022871691 242848826528560437034307537)
    ·
      refine ⟨182136619896420327775730653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242848826528560437034307537 182136619896420327775730653)
      ·
        refine ⟨68301232461157622915898995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182136619896420327775730653 68301232461157622915898995)
        ·
          refine ⟨102451848691736434373848493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68301232461157622915898995 102451848691736434373848493)
          ·
            refine ⟨38419443259401162890193185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102451848691736434373848493 38419443259401162890193185)
            ·
              refine ⟨28814582444550872167644889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38419443259401162890193185 28814582444550872167644889)
              ·
                refine ⟨21610936833413154125733667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28814582444550872167644889 21610936833413154125733667)
                ·
                  refine ⟨32416405250119731188600501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21610936833413154125733667 32416405250119731188600501)
                  ·
                    refine ⟨3039037992198724798931297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32416405250119731188600501 3039037992198724798931297)
                    ·
                      refine ⟨2279278494149043599198473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3039037992198724798931297 2279278494149043599198473)
                      ·
                        rfl

theorem cell23_4438879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 5, 2].length) (baseStart_4438879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438879 prefixEnd_4438879 := by exact prefixLift 4438879
  have htrace : WordTrace (prefixWord ++ tailWord_4438879) baseStart_4438879 baseEnd_4438879 := by
    simpa [prefixWord, tailWord_4438879, baseEnd_4438879] using wordTrace_append hprefix tailTrace_4438879
  have hstable : (prefixWord ++ tailWord_4438879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438879).length < 2 ^ (prefixWord ++ tailWord_4438879).sum := by decide
  have hdescent : baseEnd_4438879 < baseStart_4438879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438896 : List Nat := [2, 1, 1, 1, 4, 1, 5, 1, 2, 3, 2]
def baseStart_4438896 : Nat := 118140960795 + 4438896 * 2 ^ 59
def prefixEnd_4438896 : Nat := 4983230072969 + 3 ^ 40 * 4438896 * 2
def baseEnd_4438896 : Nat := 2279287223320170032685895

theorem tailTrace_4438896 : CollatzResearch.WordTrace tailWord_4438896 prefixEnd_4438896 2279287223320170032685895 := by
  unfold tailWord_4438896
  simp only [CollatzResearch.WordTrace]
  refine ⟨80949918863322684963120271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107933225151096913284160361 80949918863322684963120271)
  ·
    refine ⟨121424878294984027444680407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80949918863322684963120271 121424878294984027444680407)
    ·
      refine ⟨182137317442476041167020611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121424878294984027444680407 182137317442476041167020611)
      ·
        refine ⟨273205976163714061750530917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182137317442476041167020611 273205976163714061750530917)
        ·
          refine ⟨51226120530696386578224547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 273205976163714061750530917 51226120530696386578224547)
          ·
            refine ⟨76839180796044579867336821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51226120530696386578224547 76839180796044579867336821)
            ·
              refine ⟨7203673199629179362562827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76839180796044579867336821 7203673199629179362562827)
              ·
                refine ⟨10805509799443769043844241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7203673199629179362562827 10805509799443769043844241)
                ·
                  refine ⟨8104132349582826782883181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10805509799443769043844241 8104132349582826782883181)
                  ·
                    refine ⟨3039049631093560043581193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8104132349582826782883181 3039049631093560043581193)
                    ·
                      refine ⟨2279287223320170032685895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3039049631093560043581193 2279287223320170032685895)
                      ·
                        rfl

theorem cell23_4438896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 2, 3, 2].length) (baseStart_4438896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438896 prefixEnd_4438896 := by exact prefixLift 4438896
  have htrace : WordTrace (prefixWord ++ tailWord_4438896) baseStart_4438896 baseEnd_4438896 := by
    simpa [prefixWord, tailWord_4438896, baseEnd_4438896] using wordTrace_append hprefix tailTrace_4438896
  have hstable : (prefixWord ++ tailWord_4438896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438896).length < 2 ^ (prefixWord ++ tailWord_4438896).sum := by decide
  have hdescent : baseEnd_4438896 < baseStart_4438896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438910 : List Nat := [4, 2, 3, 1, 3, 1, 1, 2, 6]
def baseStart_4438910 : Nat := 118140960795 + 4438910 * 2 ^ 59
def prefixEnd_4438910 : Nat := 4983230072969 + 3 ^ 40 * 4438910 * 2
def baseEnd_4438910 : Nat := 253254934672148108656759

theorem tailTrace_4438910 : CollatzResearch.WordTrace tailWord_4438910 prefixEnd_4438910 253254934672148108656759 := by
  unfold tailWord_4438910
  simp only [CollatzResearch.WordTrace]
  refine ⟨20237543543574331289656273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107933565565729766878166789 20237543543574331289656273)
  ·
    refine ⟨15178157657680748467242205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20237543543574331289656273 15178157657680748467242205)
    ·
      refine ⟨5691809121630280675215827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15178157657680748467242205 5691809121630280675215827)
      ·
        refine ⟨8537713682445421012823741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5691809121630280675215827 8537713682445421012823741)
        ·
          refine ⟨3201642630917032879808903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8537713682445421012823741 3201642630917032879808903)
          ·
            refine ⟨4802463946375549319713355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3201642630917032879808903 4802463946375549319713355)
            ·
              refine ⟨7203695919563323979570033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4802463946375549319713355 7203695919563323979570033)
              ·
                refine ⟨5402771939672492984677525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7203695919563323979570033 5402771939672492984677525)
                ·
                  refine ⟨253254934672148108656759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5402771939672492984677525 253254934672148108656759)
                  ·
                    rfl

theorem cell23_4438910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_4438910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438910 prefixEnd_4438910 := by exact prefixLift 4438910
  have htrace : WordTrace (prefixWord ++ tailWord_4438910) baseStart_4438910 baseEnd_4438910 := by
    simpa [prefixWord, tailWord_4438910, baseEnd_4438910] using wordTrace_append hprefix tailTrace_4438910
  have hstable : (prefixWord ++ tailWord_4438910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438910).length < 2 ^ (prefixWord ++ tailWord_4438910).sum := by decide
  have hdescent : baseEnd_4438910 < baseStart_4438910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438943 : List Nat := [1, 1, 2, 5, 2, 1, 2, 2, 3, 2, 2]
def baseStart_4438943 : Nat := 118140960795 + 4438943 * 2 ^ 59
def prefixEnd_4438943 : Nat := 4983230072969 + 3 ^ 40 * 4438943 * 2
def baseEnd_4438943 : Nat := 2279311356910931348798179

theorem tailTrace_4438943 : CollatzResearch.WordTrace tailWord_4438943 prefixEnd_4438943 2279311356910931348798179 := by
  unfold tailWord_4438943
  simp only [CollatzResearch.WordTrace]
  refine ⟨161901551957475096953201483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107934367971650064635467655 161901551957475096953201483)
  ·
    refine ⟨242852327936212645429802225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161901551957475096953201483 242852327936212645429802225)
    ·
      refine ⟨182139245952159484072351669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242852327936212645429802225 182139245952159484072351669)
      ·
        refine ⟨17075554308014951631782969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 182139245952159484072351669 17075554308014951631782969)
        ·
          refine ⟨12806665731011213723837227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17075554308014951631782969 12806665731011213723837227)
          ·
            refine ⟨19209998596516820585755841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12806665731011213723837227 19209998596516820585755841)
            ·
              refine ⟨14407498947387615439316881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19209998596516820585755841 14407498947387615439316881)
              ·
                refine ⟨10805624210540711579487661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14407498947387615439316881 10805624210540711579487661)
                ·
                  refine ⟨4052109078952766842307873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10805624210540711579487661 4052109078952766842307873)
                  ·
                    refine ⟨3039081809214575131730905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4052109078952766842307873 3039081809214575131730905)
                    ·
                      refine ⟨2279311356910931348798179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3039081809214575131730905 2279311356910931348798179)
                      ·
                        rfl

theorem cell23_4438943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_4438943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438943 prefixEnd_4438943 := by exact prefixLift 4438943
  have htrace : WordTrace (prefixWord ++ tailWord_4438943) baseStart_4438943 baseEnd_4438943 := by
    simpa [prefixWord, tailWord_4438943, baseEnd_4438943] using wordTrace_append hprefix tailTrace_4438943
  have hstable : (prefixWord ++ tailWord_4438943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438943).length < 2 ^ (prefixWord ++ tailWord_4438943).sum := by decide
  have hdescent : baseEnd_4438943 < baseStart_4438943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438962 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 3, 9]
def baseStart_4438962 : Nat := 118140960795 + 4438962 * 2 ^ 59
def prefixEnd_4438962 : Nat := 4983230072969 + 3 ^ 40 * 4438962 * 2
def baseEnd_4438962 : Nat := 759773704347788924820197

theorem tailTrace_4438962 : CollatzResearch.WordTrace tailWord_4438962 prefixEnd_4438962 759773704347788924820197 := by
  unfold tailWord_4438962
  simp only [CollatzResearch.WordTrace]
  refine ⟨40475561236101565799535785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107934829962937508798762093 40475561236101565799535785)
  ·
    refine ⟨30356670927076174349651839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40475561236101565799535785 30356670927076174349651839)
    ·
      refine ⟨45535006390614261524477759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30356670927076174349651839 45535006390614261524477759)
      ·
        refine ⟨68302509585921392286716639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45535006390614261524477759 68302509585921392286716639)
        ·
          refine ⟨102453764378882088430074959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68302509585921392286716639 102453764378882088430074959)
          ·
            refine ⟨153680646568323132645112439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102453764378882088430074959 153680646568323132645112439)
            ·
              refine ⟨230520969852484698967668659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153680646568323132645112439 230520969852484698967668659)
              ·
                refine ⟨345781454778727048451502989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 230520969852484698967668659 345781454778727048451502989)
                ·
                  refine ⟨129668045542022643169313621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 345781454778727048451502989 129668045542022643169313621)
                  ·
                    refine ⟨759773704347788924820197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 129668045542022643169313621 759773704347788924820197)
                    ·
                      rfl

theorem cell23_4438962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_4438962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438962 prefixEnd_4438962 := by exact prefixLift 4438962
  have htrace : WordTrace (prefixWord ++ tailWord_4438962) baseStart_4438962 baseEnd_4438962 := by
    simpa [prefixWord, tailWord_4438962, baseEnd_4438962] using wordTrace_append hprefix tailTrace_4438962
  have hstable : (prefixWord ++ tailWord_4438962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438962).length < 2 ^ (prefixWord ++ tailWord_4438962).sum := by decide
  have hdescent : baseEnd_4438962 < baseStart_4438962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438976 : List Nat := [2, 1, 1, 2, 3, 3, 2, 1, 4, 1, 3]
def baseStart_4438976 : Nat := 118140960795 + 4438976 * 2 ^ 59
def prefixEnd_4438976 : Nat := 4983230072969 + 3 ^ 40 * 4438976 * 2
def baseEnd_4438976 : Nat := 2279328301772529719685527

theorem tailTrace_4438976 : CollatzResearch.WordTrace tailWord_4438976 prefixEnd_4438976 2279328301772529719685527 := by
  unfold tailWord_4438976
  simp only [CollatzResearch.WordTrace]
  refine ⟨80951377783177771794576391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107935170377570362392768521 80951377783177771794576391)
  ·
    refine ⟨121427066674766657691864587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80951377783177771794576391 121427066674766657691864587)
    ·
      refine ⟨182140600012149986537796881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121427066674766657691864587 182140600012149986537796881)
      ·
        refine ⟨136605450009112489903347661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182140600012149986537796881 136605450009112489903347661)
        ·
          refine ⟨51227043753417183713755373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136605450009112489903347661 51227043753417183713755373)
          ·
            refine ⟨19210141407531443892658265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51227043753417183713755373 19210141407531443892658265)
            ·
              refine ⟨14407606055648582919493699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19210141407531443892658265 14407606055648582919493699)
              ·
                refine ⟨21611409083472874379240549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14407606055648582919493699 21611409083472874379240549)
                ·
                  refine ⟨4052139203151163946107603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21611409083472874379240549 4052139203151163946107603)
                  ·
                    refine ⟨6078208804726745919161405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4052139203151163946107603 6078208804726745919161405)
                    ·
                      refine ⟨2279328301772529719685527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6078208804726745919161405 2279328301772529719685527)
                      ·
                        rfl

theorem cell23_4438976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 4, 1, 3].length) (baseStart_4438976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438976 prefixEnd_4438976 := by exact prefixLift 4438976
  have htrace : WordTrace (prefixWord ++ tailWord_4438976) baseStart_4438976 baseEnd_4438976 := by
    simpa [prefixWord, tailWord_4438976, baseEnd_4438976] using wordTrace_append hprefix tailTrace_4438976
  have hstable : (prefixWord ++ tailWord_4438976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438976).length < 2 ^ (prefixWord ++ tailWord_4438976).sum := by decide
  have hdescent : baseEnd_4438976 < baseStart_4438976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438986 : List Nat := [3, 1, 2, 1, 2, 1, 1, 4, 3, 3, 2]
def baseStart_4438986 : Nat := 118140960795 + 4438986 * 2 ^ 59
def prefixEnd_4438986 : Nat := 4983230072969 + 3 ^ 40 * 4438986 * 2
def baseEnd_4438986 : Nat := 2279333436579074680560481

theorem tailTrace_4438986 : CollatzResearch.WordTrace tailWord_4438986 prefixEnd_4438986 2279333436579074680560481 := by
  unfold tailWord_4438986
  simp only [CollatzResearch.WordTrace]
  refine ⟨40475780074079828824254203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107935413530879543531344541 40475780074079828824254203)
  ·
    refine ⟨60713670111119743236381305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40475780074079828824254203 60713670111119743236381305)
    ·
      refine ⟨45535252583339807427285979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60713670111119743236381305 45535252583339807427285979)
      ·
        refine ⟨68302878875009711140928969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45535252583339807427285979 68302878875009711140928969)
        ·
          refine ⟨51227159156257283355696727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68302878875009711140928969 51227159156257283355696727)
          ·
            refine ⟨76840738734385925033545091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51227159156257283355696727 76840738734385925033545091)
            ·
              refine ⟨115261108101578887550317637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76840738734385925033545091 115261108101578887550317637)
              ·
                refine ⟨21611457769046041415684557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 115261108101578887550317637 21611457769046041415684557)
                ·
                  refine ⟨8104296663392265530881709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21611457769046041415684557 8104296663392265530881709)
                  ·
                    refine ⟨3039111248772099574080641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8104296663392265530881709 3039111248772099574080641)
                    ·
                      refine ⟨2279333436579074680560481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3039111248772099574080641 2279333436579074680560481)
                      ·
                        rfl

theorem cell23_4438986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 3, 3, 2].length) (baseStart_4438986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438986 prefixEnd_4438986 := by exact prefixLift 4438986
  have htrace : WordTrace (prefixWord ++ tailWord_4438986) baseStart_4438986 baseEnd_4438986 := by
    simpa [prefixWord, tailWord_4438986, baseEnd_4438986] using wordTrace_append hprefix tailTrace_4438986
  have hstable : (prefixWord ++ tailWord_4438986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438986).length < 2 ^ (prefixWord ++ tailWord_4438986).sum := by decide
  have hdescent : baseEnd_4438986 < baseStart_4438986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4438992 : List Nat := [2, 1, 1, 1, 1, 2, 3, 3, 1, 8]
def baseStart_4438992 : Nat := 118140960795 + 4438992 * 2 ^ 59
def prefixEnd_4438992 : Nat := 4983230072969 + 3 ^ 40 * 4438992 * 2
def baseEnd_4438992 : Nat := 759778839154333885695151

theorem tailTrace_4438992 : CollatzResearch.WordTrace tailWord_4438992 prefixEnd_4438992 759778839154333885695151 := by
  unfold tailWord_4438992
  simp only [CollatzResearch.WordTrace]
  refine ⟨80951669567148789160867615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107935559422865052214490153 80951669567148789160867615)
  ·
    refine ⟨121427504350723183741301423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80951669567148789160867615 121427504350723183741301423)
    ·
      refine ⟨182141256526084775611952135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121427504350723183741301423 182141256526084775611952135)
      ·
        refine ⟨273211884789127163417928203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182141256526084775611952135 273211884789127163417928203)
        ·
          refine ⟨409817827183690745126892305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273211884789127163417928203 409817827183690745126892305)
          ·
            refine ⟨307363370387768058845169229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 409817827183690745126892305 307363370387768058845169229)
            ·
              refine ⟨115261263895413022066938461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 307363370387768058845169229 115261263895413022066938461)
              ·
                refine ⟨43222973960779883275101923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115261263895413022066938461 43222973960779883275101923)
                ·
                  refine ⟨64834460941169824912652885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43222973960779883275101923 64834460941169824912652885)
                  ·
                    refine ⟨759778839154333885695151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 64834460941169824912652885 759778839154333885695151)
                    ·
                      rfl

theorem cell23_4438992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 1, 8].length) (baseStart_4438992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4438992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4438992 prefixEnd_4438992 := by exact prefixLift 4438992
  have htrace : WordTrace (prefixWord ++ tailWord_4438992) baseStart_4438992 baseEnd_4438992 := by
    simpa [prefixWord, tailWord_4438992, baseEnd_4438992] using wordTrace_append hprefix tailTrace_4438992
  have hstable : (prefixWord ++ tailWord_4438992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4438992).length < 2 ^ (prefixWord ++ tailWord_4438992).sum := by decide
  have hdescent : baseEnd_4438992 < baseStart_4438992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4438992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439016 : List Nat := [2, 1, 4, 1, 1, 1, 3, 1, 3, 4, 2]
def baseStart_4439016 : Nat := 118140960795 + 4439016 * 2 ^ 59
def prefixEnd_4439016 : Nat := 4983230072969 + 3 ^ 40 * 4439016 * 2
def baseEnd_4439016 : Nat := 2279348840998709563185343

theorem tailTrace_4439016 : CollatzResearch.WordTrace tailWord_4439016 prefixEnd_4439016 2279348840998709563185343 := by
  unfold tailWord_4439016
  simp only [CollatzResearch.WordTrace]
  refine ⟨80952107243105315210304451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107936142990807086947072601 80952107243105315210304451)
  ·
    refine ⟨121428160864657972815456677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80952107243105315210304451 121428160864657972815456677)
    ·
      refine ⟨22767780162123369902898127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121428160864657972815456677 22767780162123369902898127)
      ·
        refine ⟨34151670243185054854347191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22767780162123369902898127 34151670243185054854347191)
        ·
          refine ⟨51227505364777582281520787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34151670243185054854347191 51227505364777582281520787)
          ·
            refine ⟨76841258047166373422281181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51227505364777582281520787 76841258047166373422281181)
            ·
              refine ⟨28815471767687390033355443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76841258047166373422281181 28815471767687390033355443)
              ·
                refine ⟨43223207651531085050033165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28815471767687390033355443 43223207651531085050033165)
                ·
                  refine ⟨16208702869324156893762437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43223207651531085050033165 16208702869324156893762437)
                  ·
                    refine ⟨3039131787998279417580457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16208702869324156893762437 3039131787998279417580457)
                    ·
                      refine ⟨2279348840998709563185343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3039131787998279417580457 2279348840998709563185343)
                      ·
                        rfl

theorem cell23_4439016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_4439016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439016 prefixEnd_4439016 := by exact prefixLift 4439016
  have htrace : WordTrace (prefixWord ++ tailWord_4439016) baseStart_4439016 baseEnd_4439016 := by
    simpa [prefixWord, tailWord_4439016, baseEnd_4439016] using wordTrace_append hprefix tailTrace_4439016
  have hstable : (prefixWord ++ tailWord_4439016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439016).length < 2 ^ (prefixWord ++ tailWord_4439016).sum := by decide
  have hdescent : baseEnd_4439016 < baseStart_4439016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439028 : List Nat := [2, 6, 2, 1, 1, 1, 1, 4, 1, 2, 2]
def baseStart_4439028 : Nat := 118140960795 + 4439028 * 2 ^ 59
def prefixEnd_4439028 : Nat := 4983230072969 + 3 ^ 40 * 4439028 * 2
def baseEnd_4439028 : Nat := 2279355002766563516235289

theorem tailTrace_4439028 : CollatzResearch.WordTrace tailWord_4439028 prefixEnd_4439028 2279355002766563516235289 := by
  unfold tailWord_4439028
  simp only [CollatzResearch.WordTrace]
  refine ⟨80952326081083578235022869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107936434774778104313363825 80952326081083578235022869)
  ·
    refine ⟨3794640285050792729766697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 80952326081083578235022869 3794640285050792729766697)
    ·
      refine ⟨2845980213788094547325023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3794640285050792729766697 2845980213788094547325023)
      ·
        refine ⟨4268970320682141820987535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2845980213788094547325023 4268970320682141820987535)
        ·
          refine ⟨6403455481023212731481303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4268970320682141820987535 6403455481023212731481303)
          ·
            refine ⟨9605183221534819097221955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6403455481023212731481303 9605183221534819097221955)
            ·
              refine ⟨14407774832302228645832933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9605183221534819097221955 14407774832302228645832933)
              ·
                refine ⟨2701457781056667871093675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14407774832302228645832933 2701457781056667871093675)
                ·
                  refine ⟨4052186671585001806640513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2701457781056667871093675 4052186671585001806640513)
                  ·
                    refine ⟨3039140003688751354980385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4052186671585001806640513 3039140003688751354980385)
                    ·
                      refine ⟨2279355002766563516235289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3039140003688751354980385 2279355002766563516235289)
                      ·
                        rfl

theorem cell23_4439028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_4439028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439028 prefixEnd_4439028 := by exact prefixLift 4439028
  have htrace : WordTrace (prefixWord ++ tailWord_4439028) baseStart_4439028 baseEnd_4439028 := by
    simpa [prefixWord, tailWord_4439028, baseEnd_4439028] using wordTrace_append hprefix tailTrace_4439028
  have hstable : (prefixWord ++ tailWord_4439028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439028).length < 2 ^ (prefixWord ++ tailWord_4439028).sum := by decide
  have hdescent : baseEnd_4439028 < baseStart_4439028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439050 : List Nat := [3, 1, 2, 2, 3, 1, 2, 3, 2, 2, 2]
def baseStart_4439050 : Nat := 118140960795 + 4439050 * 2 ^ 59
def prefixEnd_4439050 : Nat := 4983230072969 + 3 ^ 40 * 4439050 * 2
def baseEnd_4439050 : Nat := 2279366299340962430160187

theorem tailTrace_4439050 : CollatzResearch.WordTrace tailWord_4439050 prefixEnd_4439050 2279366299340962430160187 := by
  unfold tailWord_4439050
  simp only [CollatzResearch.WordTrace]
  refine ⟨40476363642021863556836651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107936969712058302818231069 40476363642021863556836651)
  ·
    refine ⟨60714545463032795335254977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40476363642021863556836651 60714545463032795335254977)
    ·
      refine ⟨45535909097274596501441233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60714545463032795335254977 45535909097274596501441233)
      ·
        refine ⟨34151931822955947376080925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45535909097274596501441233 34151931822955947376080925)
        ·
          refine ⟨12806974433608480266030347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34151931822955947376080925 12806974433608480266030347)
          ·
            refine ⟨19210461650412720399045521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12806974433608480266030347 19210461650412720399045521)
            ·
              refine ⟨14407846237809540299284141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19210461650412720399045521 14407846237809540299284141)
              ·
                refine ⟨5402942339178577612231553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14407846237809540299284141 5402942339178577612231553)
                ·
                  refine ⟨4052206754383933209173665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5402942339178577612231553 4052206754383933209173665)
                  ·
                    refine ⟨3039155065787949906880249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4052206754383933209173665 3039155065787949906880249)
                    ·
                      refine ⟨2279366299340962430160187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3039155065787949906880249 2279366299340962430160187)
                      ·
                        rfl

theorem cell23_4439050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_4439050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439050 prefixEnd_4439050 := by exact prefixLift 4439050
  have htrace : WordTrace (prefixWord ++ tailWord_4439050) baseStart_4439050 baseEnd_4439050 := by
    simpa [prefixWord, tailWord_4439050, baseEnd_4439050] using wordTrace_append hprefix tailTrace_4439050
  have hstable : (prefixWord ++ tailWord_4439050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439050).length < 2 ^ (prefixWord ++ tailWord_4439050).sum := by decide
  have hdescent : baseEnd_4439050 < baseStart_4439050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439073 : List Nat := [1, 2, 3, 2, 3, 2, 2, 3, 5]
def baseStart_4439073 : Nat := 118140960795 + 4439073 * 2 ^ 59
def prefixEnd_4439073 : Nat := 4983230072969 + 3 ^ 40 * 4439073 * 2
def baseEnd_4439073 : Nat := 253264234377335093352509

theorem tailTrace_4439073 : CollatzResearch.WordTrace tailWord_4439073 prefixEnd_4439073 253264234377335093352509 := by
  unfold tailWord_4439073
  simp only [CollatzResearch.WordTrace]
  refine ⟨161906293447004129155433873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107937528964669419436955915 161906293447004129155433873)
  ·
    refine ⟨121429720085253096866575405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161906293447004129155433873 121429720085253096866575405)
    ·
      refine ⟨45536145031969911324965777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121429720085253096866575405 45536145031969911324965777)
      ·
        refine ⟨34152108773977433493724333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45536145031969911324965777 34152108773977433493724333)
        ·
          refine ⟨12807040790241537560146625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34152108773977433493724333 12807040790241537560146625)
          ·
            refine ⟨9605280592681153170109969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12807040790241537560146625 9605280592681153170109969)
            ·
              refine ⟨7203960444510864877582477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9605280592681153170109969 7203960444510864877582477)
              ·
                refine ⟨2701485166691574329093429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7203960444510864877582477 2701485166691574329093429)
                ·
                  refine ⟨253264234377335093352509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2701485166691574329093429 253264234377335093352509)
                  ·
                    rfl

theorem cell23_4439073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 3, 5].length) (baseStart_4439073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439073 prefixEnd_4439073 := by exact prefixLift 4439073
  have htrace : WordTrace (prefixWord ++ tailWord_4439073) baseStart_4439073 baseEnd_4439073 := by
    simpa [prefixWord, tailWord_4439073, baseEnd_4439073] using wordTrace_append hprefix tailTrace_4439073
  have hstable : (prefixWord ++ tailWord_4439073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439073).length < 2 ^ (prefixWord ++ tailWord_4439073).sum := by decide
  have hdescent : baseEnd_4439073 < baseStart_4439073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439086 : List Nat := [4, 1, 3, 1, 1, 1, 2, 1, 4, 5]
def baseStart_4439086 : Nat := 118140960795 + 4439086 * 2 ^ 59
def prefixEnd_4439086 : Nat := 4983230072969 + 3 ^ 40 * 4439086 * 2
def baseEnd_4439086 : Nat := 759794928214841429770007

theorem tailTrace_4439086 : CollatzResearch.WordTrace tailWord_4439086 prefixEnd_4439086 759794928214841429770007 := by
  unfold tailWord_4439086
  simp only [CollatzResearch.WordTrace]
  refine ⟨20238345949494629046957139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107937845063971354917104741 20238345949494629046957139)
  ·
    refine ⟨30357518924241943570435709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20238345949494629046957139 30357518924241943570435709)
    ·
      refine ⟨11384069596590728838913391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30357518924241943570435709 11384069596590728838913391)
      ·
        refine ⟨17076104394886093258370087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11384069596590728838913391 17076104394886093258370087)
        ·
          refine ⟨25614156592329139887555131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17076104394886093258370087 25614156592329139887555131)
          ·
            refine ⟨38421234888493709831332697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25614156592329139887555131 38421234888493709831332697)
            ·
              refine ⟨28815926166370282373499523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38421234888493709831332697 28815926166370282373499523)
              ·
                refine ⟨43223889249555423560249285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28815926166370282373499523 43223889249555423560249285)
                ·
                  refine ⟨8104479234291641917546741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43223889249555423560249285 8104479234291641917546741)
                  ·
                    refine ⟨759794928214841429770007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8104479234291641917546741 759794928214841429770007)
                    ·
                      rfl

theorem cell23_4439086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_4439086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439086 prefixEnd_4439086 := by exact prefixLift 4439086
  have htrace : WordTrace (prefixWord ++ tailWord_4439086) baseStart_4439086 baseEnd_4439086 := by
    simpa [prefixWord, tailWord_4439086, baseEnd_4439086] using wordTrace_append hprefix tailTrace_4439086
  have hstable : (prefixWord ++ tailWord_4439086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439086).length < 2 ^ (prefixWord ++ tailWord_4439086).sum := by decide
  have hdescent : baseEnd_4439086 < baseStart_4439086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439143 : List Nat := [1, 1, 5, 1, 1, 4, 1, 2, 2, 2, 3]
def baseStart_4439143 : Nat := 118140960795 + 4439143 * 2 ^ 59
def prefixEnd_4439143 : Nat := 4983230072969 + 3 ^ 40 * 4439143 * 2
def baseEnd_4439143 : Nat := 2279414053041830566297259

theorem tailTrace_4439143 : CollatzResearch.WordTrace tailWord_4439143 prefixEnd_4439143 2279414053041830566297259 := by
  unfold tailWord_4439143
  simp only [CollatzResearch.WordTrace]
  refine ⟨161908846556750531110482083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107939231037833687406988055 161908846556750531110482083)
  ·
    refine ⟨242863269835125796665723125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161908846556750531110482083 242863269835125796665723125)
    ·
      refine ⟨22768431547043043437411543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 242863269835125796665723125 22768431547043043437411543)
      ·
        refine ⟨34152647320564565156117315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22768431547043043437411543 34152647320564565156117315)
        ·
          refine ⟨51228970980846847734175973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34152647320564565156117315 51228970980846847734175973)
          ·
            refine ⟨9605432058908783950157995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51228970980846847734175973 9605432058908783950157995)
            ·
              refine ⟨14408148088363175925236993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9605432058908783950157995 14408148088363175925236993)
              ·
                refine ⟨10806111066272381943927745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14408148088363175925236993 10806111066272381943927745)
                ·
                  refine ⟨8104583299704286457945809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10806111066272381943927745 8104583299704286457945809)
                  ·
                    refine ⟨6078437474778214843459357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8104583299704286457945809 6078437474778214843459357)
                    ·
                      refine ⟨2279414053041830566297259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6078437474778214843459357 2279414053041830566297259)
                      ·
                        rfl

theorem cell23_4439143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_4439143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439143 prefixEnd_4439143 := by exact prefixLift 4439143
  have htrace : WordTrace (prefixWord ++ tailWord_4439143) baseStart_4439143 baseEnd_4439143 := by
    simpa [prefixWord, tailWord_4439143, baseEnd_4439143] using wordTrace_append hprefix tailTrace_4439143
  have hstable : (prefixWord ++ tailWord_4439143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439143).length < 2 ^ (prefixWord ++ tailWord_4439143).sum := by decide
  have hdescent : baseEnd_4439143 < baseStart_4439143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439146 : List Nat := [3, 1, 3, 2, 2, 1, 2, 1, 8]
def baseStart_4439146 : Nat := 118140960795 + 4439146 * 2 ^ 59
def prefixEnd_4439146 : Nat := 4983230072969 + 3 ^ 40 * 4439146 * 2
def baseEnd_4439146 : Nat := 253268399275977117173305

theorem tailTrace_4439146 : CollatzResearch.WordTrace tailWord_4439146 prefixEnd_4439146 253268399275977117173305 := by
  unfold tailWord_4439146
  simp only [CollatzResearch.WordTrace]
  refine ⟨40477238993934915655710323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107939303983826441748560861 40477238993934915655710323)
  ·
    refine ⟨60715858490902373483565485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40477238993934915655710323 60715858490902373483565485)
    ·
      refine ⟨22768446934088390056337057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60715858490902373483565485 22768446934088390056337057)
      ·
        refine ⟨17076335200566292542252793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22768446934088390056337057 17076335200566292542252793)
        ·
          refine ⟨12807251400424719406689595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17076335200566292542252793 12807251400424719406689595)
          ·
            refine ⟨19210877100637079110034393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12807251400424719406689595 19210877100637079110034393)
            ·
              refine ⟨14408157825477809332525795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19210877100637079110034393 14408157825477809332525795)
              ·
                refine ⟨21612236738216713998788693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14408157825477809332525795 21612236738216713998788693)
                ·
                  refine ⟨253268399275977117173305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21612236738216713998788693 253268399275977117173305)
                  ·
                    rfl

theorem cell23_4439146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 8].length) (baseStart_4439146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439146 prefixEnd_4439146 := by exact prefixLift 4439146
  have htrace : WordTrace (prefixWord ++ tailWord_4439146) baseStart_4439146 baseEnd_4439146 := by
    simpa [prefixWord, tailWord_4439146, baseEnd_4439146] using wordTrace_append hprefix tailTrace_4439146
  have hstable : (prefixWord ++ tailWord_4439146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439146).length < 2 ^ (prefixWord ++ tailWord_4439146).sum := by decide
  have hdescent : baseEnd_4439146 < baseStart_4439146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439150 : List Nat := [4, 1, 2, 2, 1, 4, 1, 1, 3, 4]
def baseStart_4439150 : Nat := 118140960795 + 4439150 * 2 ^ 59
def prefixEnd_4439150 : Nat := 4983230072969 + 3 ^ 40 * 4439150 * 2
def baseEnd_4439150 : Nat := 759805882468804012969909

theorem tailTrace_4439150 : CollatzResearch.WordTrace tailWord_4439150 prefixEnd_4439150 759805882468804012969909 := by
  unfold tailWord_4439150
  simp only [CollatzResearch.WordTrace]
  refine ⟨20238637733465646413248363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107939401245150114203991269 20238637733465646413248363)
  ·
    refine ⟨30357956600198469619872545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20238637733465646413248363 30357956600198469619872545)
    ·
      refine ⟨22768467450148852214904409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30357956600198469619872545 22768467450148852214904409)
      ·
        refine ⟨17076350587611639161178307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22768467450148852214904409 17076350587611639161178307)
        ·
          refine ⟨25614525881417458741767461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17076350587611639161178307 25614525881417458741767461)
          ·
            refine ⟨4802723602765773514081399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25614525881417458741767461 4802723602765773514081399)
            ·
              refine ⟨7204085404148660271122099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4802723602765773514081399 7204085404148660271122099)
              ·
                refine ⟨10806128106222990406683149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7204085404148660271122099 10806128106222990406683149)
                ·
                  refine ⟨4052298039833621402506181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10806128106222990406683149 4052298039833621402506181)
                  ·
                    refine ⟨759805882468804012969909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4052298039833621402506181 759805882468804012969909)
                    ·
                      rfl

theorem cell23_4439150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_4439150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439150 prefixEnd_4439150 := by exact prefixLift 4439150
  have htrace : WordTrace (prefixWord ++ tailWord_4439150) baseStart_4439150 baseEnd_4439150 := by
    simpa [prefixWord, tailWord_4439150, baseEnd_4439150] using wordTrace_append hprefix tailTrace_4439150
  have hstable : (prefixWord ++ tailWord_4439150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439150).length < 2 ^ (prefixWord ++ tailWord_4439150).sum := by decide
  have hdescent : baseEnd_4439150 < baseStart_4439150 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439223 : List Nat := [1, 1, 3, 1, 4, 1, 1, 5, 2, 4]
def baseStart_4439223 : Nat := 118140960795 + 4439223 * 2 ^ 59
def prefixEnd_4439223 : Nat := 4983230072969 + 3 ^ 40 * 4439223 * 2
def baseEnd_4439223 : Nat := 759818377164730084432297

theorem tailTrace_4439223 : CollatzResearch.WordTrace tailWord_4439223 prefixEnd_4439223 759818377164730084432297 := by
  unfold tailWord_4439223
  simp only [CollatzResearch.WordTrace]
  refine ⟨161911764396460704773394323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107941176264307136515596215 161911764396460704773394323)
  ·
    refine ⟨242867646594691057160091485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161911764396460704773394323 242867646594691057160091485)
    ·
      refine ⟨91075367473009146435034307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 242867646594691057160091485 91075367473009146435034307)
      ·
        refine ⟨136613051209513719652551461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91075367473009146435034307 136613051209513719652551461)
        ·
          refine ⟨25614947101783822434853399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136613051209513719652551461 25614947101783822434853399)
          ·
            refine ⟨38422420652675733652280099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25614947101783822434853399 38422420652675733652280099)
            ·
              refine ⟨57633630979013600478420149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38422420652675733652280099 57633630979013600478420149)
              ·
                refine ⟨5403152904282525044851889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57633630979013600478420149 5403152904282525044851889)
                ·
                  refine ⟨4052364678211893783638917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5403152904282525044851889 4052364678211893783638917)
                  ·
                    refine ⟨759818377164730084432297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4052364678211893783638917 759818377164730084432297)
                    ·
                      rfl

theorem cell23_4439223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 2, 4].length) (baseStart_4439223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439223 prefixEnd_4439223 := by exact prefixLift 4439223
  have htrace : WordTrace (prefixWord ++ tailWord_4439223) baseStart_4439223 baseEnd_4439223 := by
    simpa [prefixWord, tailWord_4439223, baseEnd_4439223] using wordTrace_append hprefix tailTrace_4439223
  have hstable : (prefixWord ++ tailWord_4439223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439223).length < 2 ^ (prefixWord ++ tailWord_4439223).sum := by decide
  have hdescent : baseEnd_4439223 < baseStart_4439223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439234 : List Nat := [3, 5, 1, 1, 2, 1, 1, 1, 1, 5, 2]
def baseStart_4439234 : Nat := 118140960795 + 4439234 * 2 ^ 59
def prefixEnd_4439234 : Nat := 4983230072969 + 3 ^ 40 * 4439234 * 2
def baseEnd_4439234 : Nat := 2279460779781389710259341

theorem tailTrace_4439234 : CollatzResearch.WordTrace tailWord_4439234 prefixEnd_4439234 2279460779781389710259341 := by
  unfold tailWord_4439234
  simp only [CollatzResearch.WordTrace]
  refine ⟨40478041399855213413011189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107941443732947235768029837 40478041399855213413011189)
  ·
    refine ⟨3794816381236426257469799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40478041399855213413011189 3794816381236426257469799)
    ·
      refine ⟨5692224571854639386204699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3794816381236426257469799 5692224571854639386204699)
      ·
        refine ⟨8538336857781959079307049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5692224571854639386204699 8538336857781959079307049)
        ·
          refine ⟨6403752643336469309480287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8538336857781959079307049 6403752643336469309480287)
          ·
            refine ⟨9605628965004703964220431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6403752643336469309480287 9605628965004703964220431)
            ·
              refine ⟨14408443447507055946330647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9605628965004703964220431 14408443447507055946330647)
              ·
                refine ⟨21612665171260583919495971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14408443447507055946330647 21612665171260583919495971)
                ·
                  refine ⟨32418997756890875879243957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21612665171260583919495971 32418997756890875879243957)
                  ·
                    refine ⟨3039281039708519613679121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32418997756890875879243957 3039281039708519613679121)
                    ·
                      refine ⟨2279460779781389710259341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3039281039708519613679121 2279460779781389710259341)
                      ·
                        rfl

theorem cell23_4439234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_4439234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439234 prefixEnd_4439234 := by exact prefixLift 4439234
  have htrace : WordTrace (prefixWord ++ tailWord_4439234) baseStart_4439234 baseEnd_4439234 := by
    simpa [prefixWord, tailWord_4439234, baseEnd_4439234] using wordTrace_append hprefix tailTrace_4439234
  have hstable : (prefixWord ++ tailWord_4439234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439234).length < 2 ^ (prefixWord ++ tailWord_4439234).sum := by decide
  have hdescent : baseEnd_4439234 < baseStart_4439234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439250 : List Nat := [3, 2, 2, 2, 1, 1, 3, 3, 1, 2, 3]
def baseStart_4439250 : Nat := 118140960795 + 4439250 * 2 ^ 59
def prefixEnd_4439250 : Nat := 4983230072969 + 3 ^ 40 * 4439250 * 2
def baseEnd_4439250 : Nat := 2279468995471861647659267

theorem tailTrace_4439250 : CollatzResearch.WordTrace tailWord_4439250 prefixEnd_4439250 2279468995471861647659267 := by
  unfold tailWord_4439250
  simp only [CollatzResearch.WordTrace]
  refine ⟨40478187291840722096156801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107941832778241925589751469 40478187291840722096156801)
  ·
    refine ⟨30358640468880541572117601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40478187291840722096156801 30358640468880541572117601)
    ·
      refine ⟨22768980351660406179088201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30358640468880541572117601 22768980351660406179088201)
      ·
        refine ⟨17076735263745304634316151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22768980351660406179088201 17076735263745304634316151)
        ·
          refine ⟨25615102895617956951474227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17076735263745304634316151 25615102895617956951474227)
          ·
            refine ⟨38422654343426935427211341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25615102895617956951474227 38422654343426935427211341)
            ·
              refine ⟨14408495378785100785204253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38422654343426935427211341 14408495378785100785204253)
              ·
                refine ⟨5403185767044412794451595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14408495378785100785204253 5403185767044412794451595)
                ·
                  refine ⟨8104778650566619191677393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5403185767044412794451595 8104778650566619191677393)
                  ·
                    refine ⟨6078583987924964393758045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8104778650566619191677393 6078583987924964393758045)
                    ·
                      refine ⟨2279468995471861647659267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6078583987924964393758045 2279468995471861647659267)
                      ·
                        rfl

theorem cell23_4439250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_4439250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439250 prefixEnd_4439250 := by exact prefixLift 4439250
  have htrace : WordTrace (prefixWord ++ tailWord_4439250) baseStart_4439250 baseEnd_4439250 := by
    simpa [prefixWord, tailWord_4439250, baseEnd_4439250] using wordTrace_append hprefix tailTrace_4439250
  have hstable : (prefixWord ++ tailWord_4439250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439250).length < 2 ^ (prefixWord ++ tailWord_4439250).sum := by decide
  have hdescent : baseEnd_4439250 < baseStart_4439250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439298 : List Nat := [3, 4, 1, 1, 3, 2, 1, 3, 1, 2, 2]
def baseStart_4439298 : Nat := 118140960795 + 4439298 * 2 ^ 59
def prefixEnd_4439298 : Nat := 4983230072969 + 3 ^ 40 * 4439298 * 2
def baseEnd_4439298 : Nat := 2279493642543277459859047

theorem tailTrace_4439298 : CollatzResearch.WordTrace tailWord_4439298 prefixEnd_4439298 2279493642543277459859047 := by
  unfold tailWord_4439298
  simp only [CollatzResearch.WordTrace]
  refine ⟨40478624967797248145593637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107942999914125995054916365 40478624967797248145593637)
  ·
    refine ⟨7589742181461984027298807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40478624967797248145593637 7589742181461984027298807)
    ·
      refine ⟨11384613272192976040948211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7589742181461984027298807 11384613272192976040948211)
      ·
        refine ⟨17076919908289464061422317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11384613272192976040948211 17076919908289464061422317)
        ·
          refine ⟨6403844965608549023033369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17076919908289464061422317 6403844965608549023033369)
          ·
            refine ⟨4802883724206411767275027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6403844965608549023033369 4802883724206411767275027)
            ·
              refine ⟨7204325586309617650912541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4802883724206411767275027 7204325586309617650912541)
              ·
                refine ⟨2701622094866106619092203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7204325586309617650912541 2701622094866106619092203)
                ·
                  refine ⟨4052433142299159928638305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2701622094866106619092203 4052433142299159928638305)
                  ·
                    refine ⟨3039324856724369946478729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4052433142299159928638305 3039324856724369946478729)
                    ·
                      refine ⟨2279493642543277459859047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3039324856724369946478729 2279493642543277459859047)
                      ·
                        rfl

theorem cell23_4439298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_4439298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439298 prefixEnd_4439298 := by exact prefixLift 4439298
  have htrace : WordTrace (prefixWord ++ tailWord_4439298) baseStart_4439298 baseEnd_4439298 := by
    simpa [prefixWord, tailWord_4439298, baseEnd_4439298] using wordTrace_append hprefix tailTrace_4439298
  have hstable : (prefixWord ++ tailWord_4439298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439298).length < 2 ^ (prefixWord ++ tailWord_4439298).sum := by decide
  have hdescent : baseEnd_4439298 < baseStart_4439298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439341 : List Nat := [1, 5, 3, 1, 1, 3, 1, 2, 1, 3, 2]
def baseStart_4439341 : Nat := 118140960795 + 4439341 * 2 ^ 59
def prefixEnd_4439341 : Nat := 4983230072969 + 3 ^ 40 * 4439341 * 2
def baseEnd_4439341 : Nat := 2279515722211420791621349

theorem tailTrace_4439341 : CollatzResearch.WordTrace tailWord_4439341 prefixEnd_4439341 2279515722211420791621349 := by
  unfold tailWord_4439341
  simp only [CollatzResearch.WordTrace]
  refine ⟨161916068210033210926189877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107944045473355473950793251 161916068210033210926189877)
  ·
    refine ⟨15179631394690613524330301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 161916068210033210926189877 15179631394690613524330301)
    ·
      refine ⟨5692361773008980071623863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15179631394690613524330301 5692361773008980071623863)
      ·
        refine ⟨8538542659513470107435795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5692361773008980071623863 8538542659513470107435795)
        ·
          refine ⟨12807813989270205161153693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8538542659513470107435795 12807813989270205161153693)
          ·
            refine ⟨4802930245976326935432635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12807813989270205161153693 4802930245976326935432635)
            ·
              refine ⟨7204395368964490403148953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4802930245976326935432635 7204395368964490403148953)
              ·
                refine ⟨5403296526723367802361715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7204395368964490403148953 5403296526723367802361715)
                ·
                  refine ⟨8104944790085051703542573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5403296526723367802361715 8104944790085051703542573)
                  ·
                    refine ⟨3039354296281894388828465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8104944790085051703542573 3039354296281894388828465)
                    ·
                      refine ⟨2279515722211420791621349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3039354296281894388828465 2279515722211420791621349)
                      ·
                        rfl

theorem cell23_4439341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_4439341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439341 prefixEnd_4439341 := by exact prefixLift 4439341
  have htrace : WordTrace (prefixWord ++ tailWord_4439341) baseStart_4439341 baseEnd_4439341 := by
    simpa [prefixWord, tailWord_4439341, baseEnd_4439341] using wordTrace_append hprefix tailTrace_4439341
  have hstable : (prefixWord ++ tailWord_4439341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439341).length < 2 ^ (prefixWord ++ tailWord_4439341).sum := by decide
  have hdescent : baseEnd_4439341 < baseStart_4439341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439380 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 1, 7, 2]
def baseStart_4439380 : Nat := 118140960795 + 4439380 * 2 ^ 59
def prefixEnd_4439380 : Nat := 4983230072969 + 3 ^ 40 * 4439380 * 2
def baseEnd_4439380 : Nat := 2279535747956946139033669

theorem tailTrace_4439380 : CollatzResearch.WordTrace tailWord_4439380 prefixEnd_4439380 2279535747956946139033669 := by
  unfold tailWord_4439380
  simp only [CollatzResearch.WordTrace]
  refine ⟨80958745328445960293429797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107944993771261280391239729 80958745328445960293429797)
  ·
    refine ⟨15179764749083617555018087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80958745328445960293429797 15179764749083617555018087)
    ·
      refine ⟨22769647123625426332527131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15179764749083617555018087 22769647123625426332527131)
      ·
        refine ⟨34154470685438139498790697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22769647123625426332527131 34154470685438139498790697)
        ·
          refine ⟨25615853014078604624093023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34154470685438139498790697 25615853014078604624093023)
          ·
            refine ⟨38423779521117906936139535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25615853014078604624093023 38423779521117906936139535)
            ·
              refine ⟨57635669281676860404209303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38423779521117906936139535 57635669281676860404209303)
              ·
                refine ⟨86453503922515290606313955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57635669281676860404209303 86453503922515290606313955)
                ·
                  refine ⟨129680255883772935909470933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86453503922515290606313955 129680255883772935909470933)
                  ·
                    refine ⟨3039380997275928185378225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 129680255883772935909470933 3039380997275928185378225)
                    ·
                      refine ⟨2279535747956946139033669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3039380997275928185378225 2279535747956946139033669)
                      ·
                        rfl

theorem cell23_4439380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_4439380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439380 prefixEnd_4439380 := by exact prefixLift 4439380
  have htrace : WordTrace (prefixWord ++ tailWord_4439380) baseStart_4439380 baseEnd_4439380 := by
    simpa [prefixWord, tailWord_4439380, baseEnd_4439380] using wordTrace_append hprefix tailTrace_4439380
  have hstable : (prefixWord ++ tailWord_4439380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439380).length < 2 ^ (prefixWord ++ tailWord_4439380).sum := by decide
  have hdescent : baseEnd_4439380 < baseStart_4439380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439383 : List Nat := [1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 5]
def baseStart_4439383 : Nat := 118140960795 + 4439383 * 2 ^ 59
def prefixEnd_4439383 : Nat := 4983230072969 + 3 ^ 40 * 4439383 * 2
def baseEnd_4439383 : Nat := 2279537288398909627296155

theorem tailTrace_4439383 : CollatzResearch.WordTrace tailWord_4439383 prefixEnd_4439383 2279537288398909627296155 := by
  unfold tailWord_4439383
  simp only [CollatzResearch.WordTrace]
  refine ⟨161917600075881052099218803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107945066717254034732812535 161917600075881052099218803)
  ·
    refine ⟨242876400113821578148828205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161917600075881052099218803 242876400113821578148828205)
    ·
      refine ⟨91078650042683091805810577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 242876400113821578148828205 91078650042683091805810577)
      ·
        refine ⟨68308987532012318854357933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91078650042683091805810577 68308987532012318854357933)
        ·
          refine ⟨25615870324504619570384225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68308987532012318854357933 25615870324504619570384225)
          ·
            refine ⟨19211902743378464677788169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25615870324504619570384225 19211902743378464677788169)
            ·
              refine ⟨14408927057533848508341127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19211902743378464677788169 14408927057533848508341127)
              ·
                refine ⟨21613390586300772762511691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14408927057533848508341127 21613390586300772762511691)
                ·
                  refine ⟨32420085879451159143767537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21613390586300772762511691 32420085879451159143767537)
                  ·
                    refine ⟨24315064409588369357825653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32420085879451159143767537 24315064409588369357825653)
                    ·
                      refine ⟨2279537288398909627296155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24315064409588369357825653 2279537288398909627296155)
                      ·
                        rfl

theorem cell23_4439383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_4439383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439383 prefixEnd_4439383 := by exact prefixLift 4439383
  have htrace : WordTrace (prefixWord ++ tailWord_4439383) baseStart_4439383 baseEnd_4439383 := by
    simpa [prefixWord, tailWord_4439383, baseEnd_4439383] using wordTrace_append hprefix tailTrace_4439383
  have hstable : (prefixWord ++ tailWord_4439383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439383).length < 2 ^ (prefixWord ++ tailWord_4439383).sum := by decide
  have hdescent : baseEnd_4439383 < baseStart_4439383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439393 : List Nat := [1, 2, 3, 1, 1, 1, 1, 4, 4, 1, 4]
def baseStart_4439393 : Nat := 118140960795 + 4439393 * 2 ^ 59
def prefixEnd_4439393 : Nat := 4983230072969 + 3 ^ 40 * 4439393 * 2
def baseEnd_4439393 : Nat := 2279542423205454588171109

theorem tailTrace_4439393 : CollatzResearch.WordTrace tailWord_4439393 prefixEnd_4439393 2279542423205454588171109 := by
  unfold tailWord_4439393
  simp only [CollatzResearch.WordTrace]
  refine ⟨161917964805844823807082833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107945309870563215871388555 161917964805844823807082833)
  ·
    refine ⟨121438473604383617855312125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161917964805844823807082833 121438473604383617855312125)
    ·
      refine ⟨45539427601643856695742047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121438473604383617855312125 45539427601643856695742047)
      ·
        refine ⟨68309141402465785043613071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45539427601643856695742047 68309141402465785043613071)
        ·
          refine ⟨102463712103698677565419607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68309141402465785043613071 102463712103698677565419607)
          ·
            refine ⟨153695568155548016348129411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102463712103698677565419607 153695568155548016348129411)
            ·
              refine ⟨230543352233322024522194117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153695568155548016348129411 230543352233322024522194117)
              ·
                refine ⟨43226878543747879597911397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 230543352233322024522194117 43226878543747879597911397)
                ·
                  refine ⟨8105039726952727424608387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43226878543747879597911397 8105039726952727424608387)
                  ·
                    refine ⟨12157559590429091136912581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8105039726952727424608387 12157559590429091136912581)
                    ·
                      refine ⟨2279542423205454588171109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12157559590429091136912581 2279542423205454588171109)
                      ·
                        rfl

theorem cell23_4439393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_4439393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439393 prefixEnd_4439393 := by exact prefixLift 4439393
  have htrace : WordTrace (prefixWord ++ tailWord_4439393) baseStart_4439393 baseEnd_4439393 := by
    simpa [prefixWord, tailWord_4439393, baseEnd_4439393] using wordTrace_append hprefix tailTrace_4439393
  have hstable : (prefixWord ++ tailWord_4439393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439393).length < 2 ^ (prefixWord ++ tailWord_4439393).sum := by decide
  have hdescent : baseEnd_4439393 < baseStart_4439393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439410 : List Nat := [3, 2, 1, 2, 1, 2, 1, 2, 1, 6, 2]
def baseStart_4439410 : Nat := 118140960795 + 4439410 * 2 ^ 59
def prefixEnd_4439410 : Nat := 4983230072969 + 3 ^ 40 * 4439410 * 2
def baseEnd_4439410 : Nat := 2279551152376581021658531

theorem tailTrace_4439410 : CollatzResearch.WordTrace tailWord_4439410 prefixEnd_4439410 2279551152376581021658531 := by
  unfold tailWord_4439410
  simp only [CollatzResearch.WordTrace]
  refine ⟨40479646211695808927612921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107945723231188823806967789 40479646211695808927612921)
  ·
    refine ⟨30359734658771856695709691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40479646211695808927612921 30359734658771856695709691)
    ·
      refine ⟨45539601988157785043564537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30359734658771856695709691 45539601988157785043564537)
      ·
        refine ⟨34154701491118338782673403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45539601988157785043564537 34154701491118338782673403)
        ·
          refine ⟨51232052236677508174010105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34154701491118338782673403 51232052236677508174010105)
          ·
            refine ⟨38424039177508131130507579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51232052236677508174010105 38424039177508131130507579)
            ·
              refine ⟨57636058766262196695761369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38424039177508131130507579 57636058766262196695761369)
              ·
                refine ⟨43227044074696647521821027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57636058766262196695761369 43227044074696647521821027)
                ·
                  refine ⟨64840566112044971282731541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43227044074696647521821027 64840566112044971282731541)
                  ·
                    refine ⟨3039401536502108028878041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 64840566112044971282731541 3039401536502108028878041)
                    ·
                      refine ⟨2279551152376581021658531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3039401536502108028878041 2279551152376581021658531)
                      ·
                        rfl

theorem cell23_4439410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_4439410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439410 prefixEnd_4439410 := by exact prefixLift 4439410
  have htrace : WordTrace (prefixWord ++ tailWord_4439410) baseStart_4439410 baseEnd_4439410 := by
    simpa [prefixWord, tailWord_4439410, baseEnd_4439410] using wordTrace_append hprefix tailTrace_4439410
  have hstable : (prefixWord ++ tailWord_4439410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439410).length < 2 ^ (prefixWord ++ tailWord_4439410).sum := by decide
  have hdescent : baseEnd_4439410 < baseStart_4439410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439480 : List Nat := [2, 1, 2, 1, 2, 2, 4, 3, 1, 5]
def baseStart_4439480 : Nat := 118140960795 + 4439480 * 2 ^ 59
def prefixEnd_4439480 : Nat := 4983230072969 + 3 ^ 40 * 4439480 * 2
def baseEnd_4439480 : Nat := 759862365340798582594403

theorem tailTrace_4439480 : CollatzResearch.WordTrace tailWord_4439480 prefixEnd_4439480 759862365340798582594403 := by
  unfold tailWord_4439480
  simp only [CollatzResearch.WordTrace]
  refine ⟨80960568978264818832749947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107947425304353091776999929 80960568978264818832749947)
  ·
    refine ⟨121440853467397228249124921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80960568978264818832749947 121440853467397228249124921)
    ·
      refine ⟨91080640100547921186843691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121440853467397228249124921 91080640100547921186843691)
      ·
        refine ⟨136620960150821881780265537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91080640100547921186843691 136620960150821881780265537)
        ·
          refine ⟨102465720113116411335199153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136620960150821881780265537 102465720113116411335199153)
          ·
            refine ⟨76849290084837308501399365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102465720113116411335199153 76849290084837308501399365)
            ·
              refine ⟨14409241890906995344012381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76849290084837308501399365 14409241890906995344012381)
              ·
                refine ⟨5403465709090123254004643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14409241890906995344012381 5403465709090123254004643)
                ·
                  refine ⟨8105198563635184881006965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5403465709090123254004643 8105198563635184881006965)
                  ·
                    refine ⟨759862365340798582594403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8105198563635184881006965 759862365340798582594403)
                    ·
                      rfl

theorem cell23_4439480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 1, 5].length) (baseStart_4439480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439480 prefixEnd_4439480 := by exact prefixLift 4439480
  have htrace : WordTrace (prefixWord ++ tailWord_4439480) baseStart_4439480 baseEnd_4439480 := by
    simpa [prefixWord, tailWord_4439480, baseEnd_4439480] using wordTrace_append hprefix tailTrace_4439480
  have hstable : (prefixWord ++ tailWord_4439480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439480).length < 2 ^ (prefixWord ++ tailWord_4439480).sum := by decide
  have hdescent : baseEnd_4439480 < baseStart_4439480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439517 : List Nat := [1, 4, 3, 1, 1, 3, 1, 1, 3, 1, 4]
def baseStart_4439517 : Nat := 118140960795 + 4439517 * 2 ^ 59
def prefixEnd_4439517 : Nat := 4983230072969 + 3 ^ 40 * 4439517 * 2
def baseEnd_4439517 : Nat := 2279606094806612103020539

theorem tailTrace_4439517 : CollatzResearch.WordTrace tailWord_4439517 prefixEnd_4439517 2279606094806612103020539 := by
  unfold tailWord_4439517
  simp only [CollatzResearch.WordTrace]
  refine ⟨161922487457395592984596805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107948324971597061989731203 161922487457395592984596805)
  ·
    refine ⟨30360466398261673684611901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161922487457395592984596805 30360466398261673684611901)
    ·
      refine ⟨11385174899348127631729463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30360466398261673684611901 11385174899348127631729463)
      ·
        refine ⟨17077762349022191447594195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11385174899348127631729463 17077762349022191447594195)
        ·
          refine ⟨25616643523533287171391293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17077762349022191447594195 25616643523533287171391293)
          ·
            refine ⟨9606241321324982689271735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25616643523533287171391293 9606241321324982689271735)
            ·
              refine ⟨14409361981987474033907603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9606241321324982689271735 14409361981987474033907603)
              ·
                refine ⟨21614042972981211050861405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14409361981987474033907603 21614042972981211050861405)
                ·
                  refine ⟨8105266114867954144073027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21614042972981211050861405 8105266114867954144073027)
                  ·
                    refine ⟨12157899172301931216109541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8105266114867954144073027 12157899172301931216109541)
                    ·
                      refine ⟨2279606094806612103020539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12157899172301931216109541 2279606094806612103020539)
                      ·
                        rfl

theorem cell23_4439517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_4439517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439517 prefixEnd_4439517 := by exact prefixLift 4439517
  have htrace : WordTrace (prefixWord ++ tailWord_4439517) baseStart_4439517 baseEnd_4439517 := by
    simpa [prefixWord, tailWord_4439517, baseEnd_4439517] using wordTrace_append hprefix tailTrace_4439517
  have hstable : (prefixWord ++ tailWord_4439517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439517).length < 2 ^ (prefixWord ++ tailWord_4439517).sum := by decide
  have hdescent : baseEnd_4439517 < baseStart_4439517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439534 : List Nat := [4, 1, 2, 1, 2, 1, 5, 1, 1, 1, 4]
def baseStart_4439534 : Nat := 118140960795 + 4439534 * 2 ^ 59
def prefixEnd_4439534 : Nat := 4983230072969 + 3 ^ 40 * 4439534 * 2
def baseEnd_4439534 : Nat := 2279614823977738536507961

theorem tailTrace_4439534 : CollatzResearch.WordTrace tailWord_4439534 prefixEnd_4439534 2279614823977738536507961 := by
  unfold tailWord_4439534
  simp only [CollatzResearch.WordTrace]
  refine ⟨20240388437291750610995707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107948738332222669925310437 20240388437291750610995707)
  ·
    refine ⟨30360582655937625916493561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20240388437291750610995707 30360582655937625916493561)
    ·
      refine ⟨22770436991953219437370171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30360582655937625916493561 22770436991953219437370171)
      ·
        refine ⟨34155655487929829156055257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22770436991953219437370171 34155655487929829156055257)
        ·
          refine ⟨25616741615947371867041443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34155655487929829156055257 25616741615947371867041443)
          ·
            refine ⟨38425112423921057800562165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25616741615947371867041443 38425112423921057800562165)
            ·
              refine ⟨3602354289742599168802703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38425112423921057800562165 3602354289742599168802703)
              ·
                refine ⟨5403531434613898753204055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3602354289742599168802703 5403531434613898753204055)
                ·
                  refine ⟨8105297151920848129806083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5403531434613898753204055 8105297151920848129806083)
                  ·
                    refine ⟨12157945727881272194709125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8105297151920848129806083 12157945727881272194709125)
                    ·
                      refine ⟨2279614823977738536507961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12157945727881272194709125 2279614823977738536507961)
                      ·
                        rfl

theorem cell23_4439534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_4439534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439534 prefixEnd_4439534 := by exact prefixLift 4439534
  have htrace : WordTrace (prefixWord ++ tailWord_4439534) baseStart_4439534 baseEnd_4439534 := by
    simpa [prefixWord, tailWord_4439534, baseEnd_4439534] using wordTrace_append hprefix tailTrace_4439534
  have hstable : (prefixWord ++ tailWord_4439534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439534).length < 2 ^ (prefixWord ++ tailWord_4439534).sum := by decide
  have hdescent : baseEnd_4439534 < baseStart_4439534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439537 : List Nat := [1, 2, 2, 2, 3, 4, 1, 1, 1, 1, 5]
def baseStart_4439537 : Nat := 118140960795 + 4439537 * 2 ^ 59
def prefixEnd_4439537 : Nat := 4983230072969 + 3 ^ 40 * 4439537 * 2
def baseEnd_4439537 : Nat := 2279616364419702024770447

theorem tailTrace_4439537 : CollatzResearch.WordTrace tailWord_4439537 prefixEnd_4439537 2279616364419702024770447 := by
  unfold tailWord_4439537
  simp only [CollatzResearch.WordTrace]
  refine ⟨161923216917323136400324865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107948811278215424266883243 161923216917323136400324865)
  ·
    refine ⟨121442412687992352300243649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161923216917323136400324865 121442412687992352300243649)
    ·
      refine ⟨91081809515994264225182737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121442412687992352300243649 91081809515994264225182737)
      ·
        refine ⟨68311357136995698168887053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91081809515994264225182737 68311357136995698168887053)
        ·
          refine ⟨25616758926373386813332645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68311357136995698168887053 25616758926373386813332645)
          ·
            refine ⟨4803142298695010027499871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25616758926373386813332645 4803142298695010027499871)
            ·
              refine ⟨7204713448042515041249807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4803142298695010027499871 7204713448042515041249807)
              ·
                refine ⟨10807070172063772561874711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7204713448042515041249807 10807070172063772561874711)
                ·
                  refine ⟨16210605258095658842812067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10807070172063772561874711 16210605258095658842812067)
                  ·
                    refine ⟨24315907887143488264218101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16210605258095658842812067 24315907887143488264218101)
                    ·
                      refine ⟨2279616364419702024770447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24315907887143488264218101 2279616364419702024770447)
                      ·
                        rfl

theorem cell23_4439537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 1, 5].length) (baseStart_4439537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439537 prefixEnd_4439537 := by exact prefixLift 4439537
  have htrace : WordTrace (prefixWord ++ tailWord_4439537) baseStart_4439537 baseEnd_4439537 := by
    simpa [prefixWord, tailWord_4439537, baseEnd_4439537] using wordTrace_append hprefix tailTrace_4439537
  have hstable : (prefixWord ++ tailWord_4439537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439537).length < 2 ^ (prefixWord ++ tailWord_4439537).sum := by decide
  have hdescent : baseEnd_4439537 < baseStart_4439537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439543 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 6]
def baseStart_4439543 : Nat := 118140960795 + 4439543 * 2 ^ 59
def prefixEnd_4439543 : Nat := 4983230072969 + 3 ^ 40 * 4439543 * 2
def baseEnd_4439543 : Nat := 2279619445303629001295419

theorem tailTrace_4439543 : CollatzResearch.WordTrace tailWord_4439543 prefixEnd_4439543 2279619445303629001295419 := by
  unfold tailWord_4439543
  simp only [CollatzResearch.WordTrace]
  refine ⟨161923435755301399425043283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107948957170200932950028855 161923435755301399425043283)
  ·
    refine ⟨242885153632952099137564925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161923435755301399425043283 242885153632952099137564925)
    ·
      refine ⟨91081932612357037176586847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 242885153632952099137564925 91081932612357037176586847)
      ·
        refine ⟨136622898918535555764880271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91081932612357037176586847 136622898918535555764880271)
        ·
          refine ⟨204934348377803333647320407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136622898918535555764880271 204934348377803333647320407)
          ·
            refine ⟨307401522566705000470980611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204934348377803333647320407 307401522566705000470980611)
            ·
              refine ⟨461102283850057500706470917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307401522566705000470980611 461102283850057500706470917)
              ·
                refine ⟨86456678221885781382463297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 461102283850057500706470917 86456678221885781382463297)
                ·
                  refine ⟨64842508666414336036847473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86456678221885781382463297 64842508666414336036847473)
                  ·
                    refine ⟨48631881499810752027635605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64842508666414336036847473 48631881499810752027635605)
                    ·
                      refine ⟨2279619445303629001295419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48631881499810752027635605 2279619445303629001295419)
                      ·
                        rfl

theorem cell23_4439543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_4439543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439543 prefixEnd_4439543 := by exact prefixLift 4439543
  have htrace : WordTrace (prefixWord ++ tailWord_4439543) baseStart_4439543 baseEnd_4439543 := by
    simpa [prefixWord, tailWord_4439543, baseEnd_4439543] using wordTrace_append hprefix tailTrace_4439543
  have hstable : (prefixWord ++ tailWord_4439543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439543).length < 2 ^ (prefixWord ++ tailWord_4439543).sum := by decide
  have hdescent : baseEnd_4439543 < baseStart_4439543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439554 : List Nat := [3, 4, 1, 2, 1, 1, 1, 2, 3, 2, 3]
def baseStart_4439554 : Nat := 118140960795 + 4439554 * 2 ^ 59
def prefixEnd_4439554 : Nat := 4983230072969 + 3 ^ 40 * 4439554 * 2
def baseEnd_4439554 : Nat := 2279625093590828458257869

theorem tailTrace_4439554 : CollatzResearch.WordTrace tailWord_4439554 prefixEnd_4439554 2279625093590828458257869 := by
  unfold tailWord_4439554
  simp only [CollatzResearch.WordTrace]
  refine ⟨40480959239565387075923429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107949224638841032202462477 40480959239565387075923429)
  ·
    refine ⟨7590179857418510076735643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40480959239565387075923429 7590179857418510076735643)
    ·
      refine ⟨11385269786127765115103465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7590179857418510076735643 11385269786127765115103465)
      ·
        refine ⟨8538952339595823836327599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11385269786127765115103465 8538952339595823836327599)
        ·
          refine ⟨12808428509393735754491399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8538952339595823836327599 12808428509393735754491399)
          ·
            refine ⟨19212642764090603631737099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12808428509393735754491399 19212642764090603631737099)
            ·
              refine ⟨28818964146135905447605649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19212642764090603631737099 28818964146135905447605649)
              ·
                refine ⟨21614223109601929085704237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28818964146135905447605649 21614223109601929085704237)
                ·
                  refine ⟨8105333666100723407139089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21614223109601929085704237 8105333666100723407139089)
                  ·
                    refine ⟨6079000249575542555354317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8105333666100723407139089 6079000249575542555354317)
                    ·
                      refine ⟨2279625093590828458257869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6079000249575542555354317 2279625093590828458257869)
                      ·
                        rfl

theorem cell23_4439554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_4439554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439554 prefixEnd_4439554 := by exact prefixLift 4439554
  have htrace : WordTrace (prefixWord ++ tailWord_4439554) baseStart_4439554 baseEnd_4439554 := by
    simpa [prefixWord, tailWord_4439554, baseEnd_4439554] using wordTrace_append hprefix tailTrace_4439554
  have hstable : (prefixWord ++ tailWord_4439554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439554).length < 2 ^ (prefixWord ++ tailWord_4439554).sum := by decide
  have hdescent : baseEnd_4439554 < baseStart_4439554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439580 : List Nat := [2, 2, 3, 1, 2, 1, 2, 1, 2, 2, 5]
def baseStart_4439580 : Nat := 118140960795 + 4439580 * 2 ^ 59
def prefixEnd_4439580 : Nat := 4983230072969 + 3 ^ 40 * 4439580 * 2
def baseEnd_4439580 : Nat := 2279638444087845356532749

theorem tailTrace_4439580 : CollatzResearch.WordTrace tailWord_4439580 prefixEnd_4439580 2279638444087845356532749 := by
  unfold tailWord_4439580
  simp only [CollatzResearch.WordTrace]
  refine ⟨80962392628083677372070097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107949856837444903162760129 80962392628083677372070097)
  ·
    refine ⟨60721794471062758029052573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80962392628083677372070097 60721794471062758029052573)
    ·
      refine ⟨22770672926648534260894715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60721794471062758029052573 22770672926648534260894715)
      ·
        refine ⟨34156009389972801391342073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22770672926648534260894715 34156009389972801391342073)
        ·
          refine ⟨25617007042479601043506555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34156009389972801391342073 25617007042479601043506555)
          ·
            refine ⟨38425510563719401565259833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25617007042479601043506555 38425510563719401565259833)
            ·
              refine ⟨28819132922789551173944875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38425510563719401565259833 28819132922789551173944875)
              ·
                refine ⟨43228699384184326760917313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28819132922789551173944875 43228699384184326760917313)
                ·
                  refine ⟨32421524538138245070687985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43228699384184326760917313 32421524538138245070687985)
                  ·
                    refine ⟨24316143403603683803015989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32421524538138245070687985 24316143403603683803015989)
                    ·
                      refine ⟨2279638444087845356532749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24316143403603683803015989 2279638444087845356532749)
                      ·
                        rfl

theorem cell23_4439580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_4439580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439580 prefixEnd_4439580 := by exact prefixLift 4439580
  have htrace : WordTrace (prefixWord ++ tailWord_4439580) baseStart_4439580 baseEnd_4439580 := by
    simpa [prefixWord, tailWord_4439580, baseEnd_4439580] using wordTrace_append hprefix tailTrace_4439580
  have hstable : (prefixWord ++ tailWord_4439580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439580).length < 2 ^ (prefixWord ++ tailWord_4439580).sum := by decide
  have hdescent : baseEnd_4439580 < baseStart_4439580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439582 : List Nat := [4, 3, 3, 1, 2, 1, 2, 1, 1, 5]
def baseStart_4439582 : Nat := 118140960795 + 4439582 * 2 ^ 59
def prefixEnd_4439582 : Nat := 4983230072969 + 3 ^ 40 * 4439582 * 2
def baseEnd_4439582 : Nat := 759879823683051449569247

theorem tailTrace_4439582 : CollatzResearch.WordTrace tailWord_4439582 prefixEnd_4439582 759879823683051449569247 := by
  unfold tailWord_4439582
  simp only [CollatzResearch.WordTrace]
  refine ⟨20240607275270013635714125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107949905468106739390475333 20240607275270013635714125)
  ·
    refine ⟨7590227728226255113392797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20240607275270013635714125 7590227728226255113392797)
    ·
      refine ⟨2846335398084845667522299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7590227728226255113392797 2846335398084845667522299)
      ·
        refine ⟨4269503097127268501283449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2846335398084845667522299 4269503097127268501283449)
        ·
          refine ⟨3202127322845451375962587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4269503097127268501283449 3202127322845451375962587)
          ·
            refine ⟨4803190984268177063943881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3202127322845451375962587 4803190984268177063943881)
            ·
              refine ⟨3602393238201132797957911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4803190984268177063943881 3602393238201132797957911)
              ·
                refine ⟨5403589857301699196936867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3602393238201132797957911 5403589857301699196936867)
                ·
                  refine ⟨8105384785952548795405301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5403589857301699196936867 8105384785952548795405301)
                  ·
                    refine ⟨759879823683051449569247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8105384785952548795405301 759879823683051449569247)
                    ·
                      rfl

theorem cell23_4439582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_4439582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439582 prefixEnd_4439582 := by exact prefixLift 4439582
  have htrace : WordTrace (prefixWord ++ tailWord_4439582) baseStart_4439582 baseEnd_4439582 := by
    simpa [prefixWord, tailWord_4439582, baseEnd_4439582] using wordTrace_append hprefix tailTrace_4439582
  have hstable : (prefixWord ++ tailWord_4439582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439582).length < 2 ^ (prefixWord ++ tailWord_4439582).sum := by decide
  have hdescent : baseEnd_4439582 < baseStart_4439582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439694 : List Nat := [4, 1, 1, 3, 1, 3, 2, 1, 2, 5]
def baseStart_4439694 : Nat := 118140960795 + 4439694 * 2 ^ 59
def prefixEnd_4439694 : Nat := 4983230072969 + 3 ^ 40 * 4439694 * 2
def baseEnd_4439694 : Nat := 759898993627485970169075

theorem tailTrace_4439694 : CollatzResearch.WordTrace tailWord_4439694 prefixEnd_4439694 759898993627485970169075 := by
  unfold tailWord_4439694
  simp only [CollatzResearch.WordTrace]
  refine ⟨20241117897219294026723767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107952628785169568142526757 20241117897219294026723767)
  ·
    refine ⟨30361676845828941040085651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20241117897219294026723767 30361676845828941040085651)
    ·
      refine ⟨45542515268743411560128477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30361676845828941040085651 45542515268743411560128477)
      ·
        refine ⟨17078443225778779335048179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45542515268743411560128477 17078443225778779335048179)
        ·
          refine ⟨25617664838668169002572269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17078443225778779335048179 25617664838668169002572269)
          ·
            refine ⟨9606624314500563375964601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25617664838668169002572269 9606624314500563375964601)
            ·
              refine ⟨7204968235875422531973451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9606624314500563375964601 7204968235875422531973451)
              ·
                refine ⟨10807452353813133797960177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7204968235875422531973451 10807452353813133797960177)
                ·
                  refine ⟨8105589265359850348470133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10807452353813133797960177 8105589265359850348470133)
                  ·
                    refine ⟨759898993627485970169075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8105589265359850348470133 759898993627485970169075)
                    ·
                      rfl

theorem cell23_4439694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_4439694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439694 prefixEnd_4439694 := by exact prefixLift 4439694
  have htrace : WordTrace (prefixWord ++ tailWord_4439694) baseStart_4439694 baseEnd_4439694 := by
    simpa [prefixWord, tailWord_4439694, baseEnd_4439694] using wordTrace_append hprefix tailTrace_4439694
  have hstable : (prefixWord ++ tailWord_4439694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439694).length < 2 ^ (prefixWord ++ tailWord_4439694).sum := by decide
  have hdescent : baseEnd_4439694 < baseStart_4439694 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439697 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 3, 6, 2]
def baseStart_4439697 : Nat := 118140960795 + 4439697 * 2 ^ 59
def prefixEnd_4439697 : Nat := 4983230072969 + 3 ^ 40 * 4439697 * 2
def baseEnd_4439697 : Nat := 2279698521324421398769711

theorem tailTrace_4439697 : CollatzResearch.WordTrace tailWord_4439697 prefixEnd_4439697 2279698521324421398769711 := by
  unfold tailWord_4439697
  simp only [CollatzResearch.WordTrace]
  refine ⟨161929052596743483726149345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107952701731162322484099563 161929052596743483726149345)
  ·
    refine ⟨121446789447557612794612009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161929052596743483726149345 121446789447557612794612009)
    ·
      refine ⟨91085092085668209595959007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121446789447557612794612009 91085092085668209595959007)
      ·
        refine ⟨136627638128502314393938511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91085092085668209595959007 136627638128502314393938511)
        ·
          refine ⟨204941457192753471590907767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136627638128502314393938511 204941457192753471590907767)
          ·
            refine ⟨307412185789130207386361651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204941457192753471590907767 307412185789130207386361651)
            ·
              refine ⟨461118278683695311079542477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307412185789130207386361651 461118278683695311079542477)
              ·
                refine ⟨172919354506385741654828429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 461118278683695311079542477 172919354506385741654828429)
                ·
                  refine ⟨64844757939894653120560661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 172919354506385741654828429 64844757939894653120560661)
                  ·
                    refine ⟨3039598028432561865026281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 64844757939894653120560661 3039598028432561865026281)
                    ·
                      refine ⟨2279698521324421398769711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3039598028432561865026281 2279698521324421398769711)
                      ·
                        rfl

theorem cell23_4439697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 6, 2].length) (baseStart_4439697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439697 prefixEnd_4439697 := by exact prefixLift 4439697
  have htrace : WordTrace (prefixWord ++ tailWord_4439697) baseStart_4439697 baseEnd_4439697 := by
    simpa [prefixWord, tailWord_4439697, baseEnd_4439697] using wordTrace_append hprefix tailTrace_4439697
  have hstable : (prefixWord ++ tailWord_4439697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439697).length < 2 ^ (prefixWord ++ tailWord_4439697).sum := by decide
  have hdescent : baseEnd_4439697 < baseStart_4439697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439737 : List Nat := [1, 2, 1, 4, 1, 1, 4, 3, 6]
def baseStart_4439737 : Nat := 118140960795 + 4439737 * 2 ^ 59
def prefixEnd_4439737 : Nat := 4983230072969 + 3 ^ 40 * 4439737 * 2
def baseEnd_4439737 : Nat := 253302117838955693585503

theorem tailTrace_4439737 : CollatzResearch.WordTrace tailWord_4439737 prefixEnd_4439737 253302117838955693585503 := by
  unfold tailWord_4439737
  simp only [CollatzResearch.WordTrace]
  refine ⟨161930511516598570557605465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107953674344399047038403643 161930511516598570557605465)
  ·
    refine ⟨121447883637448927918204099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161930511516598570557605465 121447883637448927918204099)
    ·
      refine ⟨182171825456173391877306149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121447883637448927918204099 182171825456173391877306149)
      ·
        refine ⟨34157217273032510976994903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 182171825456173391877306149 34157217273032510976994903)
        ·
          refine ⟨51235825909548766465492355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34157217273032510976994903 51235825909548766465492355)
          ·
            refine ⟨76853738864323149698238533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51235825909548766465492355 76853738864323149698238533)
            ·
              refine ⟨14410076037060590568419725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76853738864323149698238533 14410076037060590568419725)
              ·
                refine ⟨5403778513897721463157397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14410076037060590568419725 5403778513897721463157397)
                ·
                  refine ⟨253302117838955693585503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5403778513897721463157397 253302117838955693585503)
                  ·
                    rfl

theorem cell23_4439737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 6].length) (baseStart_4439737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439737 prefixEnd_4439737 := by exact prefixLift 4439737
  have htrace : WordTrace (prefixWord ++ tailWord_4439737) baseStart_4439737 baseEnd_4439737 := by
    simpa [prefixWord, tailWord_4439737, baseEnd_4439737] using wordTrace_append hprefix tailTrace_4439737
  have hstable : (prefixWord ++ tailWord_4439737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439737).length < 2 ^ (prefixWord ++ tailWord_4439737).sum := by decide
  have hdescent : baseEnd_4439737 < baseStart_4439737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439781 : List Nat := [1, 3, 1, 4, 1, 1, 4, 1, 3, 1, 3]
def baseStart_4439781 : Nat := 118140960795 + 4439781 * 2 ^ 59
def prefixEnd_4439781 : Nat := 4983230072969 + 3 ^ 40 * 4439781 * 2
def baseEnd_4439781 : Nat := 2279741653699399070119325

theorem tailTrace_4439781 : CollatzResearch.WordTrace tailWord_4439781 prefixEnd_4439781 2279741653699399070119325 := by
  unfold tailWord_4439781
  simp only [CollatzResearch.WordTrace]
  refine ⟨161932116328439166072207197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107954744218959444048138131 161932116328439166072207197)
  ·
    refine ⟨60724543623164687277077699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161932116328439166072207197 60724543623164687277077699)
    ·
      refine ⟨91086815434747030915616549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60724543623164687277077699 91086815434747030915616549)
      ·
        refine ⟨17078777894015068296678103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91086815434747030915616549 17078777894015068296678103)
        ·
          refine ⟨25618166841022602445017155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17078777894015068296678103 25618166841022602445017155)
          ·
            refine ⟨38427250261533903667525733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25618166841022602445017155 38427250261533903667525733)
            ·
              refine ⟨7205109424037606937661075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38427250261533903667525733 7205109424037606937661075)
              ·
                refine ⟨10807664136056410406491613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7205109424037606937661075 10807664136056410406491613)
                ·
                  refine ⟨4052874051021153902434355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10807664136056410406491613 4052874051021153902434355)
                  ·
                    refine ⟨6079311076531730853651533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4052874051021153902434355 6079311076531730853651533)
                    ·
                      refine ⟨2279741653699399070119325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6079311076531730853651533 2279741653699399070119325)
                      ·
                        rfl

theorem cell23_4439781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_4439781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439781 prefixEnd_4439781 := by exact prefixLift 4439781
  have htrace : WordTrace (prefixWord ++ tailWord_4439781) baseStart_4439781 baseEnd_4439781 := by
    simpa [prefixWord, tailWord_4439781, baseEnd_4439781] using wordTrace_append hprefix tailTrace_4439781
  have hstable : (prefixWord ++ tailWord_4439781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439781).length < 2 ^ (prefixWord ++ tailWord_4439781).sum := by decide
  have hdescent : baseEnd_4439781 < baseStart_4439781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439787 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 4]
def baseStart_4439787 : Nat := 118140960795 + 4439787 * 2 ^ 59
def prefixEnd_4439787 : Nat := 4983230072969 + 3 ^ 40 * 4439787 * 2
def baseEnd_4439787 : Nat := 2279744734583326046644297

theorem tailTrace_4439787 : CollatzResearch.WordTrace tailWord_4439787 prefixEnd_4439787 2279744734583326046644297 := by
  unfold tailWord_4439787
  simp only [CollatzResearch.WordTrace]
  refine ⟨161932335166417429096925615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107954890110944952731283743 161932335166417429096925615)
  ·
    refine ⟨242898502749626143645388423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161932335166417429096925615 242898502749626143645388423)
    ·
      refine ⟨364347754124439215468082635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242898502749626143645388423 364347754124439215468082635)
      ·
        refine ⟨546521631186658823202123953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 364347754124439215468082635 546521631186658823202123953)
        ·
          refine ⟨409891223389994117401592965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 546521631186658823202123953 409891223389994117401592965)
          ·
            refine ⟨76854604385623897012798681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 409891223389994117401592965 76854604385623897012798681)
            ·
              refine ⟨57640953289217922759599011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76854604385623897012798681 57640953289217922759599011)
              ·
                refine ⟨86461429933826884139398517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57640953289217922759599011 86461429933826884139398517)
                ·
                  refine ⟨8105759056296270388068611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 86461429933826884139398517 8105759056296270388068611)
                  ·
                    refine ⟨12158638584444405582102917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8105759056296270388068611 12158638584444405582102917)
                    ·
                      refine ⟨2279744734583326046644297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12158638584444405582102917 2279744734583326046644297)
                      ·
                        rfl

theorem cell23_4439787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 4].length) (baseStart_4439787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439787 prefixEnd_4439787 := by exact prefixLift 4439787
  have htrace : WordTrace (prefixWord ++ tailWord_4439787) baseStart_4439787 baseEnd_4439787 := by
    simpa [prefixWord, tailWord_4439787, baseEnd_4439787] using wordTrace_append hprefix tailTrace_4439787
  have hstable : (prefixWord ++ tailWord_4439787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439787).length < 2 ^ (prefixWord ++ tailWord_4439787).sum := by decide
  have hdescent : baseEnd_4439787 < baseStart_4439787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439804 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 2, 6, 2]
def baseStart_4439804 : Nat := 118140960795 + 4439804 * 2 ^ 59
def prefixEnd_4439804 : Nat := 4983230072969 + 3 ^ 40 * 4439804 * 2
def baseEnd_4439804 : Nat := 2279753463754452480131719

theorem tailTrace_4439804 : CollatzResearch.WordTrace tailWord_4439804 prefixEnd_4439804 2279753463754452480131719 := by
  unfold tailWord_4439804
  simp only [CollatzResearch.WordTrace]
  refine ⟨80966477603677920500147233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107955303471570560666862977 80966477603677920500147233)
  ·
    refine ⟨60724858202758440375110425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80966477603677920500147233 60724858202758440375110425)
    ·
      refine ⟨45543643652068830281332819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60724858202758440375110425 45543643652068830281332819)
      ·
        refine ⟨68315465478103245421999229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45543643652068830281332819 68315465478103245421999229)
        ·
          refine ⟨25618299554288717033249711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68315465478103245421999229 25618299554288717033249711)
          ·
            refine ⟨38427449331433075549874567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25618299554288717033249711 38427449331433075549874567)
            ·
              refine ⟨57641173997149613324811851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38427449331433075549874567 57641173997149613324811851)
              ·
                refine ⟨86461760995724419987217777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57641173997149613324811851 86461760995724419987217777)
                ·
                  refine ⟨64846320746793314990413333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86461760995724419987217777 64846320746793314990413333)
                  ·
                    refine ⟨3039671285005936640175625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 64846320746793314990413333 3039671285005936640175625)
                    ·
                      refine ⟨2279753463754452480131719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3039671285005936640175625 2279753463754452480131719)
                      ·
                        rfl

theorem cell23_4439804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 2, 6, 2].length) (baseStart_4439804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439804 prefixEnd_4439804 := by exact prefixLift 4439804
  have htrace : WordTrace (prefixWord ++ tailWord_4439804) baseStart_4439804 baseEnd_4439804 := by
    simpa [prefixWord, tailWord_4439804, baseEnd_4439804] using wordTrace_append hprefix tailTrace_4439804
  have hstable : (prefixWord ++ tailWord_4439804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439804).length < 2 ^ (prefixWord ++ tailWord_4439804).sum := by decide
  have hdescent : baseEnd_4439804 < baseStart_4439804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439817 : List Nat := [1, 2, 1, 1, 3, 2, 1, 3, 3, 2, 4]
def baseStart_4439817 : Nat := 118140960795 + 4439817 * 2 ^ 59
def prefixEnd_4439817 : Nat := 4983230072969 + 3 ^ 40 * 4439817 * 2
def baseEnd_4439817 : Nat := 2279760139002960929269159

theorem tailTrace_4439817 : CollatzResearch.WordTrace tailWord_4439817 prefixEnd_4439817 2279760139002960929269159 := by
  unfold tailWord_4439817
  simp only [CollatzResearch.WordTrace]
  refine ⟨161933429356308744220517705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107955619570872496147011803 161933429356308744220517705)
  ·
    refine ⟨121450072017231558165388279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161933429356308744220517705 121450072017231558165388279)
    ·
      refine ⟨182175108025847337248082419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121450072017231558165388279 182175108025847337248082419)
      ·
        refine ⟨273262662038771005872123629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182175108025847337248082419 273262662038771005872123629)
        ·
          refine ⟨102473498264539127202046361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 273262662038771005872123629 102473498264539127202046361)
          ·
            refine ⟨76855123698404345401534771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102473498264539127202046361 76855123698404345401534771)
            ·
              refine ⟨115282685547606518102302157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76855123698404345401534771 115282685547606518102302157)
              ·
                refine ⟨43231007080352444288363309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115282685547606518102302157 43231007080352444288363309)
                ·
                  refine ⟨16211627655132166608136241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43231007080352444288363309 16211627655132166608136241)
                  ·
                    refine ⟨12158720741349124956102181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16211627655132166608136241 12158720741349124956102181)
                    ·
                      refine ⟨2279760139002960929269159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12158720741349124956102181 2279760139002960929269159)
                      ·
                        rfl

theorem cell23_4439817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 2, 4].length) (baseStart_4439817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439817 prefixEnd_4439817 := by exact prefixLift 4439817
  have htrace : WordTrace (prefixWord ++ tailWord_4439817) baseStart_4439817 baseEnd_4439817 := by
    simpa [prefixWord, tailWord_4439817, baseEnd_4439817] using wordTrace_append hprefix tailTrace_4439817
  have hstable : (prefixWord ++ tailWord_4439817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439817).length < 2 ^ (prefixWord ++ tailWord_4439817).sum := by decide
  have hdescent : baseEnd_4439817 < baseStart_4439817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439844 : List Nat := [2, 3, 1, 3, 2, 2, 2, 8]
def baseStart_4439844 : Nat := 118140960795 + 4439844 * 2 ^ 59
def prefixEnd_4439844 : Nat := 4983230072969 + 3 ^ 40 * 4439844 * 2
def baseEnd_4439844 : Nat := 84436074184467863838205

theorem tailTrace_4439844 : CollatzResearch.WordTrace tailWord_4439844 prefixEnd_4439844 84436074184467863838205 := by
  unfold tailWord_4439844
  simp only [CollatzResearch.WordTrace]
  refine ⟨80967207063605463915875293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107956276084807285221167057 80967207063605463915875293)
  ·
    refine ⟨30362702648852048968453235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80967207063605463915875293 30362702648852048968453235)
    ·
      refine ⟨45544053973278073452679853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30362702648852048968453235 45544053973278073452679853)
      ·
        refine ⟨17079020239979277544754945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45544053973278073452679853 17079020239979277544754945)
        ·
          refine ⟨12809265179984458158566209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17079020239979277544754945 12809265179984458158566209)
          ·
            refine ⟨9606948884988343618924657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12809265179984458158566209 9606948884988343618924657)
            ·
              refine ⟨7205211663741257714193493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9606948884988343618924657 7205211663741257714193493)
              ·
                refine ⟨84436074184467863838205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7205211663741257714193493 84436074184467863838205)
                ·
                  rfl

theorem cell23_4439844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 8].length) (baseStart_4439844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439844 prefixEnd_4439844 := by exact prefixLift 4439844
  have htrace : WordTrace (prefixWord ++ tailWord_4439844) baseStart_4439844 baseEnd_4439844 := by
    simpa [prefixWord, tailWord_4439844, baseEnd_4439844] using wordTrace_append hprefix tailTrace_4439844
  have hstable : (prefixWord ++ tailWord_4439844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439844).length < 2 ^ (prefixWord ++ tailWord_4439844).sum := by decide
  have hdescent : baseEnd_4439844 < baseStart_4439844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439848 : List Nat := [2, 1, 5, 1, 1, 2, 4, 1, 2, 4]
def baseStart_4439848 : Nat := 118140960795 + 4439848 * 2 ^ 59
def prefixEnd_4439848 : Nat := 4983230072969 + 3 ^ 40 * 4439848 * 2
def baseEnd_4439848 : Nat := 759925352301083435993839

theorem tailTrace_4439848 : CollatzResearch.WordTrace tailWord_4439848 prefixEnd_4439848 759925352301083435993839 := by
  unfold tailWord_4439848
  simp only [CollatzResearch.WordTrace]
  refine ⟨80967280009598218257448099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107956373346130957676597465 80967280009598218257448099)
  ·
    refine ⟨121450920014397327386172149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80967280009598218257448099 121450920014397327386172149)
    ·
      refine ⟨11386023751349749442453639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 121450920014397327386172149 11386023751349749442453639)
      ·
        refine ⟨17079035627024624163680459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11386023751349749442453639 17079035627024624163680459)
        ·
          refine ⟨25618553440536936245520689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17079035627024624163680459 25618553440536936245520689)
          ·
            refine ⟨19213915080402702184140517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25618553440536936245520689 19213915080402702184140517)
            ·
              refine ⟨3602609077575506659526347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19213915080402702184140517 3602609077575506659526347)
              ·
                refine ⟨5403913616363259989289521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3602609077575506659526347 5403913616363259989289521)
                ·
                  refine ⟨4052935212272444991967141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5403913616363259989289521 4052935212272444991967141)
                  ·
                    refine ⟨759925352301083435993839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4052935212272444991967141 759925352301083435993839)
                    ·
                      rfl

theorem cell23_4439848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_4439848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439848 prefixEnd_4439848 := by exact prefixLift 4439848
  have htrace : WordTrace (prefixWord ++ tailWord_4439848) baseStart_4439848 baseEnd_4439848 := by
    simpa [prefixWord, tailWord_4439848, baseEnd_4439848] using wordTrace_append hprefix tailTrace_4439848
  have hstable : (prefixWord ++ tailWord_4439848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439848).length < 2 ^ (prefixWord ++ tailWord_4439848).sum := by decide
  have hdescent : baseEnd_4439848 < baseStart_4439848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439858 : List Nat := [3, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3]
def baseStart_4439858 : Nat := 118140960795 + 4439858 * 2 ^ 59
def prefixEnd_4439858 : Nat := 4983230072969 + 3 ^ 40 * 4439858 * 2
def baseEnd_4439858 : Nat := 2279781191709795268856471

theorem tailTrace_4439858 : CollatzResearch.WordTrace tailWord_4439858 prefixEnd_4439858 2279781191709795268856471 := by
  unfold tailWord_4439858
  simp only [CollatzResearch.WordTrace]
  refine ⟨40483731187290052055690057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107956616499440138815173485 40483731187290052055690057)
  ·
    refine ⟨30362798390467539041767543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40483731187290052055690057 30362798390467539041767543)
    ·
      refine ⟨45544197585701308562651315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30362798390467539041767543 45544197585701308562651315)
      ·
        refine ⟨68316296378551962843976973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45544197585701308562651315 68316296378551962843976973)
        ·
          refine ⟨25618611141956986066491365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68316296378551962843976973 25618611141956986066491365)
          ·
            refine ⟨4803489589116934887467131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25618611141956986066491365 4803489589116934887467131)
            ·
              refine ⟨7205234383675402331200697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4803489589116934887467131 7205234383675402331200697)
              ·
                refine ⟨5403925787756551748400523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7205234383675402331200697 5403925787756551748400523)
                ·
                  refine ⟨8105888681634827622600785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5403925787756551748400523 8105888681634827622600785)
                  ·
                    refine ⟨6079416511226120716950589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8105888681634827622600785 6079416511226120716950589)
                    ·
                      refine ⟨2279781191709795268856471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6079416511226120716950589 2279781191709795268856471)
                      ·
                        rfl

theorem cell23_4439858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3].length) (baseStart_4439858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439858 prefixEnd_4439858 := by exact prefixLift 4439858
  have htrace : WordTrace (prefixWord ++ tailWord_4439858) baseStart_4439858 baseEnd_4439858 := by
    simpa [prefixWord, tailWord_4439858, baseEnd_4439858] using wordTrace_append hprefix tailTrace_4439858
  have hstable : (prefixWord ++ tailWord_4439858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439858).length < 2 ^ (prefixWord ++ tailWord_4439858).sum := by decide
  have hdescent : baseEnd_4439858 < baseStart_4439858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439871 : List Nat := [1, 1, 2, 2, 6, 1, 1, 2, 1, 3, 3]
def baseStart_4439871 : Nat := 118140960795 + 4439871 * 2 ^ 59
def prefixEnd_4439871 : Nat := 4983230072969 + 3 ^ 40 * 4439871 * 2
def baseEnd_4439871 : Nat := 2279787866958303717993911

theorem tailTrace_4439871 : CollatzResearch.WordTrace tailWord_4439871 prefixEnd_4439871 2279787866958303717993911 := by
  unfold tailWord_4439871
  simp only [CollatzResearch.WordTrace]
  refine ⟨161935398898113111442983467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107956932598742074295322311 161935398898113111442983467)
  ·
    refine ⟨242903098347169667164475201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161935398898113111442983467 242903098347169667164475201)
    ·
      refine ⟨182177323760377250373356401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242903098347169667164475201 182177323760377250373356401)
      ·
        refine ⟨136632992820282937780017301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182177323760377250373356401 136632992820282937780017301)
        ·
          refine ⟨6404671538450762708438311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 136632992820282937780017301 6404671538450762708438311)
          ·
            refine ⟨9607007307676144062657467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6404671538450762708438311 9607007307676144062657467)
            ·
              refine ⟨14410510961514216093986201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9607007307676144062657467 14410510961514216093986201)
              ·
                refine ⟨10807883221135662070489651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14410510961514216093986201 10807883221135662070489651)
                ·
                  refine ⟨16211824831703493105734477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10807883221135662070489651 16211824831703493105734477)
                  ·
                    refine ⟨6079434311888809914650429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16211824831703493105734477 6079434311888809914650429)
                    ·
                      refine ⟨2279787866958303717993911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6079434311888809914650429 2279787866958303717993911)
                      ·
                        rfl

theorem cell23_4439871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 3, 3].length) (baseStart_4439871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439871 prefixEnd_4439871 := by exact prefixLift 4439871
  have htrace : WordTrace (prefixWord ++ tailWord_4439871) baseStart_4439871 baseEnd_4439871 := by
    simpa [prefixWord, tailWord_4439871, baseEnd_4439871] using wordTrace_append hprefix tailTrace_4439871
  have hstable : (prefixWord ++ tailWord_4439871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439871).length < 2 ^ (prefixWord ++ tailWord_4439871).sum := by decide
  have hdescent : baseEnd_4439871 < baseStart_4439871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439904 : List Nat := [2, 1, 1, 3, 3, 3, 1, 1, 2, 6]
def baseStart_4439904 : Nat := 118140960795 + 4439904 * 2 ^ 59
def prefixEnd_4439904 : Nat := 4983230072969 + 3 ^ 40 * 4439904 * 2
def baseEnd_4439904 : Nat := 759934937273300696293753

theorem tailTrace_4439904 : CollatzResearch.WordTrace tailWord_4439904 prefixEnd_4439904 759934937273300696293753 := by
  unfold tailWord_4439904
  simp only [CollatzResearch.WordTrace]
  refine ⟨80968301253496779039467383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107957735004662372052623177 80968301253496779039467383)
  ·
    refine ⟨121452451880245168559201075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80968301253496779039467383 121452451880245168559201075)
    ·
      refine ⟨182178677820367752838801613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121452451880245168559201075 182178677820367752838801613)
      ·
        refine ⟨68317004182637907314550605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182178677820367752838801613 68317004182637907314550605)
        ·
          refine ⟨25618876568489215242956477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68317004182637907314550605 25618876568489215242956477)
          ·
            refine ⟨9607078713183455716108679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25618876568489215242956477 9607078713183455716108679)
            ·
              refine ⟨14410618069775183574163019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9607078713183455716108679 14410618069775183574163019)
              ·
                refine ⟨21615927104662775361244529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14410618069775183574163019 21615927104662775361244529)
                ·
                  refine ⟨16211945328497081520933397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21615927104662775361244529 16211945328497081520933397)
                  ·
                    refine ⟨759934937273300696293753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16211945328497081520933397 759934937273300696293753)
                    ·
                      rfl

theorem cell23_4439904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 2, 6].length) (baseStart_4439904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439904 prefixEnd_4439904 := by exact prefixLift 4439904
  have htrace : WordTrace (prefixWord ++ tailWord_4439904) baseStart_4439904 baseEnd_4439904 := by
    simpa [prefixWord, tailWord_4439904, baseEnd_4439904] using wordTrace_append hprefix tailTrace_4439904
  have hstable : (prefixWord ++ tailWord_4439904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439904).length < 2 ^ (prefixWord ++ tailWord_4439904).sum := by decide
  have hdescent : baseEnd_4439904 < baseStart_4439904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439927 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 7]
def baseStart_4439927 : Nat := 118140960795 + 4439927 * 2 ^ 59
def prefixEnd_4439927 : Nat := 4983230072969 + 3 ^ 40 * 4439927 * 2
def baseEnd_4439927 : Nat := 2279816621874955498893653

theorem tailTrace_4439927 : CollatzResearch.WordTrace tailWord_4439927 prefixEnd_4439927 2279816621874955498893653 := by
  unfold tailWord_4439927
  simp only [CollatzResearch.WordTrace]
  refine ⟨161937441385910233007022035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107958294257273488671348023 161937441385910233007022035)
  ·
    refine ⟨242906162078865349510533053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161937441385910233007022035 242906162078865349510533053)
    ·
      refine ⟨91089810779574506066449895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 242906162078865349510533053 91089810779574506066449895)
      ·
        refine ⟨136634716169361759099674843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91089810779574506066449895 136634716169361759099674843)
        ·
          refine ⟨204952074254042638649512265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136634716169361759099674843 204952074254042638649512265)
          ·
            refine ⟨153714055690531978987134199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204952074254042638649512265 153714055690531978987134199)
            ·
              refine ⟨230571083535797968480701299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153714055690531978987134199 230571083535797968480701299)
              ·
                refine ⟨345856625303696952721051949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 230571083535797968480701299 345856625303696952721051949)
                ·
                  refine ⟨129696234488886357270394481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 345856625303696952721051949 129696234488886357270394481)
                  ·
                    refine ⟨97272175866664767952795861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 129696234488886357270394481 97272175866664767952795861)
                    ·
                      refine ⟨2279816621874955498893653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 97272175866664767952795861 2279816621874955498893653)
                      ·
                        rfl

theorem cell23_4439927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_4439927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439927 prefixEnd_4439927 := by exact prefixLift 4439927
  have htrace : WordTrace (prefixWord ++ tailWord_4439927) baseStart_4439927 baseEnd_4439927 := by
    simpa [prefixWord, tailWord_4439927, baseEnd_4439927] using wordTrace_append hprefix tailTrace_4439927
  have hstable : (prefixWord ++ tailWord_4439927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439927).length < 2 ^ (prefixWord ++ tailWord_4439927).sum := by decide
  have hdescent : baseEnd_4439927 < baseStart_4439927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439962 : List Nat := [3, 1, 1, 4, 2, 2, 3, 1, 2, 2, 2]
def baseStart_4439962 : Nat := 118140960795 + 4439962 * 2 ^ 59
def prefixEnd_4439962 : Nat := 4983230072969 + 3 ^ 40 * 4439962 * 2
def baseEnd_4439962 : Nat := 2279834593697862861955993

theorem tailTrace_4439962 : CollatzResearch.WordTrace tailWord_4439962 prefixEnd_4439962 2279834593697862861955993 := by
  unfold tailWord_4439962
  simp only [CollatzResearch.WordTrace]
  refine ⟨40484679485195858496136535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107959145293855622656364093 40484679485195858496136535)
  ·
    refine ⟨60727019227793787744204803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40484679485195858496136535 60727019227793787744204803)
    ·
      refine ⟨91090528841690681616307205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60727019227793787744204803 91090528841690681616307205)
      ·
        refine ⟨17079474157817002803057601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91090528841690681616307205 17079474157817002803057601)
        ·
          refine ⟨12809605618362752102293201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17079474157817002803057601 12809605618362752102293201)
          ·
            refine ⟨9607204213772064076719901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12809605618362752102293201 9607204213772064076719901)
            ·
              refine ⟨3602701580164524028769963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9607204213772064076719901 3602701580164524028769963)
              ·
                refine ⟨5404052370246786043154945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3602701580164524028769963 5404052370246786043154945)
                ·
                  refine ⟨4053039277685089532366209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5404052370246786043154945 4053039277685089532366209)
                  ·
                    refine ⟨3039779458263817149274657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4053039277685089532366209 3039779458263817149274657)
                    ·
                      refine ⟨2279834593697862861955993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3039779458263817149274657 2279834593697862861955993)
                      ·
                        rfl

theorem cell23_4439962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_4439962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439962 prefixEnd_4439962 := by exact prefixLift 4439962
  have htrace : WordTrace (prefixWord ++ tailWord_4439962) baseStart_4439962 baseEnd_4439962 := by
    simpa [prefixWord, tailWord_4439962, baseEnd_4439962] using wordTrace_append hprefix tailTrace_4439962
  have hstable : (prefixWord ++ tailWord_4439962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439962).length < 2 ^ (prefixWord ++ tailWord_4439962).sum := by decide
  have hdescent : baseEnd_4439962 < baseStart_4439962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4439984 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 4]
def baseStart_4439984 : Nat := 118140960795 + 4439984 * 2 ^ 59
def prefixEnd_4439984 : Nat := 4983230072969 + 3 ^ 40 * 4439984 * 2
def baseEnd_4439984 : Nat := 2279845890272261775880891

theorem tailTrace_4439984 : CollatzResearch.WordTrace tailWord_4439984 prefixEnd_4439984 2279845890272261775880891 := by
  unfold tailWord_4439984
  simp only [CollatzResearch.WordTrace]
  refine ⟨80969760173351865870923503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107959680231135821161231337 80969760173351865870923503)
  ·
    refine ⟨121454640260027798806385255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80969760173351865870923503 121454640260027798806385255)
    ·
      refine ⟨182181960390041698209577883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121454640260027798806385255 182181960390041698209577883)
      ·
        refine ⟨273272940585062547314366825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182181960390041698209577883 273272940585062547314366825)
        ·
          refine ⟨204954705438796910485775119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 273272940585062547314366825 204954705438796910485775119)
          ·
            refine ⟨307432058158195365728662679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204954705438796910485775119 307432058158195365728662679)
            ·
              refine ⟨461148087237293048592994019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307432058158195365728662679 461148087237293048592994019)
              ·
                refine ⟨691722130855939572889491029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 461148087237293048592994019 691722130855939572889491029)
                ·
                  refine ⟨8106118720968041869798723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 691722130855939572889491029 8106118720968041869798723)
                  ·
                    refine ⟨12159178081452062804698085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8106118720968041869798723 12159178081452062804698085)
                    ·
                      refine ⟨2279845890272261775880891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12159178081452062804698085 2279845890272261775880891)
                      ·
                        rfl

theorem cell23_4439984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 4].length) (baseStart_4439984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4439984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4439984 prefixEnd_4439984 := by exact prefixLift 4439984
  have htrace : WordTrace (prefixWord ++ tailWord_4439984) baseStart_4439984 baseEnd_4439984 := by
    simpa [prefixWord, tailWord_4439984, baseEnd_4439984] using wordTrace_append hprefix tailTrace_4439984
  have hstable : (prefixWord ++ tailWord_4439984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4439984).length < 2 ^ (prefixWord ++ tailWord_4439984).sum := by decide
  have hdescent : baseEnd_4439984 < baseStart_4439984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4439984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440062 : List Nat := [4, 2, 2, 2, 1, 2, 1, 4, 1, 4]
def baseStart_4440062 : Nat := 118140960795 + 4440062 * 2 ^ 59
def prefixEnd_4440062 : Nat := 4983230072969 + 3 ^ 40 * 4440062 * 2
def baseEnd_4440062 : Nat := 759961980587770823568511

theorem tailTrace_4440062 : CollatzResearch.WordTrace tailWord_4440062 prefixEnd_4440062 759961980587770823568511 := by
  unfold tailWord_4440062
  simp only [CollatzResearch.WordTrace]
  refine ⟨20242795655052643882898305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107961576826947434042124293 20242795655052643882898305)
  ·
    refine ⟨15182096741289482912173729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20242795655052643882898305 15182096741289482912173729)
    ·
      refine ⟨11386572555967112184130297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15182096741289482912173729 11386572555967112184130297)
      ·
        refine ⟨8539929416975334138097723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11386572555967112184130297 8539929416975334138097723)
        ·
          refine ⟨12809894125463001207146585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8539929416975334138097723 12809894125463001207146585)
          ·
            refine ⟨9607420594097250905359939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12809894125463001207146585 9607420594097250905359939)
            ·
              refine ⟨14411130891145876358039909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9607420594097250905359939 14411130891145876358039909)
              ·
                refine ⟨2702087042089851817132483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14411130891145876358039909 2702087042089851817132483)
                ·
                  refine ⟨4053130563134777725698725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2702087042089851817132483 4053130563134777725698725)
                  ·
                    refine ⟨759961980587770823568511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4053130563134777725698725 759961980587770823568511)
                    ·
                      rfl

theorem cell23_4440062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_4440062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440062 prefixEnd_4440062 := by exact prefixLift 4440062
  have htrace : WordTrace (prefixWord ++ tailWord_4440062) baseStart_4440062 baseEnd_4440062 := by
    simpa [prefixWord, tailWord_4440062, baseEnd_4440062] using wordTrace_append hprefix tailTrace_4440062
  have hstable : (prefixWord ++ tailWord_4440062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440062).length < 2 ^ (prefixWord ++ tailWord_4440062).sum := by decide
  have hdescent : baseEnd_4440062 < baseStart_4440062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440071 : List Nat := [1, 1, 4, 3, 1, 2, 1, 2, 3, 5]
def baseStart_4440071 : Nat := 118140960795 + 4440071 * 2 ^ 59
def prefixEnd_4440071 : Nat := 4983230072969 + 3 ^ 40 * 4440071 * 2
def baseEnd_4440071 : Nat := 759963521029734311830997

theorem tailTrace_4440071 : CollatzResearch.WordTrace tailWord_4440071 prefixEnd_4440071 759963521029734311830997 := by
  unfold tailWord_4440071
  simp only [CollatzResearch.WordTrace]
  refine ⟨161942693497388545600264067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107961795664925697066842711 161942693497388545600264067)
  ·
    refine ⟨242914040246082818400396101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161942693497388545600264067 242914040246082818400396101)
    ·
      refine ⟨45546382546140528450074269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 242914040246082818400396101 45546382546140528450074269)
      ·
        refine ⟨17079893454802698168777851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45546382546140528450074269 17079893454802698168777851)
        ·
          refine ⟨25619840182204047253166777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17079893454802698168777851 25619840182204047253166777)
          ·
            refine ⟨19214880136653035439875083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25619840182204047253166777 19214880136653035439875083)
            ·
              refine ⟨28822320204979553159812625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19214880136653035439875083 28822320204979553159812625)
              ·
                refine ⟨21616740153734664869859469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28822320204979553159812625 21616740153734664869859469)
                ·
                  refine ⟨8106277557650499326197301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21616740153734664869859469 8106277557650499326197301)
                  ·
                    refine ⟨759963521029734311830997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8106277557650499326197301 759963521029734311830997)
                    ·
                      rfl

theorem cell23_4440071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_4440071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440071 prefixEnd_4440071 := by exact prefixLift 4440071
  have htrace : WordTrace (prefixWord ++ tailWord_4440071) baseStart_4440071 baseEnd_4440071 := by
    simpa [prefixWord, tailWord_4440071, baseEnd_4440071] using wordTrace_append hprefix tailTrace_4440071
  have hstable : (prefixWord ++ tailWord_4440071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440071).length < 2 ^ (prefixWord ++ tailWord_4440071).sum := by decide
  have hdescent : baseEnd_4440071 < baseStart_4440071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440078 : List Nat := [4, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2]
def baseStart_4440078 : Nat := 118140960795 + 4440078 * 2 ^ 59
def prefixEnd_4440078 : Nat := 4983230072969 + 3 ^ 40 * 4440078 * 2
def baseEnd_4440078 : Nat := 2279894157453784408105459

theorem tailTrace_4440078 : CollatzResearch.WordTrace tailWord_4440078 prefixEnd_4440078 2279894157453784408105459 := by
  unfold tailWord_4440078
  simp only [CollatzResearch.WordTrace]
  refine ⟨20242868601045398224471111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107961965872242123863845925 20242868601045398224471111)
  ·
    refine ⟨30364302901568097336706667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20242868601045398224471111 30364302901568097336706667)
    ·
      refine ⟨45546454352352146005060001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30364302901568097336706667 45546454352352146005060001)
      ·
        refine ⟨34159840764264109503795001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45546454352352146005060001 34159840764264109503795001)
        ·
          refine ⟨25619880573198082127846251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34159840764264109503795001 25619880573198082127846251)
          ·
            refine ⟨38429820859797123191769377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25619880573198082127846251 38429820859797123191769377)
            ·
              refine ⟨28822365644847842393827033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38429820859797123191769377 28822365644847842393827033)
              ·
                refine ⟨21616774233635881795370275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28822365644847842393827033 21616774233635881795370275)
                ·
                  refine ⟨32425161350453822693055413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21616774233635881795370275 32425161350453822693055413)
                  ·
                    refine ⟨3039858876605045877473945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32425161350453822693055413 3039858876605045877473945)
                    ·
                      refine ⟨2279894157453784408105459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3039858876605045877473945 2279894157453784408105459)
                      ·
                        rfl

theorem cell23_4440078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_4440078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440078 prefixEnd_4440078 := by exact prefixLift 4440078
  have htrace : WordTrace (prefixWord ++ tailWord_4440078) baseStart_4440078 baseEnd_4440078 := by
    simpa [prefixWord, tailWord_4440078, baseEnd_4440078] using wordTrace_append hprefix tailTrace_4440078
  have hstable : (prefixWord ++ tailWord_4440078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440078).length < 2 ^ (prefixWord ++ tailWord_4440078).sum := by decide
  have hdescent : baseEnd_4440078 < baseStart_4440078 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440085 : List Nat := [1, 3, 2, 1, 5, 1, 1, 2, 3, 1, 3]
def baseStart_4440085 : Nat := 118140960795 + 4440085 * 2 ^ 59
def prefixEnd_4440085 : Nat := 4983230072969 + 3 ^ 40 * 4440085 * 2
def baseEnd_4440085 : Nat := 2279897751818365880717927

theorem tailTrace_4440085 : CollatzResearch.WordTrace tailWord_4440085 prefixEnd_4440085 2279897751818365880717927 := by
  unfold tailWord_4440085
  simp only [CollatzResearch.WordTrace]
  refine ⟨161943204119337825991273709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107962136079558550660849139 161943204119337825991273709)
  ·
    refine ⟨60728701544751684746727641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161943204119337825991273709 60728701544751684746727641)
    ·
      refine ⟨45546526158563763560045731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60728701544751684746727641 45546526158563763560045731)
      ·
        refine ⟨68319789237845645340068597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45546526158563763560045731 68319789237845645340068597)
        ·
          refine ⟨6404980241048029250631431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68319789237845645340068597 6404980241048029250631431)
          ·
            refine ⟨9607470361572043875947147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6404980241048029250631431 9607470361572043875947147)
            ·
              refine ⟨14411205542358065813920721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9607470361572043875947147 14411205542358065813920721)
              ·
                refine ⟨10808404156768549360440541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14411205542358065813920721 10808404156768549360440541)
                ·
                  refine ⟨4053151558788206010165203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10808404156768549360440541 4053151558788206010165203)
                  ·
                    refine ⟨6079727338182309015247805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4053151558788206010165203 6079727338182309015247805)
                    ·
                      refine ⟨2279897751818365880717927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6079727338182309015247805 2279897751818365880717927)
                      ·
                        rfl

theorem cell23_4440085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 3, 1, 3].length) (baseStart_4440085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440085 prefixEnd_4440085 := by exact prefixLift 4440085
  have htrace : WordTrace (prefixWord ++ tailWord_4440085) baseStart_4440085 baseEnd_4440085 := by
    simpa [prefixWord, tailWord_4440085, baseEnd_4440085] using wordTrace_append hprefix tailTrace_4440085
  have hstable : (prefixWord ++ tailWord_4440085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440085).length < 2 ^ (prefixWord ++ tailWord_4440085).sum := by decide
  have hdescent : baseEnd_4440085 < baseStart_4440085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440091 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 1, 8, 2]
def baseStart_4440091 : Nat := 118140960795 + 4440091 * 2 ^ 59
def prefixEnd_4440091 : Nat := 4983230072969 + 3 ^ 40 * 4440091 * 2
def baseEnd_4440091 : Nat := 2279900832702292857242899

theorem tailTrace_4440091 : CollatzResearch.WordTrace tailWord_4440091 prefixEnd_4440091 2279900832702292857242899 := by
  unfold tailWord_4440091
  simp only [CollatzResearch.WordTrace]
  refine ⟨161943422957316089015992127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107962281971544059343994751 161943422957316089015992127)
  ·
    refine ⟨242915134435974133523988191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161943422957316089015992127 242915134435974133523988191)
    ·
      refine ⟨364372701653961200285982287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242915134435974133523988191 364372701653961200285982287)
      ·
        refine ⟨546559052480941800428973431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 364372701653961200285982287 546559052480941800428973431)
        ·
          refine ⟨819838578721412700643460147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 546559052480941800428973431 819838578721412700643460147)
          ·
            refine ⟨1229757868082119050965190221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 819838578721412700643460147 1229757868082119050965190221)
            ·
              refine ⟨461159200530794644111946333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1229757868082119050965190221 461159200530794644111946333)
              ·
                refine ⟨172934700199047991541979875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 461159200530794644111946333 172934700199047991541979875)
                ·
                  refine ⟨259402050298571987312969813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 172934700199047991541979875 259402050298571987312969813)
                  ·
                    refine ⟨3039867776936390476323865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 259402050298571987312969813 3039867776936390476323865)
                    ·
                      refine ⟨2279900832702292857242899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3039867776936390476323865 2279900832702292857242899)
                      ·
                        rfl

theorem cell23_4440091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 8, 2].length) (baseStart_4440091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440091 prefixEnd_4440091 := by exact prefixLift 4440091
  have htrace : WordTrace (prefixWord ++ tailWord_4440091) baseStart_4440091 baseEnd_4440091 := by
    simpa [prefixWord, tailWord_4440091, baseEnd_4440091] using wordTrace_append hprefix tailTrace_4440091
  have hstable : (prefixWord ++ tailWord_4440091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440091).length < 2 ^ (prefixWord ++ tailWord_4440091).sum := by decide
  have hdescent : baseEnd_4440091 < baseStart_4440091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440101 : List Nat := [1, 3, 1, 2, 2, 3, 2, 2, 1, 6]
def baseStart_4440101 : Nat := 118140960795 + 4440101 * 2 ^ 59
def prefixEnd_4440101 : Nat := 4983230072969 + 3 ^ 40 * 4440101 * 2
def baseEnd_4440101 : Nat := 759968655836279272705951

theorem tailTrace_4440101 : CollatzResearch.WordTrace tailWord_4440101 prefixEnd_4440101 759968655836279272705951 := by
  unfold tailWord_4440101
  simp only [CollatzResearch.WordTrace]
  refine ⟨161943787687279860723856157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107962525124853240482570771 161943787687279860723856157)
  ·
    refine ⟨60728920382729947771446059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161943787687279860723856157 60728920382729947771446059)
    ·
      refine ⟨91093380574094921657169089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60728920382729947771446059 91093380574094921657169089)
      ·
        refine ⟨68320035430571191242876817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91093380574094921657169089 68320035430571191242876817)
        ·
          refine ⟨51240026572928393432157613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68320035430571191242876817 51240026572928393432157613)
          ·
            refine ⟨19215009964848147537059105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51240026572928393432157613 19215009964848147537059105)
            ·
              refine ⟨14411257473636110652794329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19215009964848147537059105 14411257473636110652794329)
              ·
                refine ⟨10808443105227082989595747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14411257473636110652794329 10808443105227082989595747)
                ·
                  refine ⟨16212664657840624484393621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10808443105227082989595747 16212664657840624484393621)
                  ·
                    refine ⟨759968655836279272705951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16212664657840624484393621 759968655836279272705951)
                    ·
                      rfl

theorem cell23_4440101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 6].length) (baseStart_4440101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440101 prefixEnd_4440101 := by exact prefixLift 4440101
  have htrace : WordTrace (prefixWord ++ tailWord_4440101) baseStart_4440101 baseEnd_4440101 := by
    simpa [prefixWord, tailWord_4440101, baseEnd_4440101] using wordTrace_append hprefix tailTrace_4440101
  have hstable : (prefixWord ++ tailWord_4440101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440101).length < 2 ^ (prefixWord ++ tailWord_4440101).sum := by decide
  have hdescent : baseEnd_4440101 < baseStart_4440101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440111 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 5, 2, 3]
def baseStart_4440111 : Nat := 118140960795 + 4440111 * 2 ^ 59
def prefixEnd_4440111 : Nat := 4983230072969 + 3 ^ 40 * 4440111 * 2
def baseEnd_4440111 : Nat := 2279911102315382778992807

theorem tailTrace_4440111 : CollatzResearch.WordTrace tailWord_4440111 prefixEnd_4440111 2279911102315382778992807 := by
  unfold tailWord_4440111
  simp only [CollatzResearch.WordTrace]
  refine ⟨161944152417243632431720187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107962768278162421621146791 161944152417243632431720187)
  ·
    refine ⟨242916228625865448647580281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161944152417243632431720187 242916228625865448647580281)
    ·
      refine ⟨182187171469399086485685211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242916228625865448647580281 182187171469399086485685211)
      ·
        refine ⟨273280757204098629728527817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182187171469399086485685211 273280757204098629728527817)
        ·
          refine ⟨204960567903073972296395863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 273280757204098629728527817 204960567903073972296395863)
          ·
            refine ⟨307440851854610958444593795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204960567903073972296395863 307440851854610958444593795)
            ·
              refine ⟨461161277781916437666890693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307440851854610958444593795 461161277781916437666890693)
              ·
                refine ⟨86467739584109332062542005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 461161277781916437666890693 86467739584109332062542005)
                ·
                  refine ⟨8106350586010249880863313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 86467739584109332062542005 8106350586010249880863313)
                  ·
                    refine ⟨6079762939507687410647485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8106350586010249880863313 6079762939507687410647485)
                    ·
                      refine ⟨2279911102315382778992807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6079762939507687410647485 2279911102315382778992807)
                      ·
                        rfl

theorem cell23_4440111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 2, 3].length) (baseStart_4440111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440111 prefixEnd_4440111 := by exact prefixLift 4440111
  have htrace : WordTrace (prefixWord ++ tailWord_4440111) baseStart_4440111 baseEnd_4440111 := by
    simpa [prefixWord, tailWord_4440111, baseEnd_4440111] using wordTrace_append hprefix tailTrace_4440111
  have hstable : (prefixWord ++ tailWord_4440111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440111).length < 2 ^ (prefixWord ++ tailWord_4440111).sum := by decide
  have hdescent : baseEnd_4440111 < baseStart_4440111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440135 : List Nat := [1, 1, 4, 1, 3, 1, 5, 1, 2, 4]
def baseStart_4440135 : Nat := 118140960795 + 4440135 * 2 ^ 59
def prefixEnd_4440135 : Nat := 4983230072969 + 3 ^ 40 * 4440135 * 2
def baseEnd_4440135 : Nat := 759974475283696895030899

theorem tailTrace_4440135 : CollatzResearch.WordTrace tailWord_4440135 prefixEnd_4440135 759974475283696895030899 := by
  unfold tailWord_4440135
  simp only [CollatzResearch.WordTrace]
  refine ⟨161945027769156684530593859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107963351846104456353729239 161945027769156684530593859)
  ·
    refine ⟨242917541653735026795890789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161945027769156684530593859 242917541653735026795890789)
    ·
      refine ⟨45547039060075317524229523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 242917541653735026795890789 45547039060075317524229523)
      ·
        refine ⟨68320558590112976286344285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45547039060075317524229523 68320558590112976286344285)
        ·
          refine ⟨25620209471292366107379107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68320558590112976286344285 25620209471292366107379107)
          ·
            refine ⟨38430314206938549161068661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25620209471292366107379107 38430314206938549161068661)
            ·
              refine ⟨3602841956900488983850187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38430314206938549161068661 3602841956900488983850187)
              ·
                refine ⟨5404262935350733475775281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3602841956900488983850187 5404262935350733475775281)
                ·
                  refine ⟨4053197201513050106831461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5404262935350733475775281 4053197201513050106831461)
                  ·
                    refine ⟨759974475283696895030899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4053197201513050106831461 759974475283696895030899)
                    ·
                      rfl

theorem cell23_4440135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 2, 4].length) (baseStart_4440135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440135 prefixEnd_4440135 := by exact prefixLift 4440135
  have htrace : WordTrace (prefixWord ++ tailWord_4440135) baseStart_4440135 baseEnd_4440135 := by
    simpa [prefixWord, tailWord_4440135, baseEnd_4440135] using wordTrace_append hprefix tailTrace_4440135
  have hstable : (prefixWord ++ tailWord_4440135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440135).length < 2 ^ (prefixWord ++ tailWord_4440135).sum := by decide
  have hdescent : baseEnd_4440135 < baseStart_4440135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440201 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 4, 1, 5]
def baseStart_4440201 : Nat := 118140960795 + 4440201 * 2 ^ 59
def prefixEnd_4440201 : Nat := 4983230072969 + 3 ^ 40 * 4440201 * 2
def baseEnd_4440201 : Nat := 2279957315574287426867393

theorem tailTrace_4440201 : CollatzResearch.WordTrace tailWord_4440201 prefixEnd_4440201 2279957315574287426867393 := by
  unfold tailWord_4440201
  simp only [CollatzResearch.WordTrace]
  refine ⟨161947434986917577802496457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107964956657945051868330971 161947434986917577802496457)
  ·
    refine ⟨121460576240188183351872343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161947434986917577802496457 121460576240188183351872343)
    ·
      refine ⟨182190864360282275027808515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121460576240188183351872343 182190864360282275027808515)
      ·
        refine ⟨273286296540423412541712773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182190864360282275027808515 273286296540423412541712773)
        ·
          refine ⟨51241180601329389851571145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 273286296540423412541712773 51241180601329389851571145)
          ·
            refine ⟨38430885450997042388678359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51241180601329389851571145 38430885450997042388678359)
            ·
              refine ⟨57646328176495563583017539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38430885450997042388678359 57646328176495563583017539)
              ·
                refine ⟨86469492264743345374526309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57646328176495563583017539 86469492264743345374526309)
                ·
                  refine ⟨16213029799639377257723683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86469492264743345374526309 16213029799639377257723683)
                  ·
                    refine ⟨24319544699459065886585525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16213029799639377257723683 24319544699459065886585525)
                    ·
                      refine ⟨2279957315574287426867393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24319544699459065886585525 2279957315574287426867393)
                      ·
                        rfl

theorem cell23_4440201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 1, 5].length) (baseStart_4440201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440201 prefixEnd_4440201 := by exact prefixLift 4440201
  have htrace : WordTrace (prefixWord ++ tailWord_4440201) baseStart_4440201 baseEnd_4440201 := by
    simpa [prefixWord, tailWord_4440201, baseEnd_4440201] using wordTrace_append hprefix tailTrace_4440201
  have hstable : (prefixWord ++ tailWord_4440201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440201).length < 2 ^ (prefixWord ++ tailWord_4440201).sum := by decide
  have hdescent : baseEnd_4440201 < baseStart_4440201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440202 : List Nat := [3, 1, 2, 3, 1, 2, 3, 2, 1, 3, 2]
def baseStart_4440202 : Nat := 118140960795 + 4440202 * 2 ^ 59
def prefixEnd_4440202 : Nat := 4983230072969 + 3 ^ 40 * 4440202 * 2
def baseEnd_4440202 : Nat := 2279957829054941922954889

theorem tailTrace_4440202 : CollatzResearch.WordTrace tailWord_4440202 prefixEnd_4440202 2279957829054941922954889 := by
  unfold tailWord_4440202
  simp only [CollatzResearch.WordTrace]
  refine ⟨40486867864978488743320715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107964980973275969982188573 40486867864978488743320715)
  ·
    refine ⟨60730301797467733114981073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40486867864978488743320715 60730301797467733114981073)
    ·
      refine ⟨45547726348100799836235805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60730301797467733114981073 45547726348100799836235805)
      ·
        refine ⟨17080397380537799938588427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45547726348100799836235805 17080397380537799938588427)
        ·
          refine ⟨25620596070806699907882641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17080397380537799938588427 25620596070806699907882641)
          ·
            refine ⟨19215447053105024930911981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25620596070806699907882641 19215447053105024930911981)
            ·
              refine ⟨7205792644914384349091993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19215447053105024930911981 7205792644914384349091993)
              ·
                refine ⟨5404344483685788261818995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7205792644914384349091993 5404344483685788261818995)
                ·
                  refine ⟨8106516725528682392728493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5404344483685788261818995 8106516725528682392728493)
                  ·
                    refine ⟨3039943772073255897273185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8106516725528682392728493 3039943772073255897273185)
                    ·
                      refine ⟨2279957829054941922954889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3039943772073255897273185 2279957829054941922954889)
                      ·
                        rfl

theorem cell23_4440202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_4440202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440202 prefixEnd_4440202 := by exact prefixLift 4440202
  have htrace : WordTrace (prefixWord ++ tailWord_4440202) baseStart_4440202 baseEnd_4440202 := by
    simpa [prefixWord, tailWord_4440202, baseEnd_4440202] using wordTrace_append hprefix tailTrace_4440202
  have hstable : (prefixWord ++ tailWord_4440202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440202).length < 2 ^ (prefixWord ++ tailWord_4440202).sum := by decide
  have hdescent : baseEnd_4440202 < baseStart_4440202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440211 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 4]
def baseStart_4440211 : Nat := 118140960795 + 4440211 * 2 ^ 59
def prefixEnd_4440211 : Nat := 4983230072969 + 3 ^ 40 * 4440211 * 2
def baseEnd_4440211 : Nat := 2279962450380832387742347

theorem tailTrace_4440211 : CollatzResearch.WordTrace tailWord_4440211 prefixEnd_4440211 2279962450380832387742347 := by
  unfold tailWord_4440211
  simp only [CollatzResearch.WordTrace]
  refine ⟨161947799716881349510360487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107965199811254233006906991 161947799716881349510360487)
  ·
    refine ⟨242921699575322024265540731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161947799716881349510360487 242921699575322024265540731)
    ·
      refine ⟨364382549362983036398311097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242921699575322024265540731 364382549362983036398311097)
      ·
        refine ⟨273286912022237277298733323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 364382549362983036398311097 273286912022237277298733323)
        ·
          refine ⟨409930368033355915948099985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273286912022237277298733323 409930368033355915948099985)
          ·
            refine ⟨307447776025016936961074989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 409930368033355915948099985 307447776025016936961074989)
            ·
              refine ⟨115292916009381351360403121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 307447776025016936961074989 115292916009381351360403121)
              ·
                refine ⟨86469687007036013520302341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115292916009381351360403121 86469687007036013520302341)
                ·
                  refine ⟨16213066313819252535056689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86469687007036013520302341 16213066313819252535056689)
                  ·
                    refine ⟨12159799735364439401292517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16213066313819252535056689 12159799735364439401292517)
                    ·
                      refine ⟨2279962450380832387742347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12159799735364439401292517 2279962450380832387742347)
                      ·
                        rfl

theorem cell23_4440211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 4].length) (baseStart_4440211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440211 prefixEnd_4440211 := by exact prefixLift 4440211
  have htrace : WordTrace (prefixWord ++ tailWord_4440211) baseStart_4440211 baseEnd_4440211 := by
    simpa [prefixWord, tailWord_4440211, baseEnd_4440211] using wordTrace_append hprefix tailTrace_4440211
  have hstable : (prefixWord ++ tailWord_4440211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440211).length < 2 ^ (prefixWord ++ tailWord_4440211).sum := by decide
  have hdescent : baseEnd_4440211 < baseStart_4440211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440248 : List Nat := [2, 1, 2, 1, 2, 1, 5, 1, 2, 3, 3]
def baseStart_4440248 : Nat := 118140960795 + 4440248 * 2 ^ 59
def prefixEnd_4440248 : Nat := 4983230072969 + 3 ^ 40 * 4440248 * 2
def baseEnd_4440248 : Nat := 2279981449165048742979677

theorem tailTrace_4440248 : CollatzResearch.WordTrace tailWord_4440248 prefixEnd_4440248 2279981449165048742979677 := by
  unfold tailWord_4440248
  simp only [CollatzResearch.WordTrace]
  refine ⟨80974574608873652414728699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107966099478498203219638265 80974574608873652414728699)
  ·
    refine ⟨121461861913310478622093049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80974574608873652414728699 121461861913310478622093049)
    ·
      refine ⟨91096396434982858966569787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121461861913310478622093049 91096396434982858966569787)
      ·
        refine ⟨136644594652474288449854681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91096396434982858966569787 136644594652474288449854681)
        ·
          refine ⟨102483445989355716337391011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136644594652474288449854681 102483445989355716337391011)
          ·
            refine ⟨153725168984033574506086517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102483445989355716337391011 153725168984033574506086517)
            ·
              refine ⟨14411734592253147609945611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 153725168984033574506086517 14411734592253147609945611)
              ·
                refine ⟨21617601888379721414918417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14411734592253147609945611 21617601888379721414918417)
                ·
                  refine ⟨16213201416284791061188813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21617601888379721414918417 16213201416284791061188813)
                  ·
                    refine ⟨6079950531106796647945805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16213201416284791061188813 6079950531106796647945805)
                    ·
                      refine ⟨2279981449165048742979677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6079950531106796647945805 2279981449165048742979677)
                      ·
                        rfl

theorem cell23_4440248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 2, 3, 3].length) (baseStart_4440248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440248 prefixEnd_4440248 := by exact prefixLift 4440248
  have htrace : WordTrace (prefixWord ++ tailWord_4440248) baseStart_4440248 baseEnd_4440248 := by
    simpa [prefixWord, tailWord_4440248, baseEnd_4440248] using wordTrace_append hprefix tailTrace_4440248
  have hstable : (prefixWord ++ tailWord_4440248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440248).length < 2 ^ (prefixWord ++ tailWord_4440248).sum := by decide
  have hdescent : baseEnd_4440248 < baseStart_4440248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440251 : List Nat := [1, 1, 1, 1, 1, 2, 6, 2, 1, 7]
def baseStart_4440251 : Nat := 118140960795 + 4440251 * 2 ^ 59
def prefixEnd_4440251 : Nat := 4983230072969 + 3 ^ 40 * 4440251 * 2
def baseEnd_4440251 : Nat := 759994329869004077080721

theorem tailTrace_4440251 : CollatzResearch.WordTrace tailWord_4440251 prefixEnd_4440251 759994329869004077080721 := by
  unfold tailWord_4440251
  simp only [CollatzResearch.WordTrace]
  refine ⟨161949258636736436341816607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107966172424490957561211071 161949258636736436341816607)
  ·
    refine ⟨242923887955104654512724911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161949258636736436341816607 242923887955104654512724911)
    ·
      refine ⟨364385831932656981769087367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242923887955104654512724911 364385831932656981769087367)
      ·
        refine ⟨546578747898985472653631051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 364385831932656981769087367 546578747898985472653631051)
        ·
          refine ⟨819868121848478208980446577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 546578747898985472653631051 819868121848478208980446577)
          ·
            refine ⟨614901091386358656735334933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 819868121848478208980446577 614901091386358656735334933)
            ·
              refine ⟨28823488658735562034468825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 614901091386358656735334933 28823488658735562034468825)
              ·
                refine ⟨21617616494051671525851619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28823488658735562034468825 21617616494051671525851619)
                ·
                  refine ⟨32426424741077507288777429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21617616494051671525851619 32426424741077507288777429)
                  ·
                    refine ⟨759994329869004077080721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32426424741077507288777429 759994329869004077080721)
                    ·
                      rfl

theorem cell23_4440251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 7].length) (baseStart_4440251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440251 prefixEnd_4440251 := by exact prefixLift 4440251
  have htrace : WordTrace (prefixWord ++ tailWord_4440251) baseStart_4440251 baseEnd_4440251 := by
    simpa [prefixWord, tailWord_4440251, baseEnd_4440251] using wordTrace_append hprefix tailTrace_4440251
  have hstable : (prefixWord ++ tailWord_4440251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440251).length < 2 ^ (prefixWord ++ tailWord_4440251).sum := by decide
  have hdescent : baseEnd_4440251 < baseStart_4440251 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440261 : List Nat := [1, 3, 1, 1, 1, 1, 4, 2, 1, 1, 7]
def baseStart_4440261 : Nat := 118140960795 + 4440261 * 2 ^ 59
def prefixEnd_4440261 : Nat := 4983230072969 + 3 ^ 40 * 4440261 * 2
def baseEnd_4440261 : Nat := 2279988124413557192117117

theorem tailTrace_4440261 : CollatzResearch.WordTrace tailWord_4440261 prefixEnd_4440261 2279988124413557192117117 := by
  unfold tailWord_4440261
  simp only [CollatzResearch.WordTrace]
  refine ⟨161949623366700208049680637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107966415577800138699787091 161949623366700208049680637)
  ·
    refine ⟨60731108762512578018630239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161949623366700208049680637 60731108762512578018630239)
    ·
      refine ⟨91096663143768867027945359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60731108762512578018630239 91096663143768867027945359)
      ·
        refine ⟨136644994715653300541918039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91096663143768867027945359 136644994715653300541918039)
        ·
          refine ⟨204967492073479950812877059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136644994715653300541918039 204967492073479950812877059)
          ·
            refine ⟨307451238110219926219315589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204967492073479950812877059 307451238110219926219315589)
            ·
              refine ⟨57647107145666236166121673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 307451238110219926219315589 57647107145666236166121673)
              ·
                refine ⟨43235330359249677124591255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57647107145666236166121673 43235330359249677124591255)
                ·
                  refine ⟨64852995538874515686886883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43235330359249677124591255 64852995538874515686886883)
                  ·
                    refine ⟨97279493308311773530330325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 64852995538874515686886883 97279493308311773530330325)
                    ·
                      refine ⟨2279988124413557192117117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 97279493308311773530330325 2279988124413557192117117)
                      ·
                        rfl

theorem cell23_4440261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_4440261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440261 prefixEnd_4440261 := by exact prefixLift 4440261
  have htrace : WordTrace (prefixWord ++ tailWord_4440261) baseStart_4440261 baseEnd_4440261 := by
    simpa [prefixWord, tailWord_4440261, baseEnd_4440261] using wordTrace_append hprefix tailTrace_4440261
  have hstable : (prefixWord ++ tailWord_4440261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440261).length < 2 ^ (prefixWord ++ tailWord_4440261).sum := by decide
  have hdescent : baseEnd_4440261 < baseStart_4440261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440288 : List Nat := [2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 4]
def baseStart_4440288 : Nat := 118140960795 + 4440288 * 2 ^ 59
def prefixEnd_4440288 : Nat := 4983230072969 + 3 ^ 40 * 4440288 * 2
def baseEnd_4440288 : Nat := 2280001988391228586479493

theorem tailTrace_4440288 : CollatzResearch.WordTrace tailWord_4440288 prefixEnd_4440288 2280001988391228586479493 := by
  unfold tailWord_4440288
  simp only [CollatzResearch.WordTrace]
  refine ⟨80975304068801195830456759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107967072091734927773942345 80975304068801195830456759)
  ·
    refine ⟨121462956103201793745685139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80975304068801195830456759 121462956103201793745685139)
    ·
      refine ⟨182194434154802690618527709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121462956103201793745685139 182194434154802690618527709)
      ·
        refine ⟨68322912808051008981947891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182194434154802690618527709 68322912808051008981947891)
        ·
          refine ⟨102484369212076513472921837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68322912808051008981947891 102484369212076513472921837)
          ·
            refine ⟨38431638454528692552345689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102484369212076513472921837 38431638454528692552345689)
            ·
              refine ⟨28823728840896519414259267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38431638454528692552345689 28823728840896519414259267)
              ·
                refine ⟨43235593261344779121388901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28823728840896519414259267 43235593261344779121388901)
                ·
                  refine ⟨8106673736502146085260419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43235593261344779121388901 8106673736502146085260419)
                  ·
                    refine ⟨12160010604753219127890629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8106673736502146085260419 12160010604753219127890629)
                    ·
                      refine ⟨2280001988391228586479493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12160010604753219127890629 2280001988391228586479493)
                      ·
                        rfl

theorem cell23_4440288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_4440288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440288 prefixEnd_4440288 := by exact prefixLift 4440288
  have htrace : WordTrace (prefixWord ++ tailWord_4440288) baseStart_4440288 baseEnd_4440288 := by
    simpa [prefixWord, tailWord_4440288, baseEnd_4440288] using wordTrace_append hprefix tailTrace_4440288
  have hstable : (prefixWord ++ tailWord_4440288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440288).length < 2 ^ (prefixWord ++ tailWord_4440288).sum := by decide
  have hdescent : baseEnd_4440288 < baseStart_4440288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440305 : List Nat := [1, 2, 2, 2, 2, 1, 4, 1, 2, 4, 2]
def baseStart_4440305 : Nat := 118140960795 + 4440305 * 2 ^ 59
def prefixEnd_4440305 : Nat := 4983230072969 + 3 ^ 40 * 4440305 * 2
def baseEnd_4440305 : Nat := 2280010717562355019966915

theorem tailTrace_4440305 : CollatzResearch.WordTrace tailWord_4440305 prefixEnd_4440305 2280010717562355019966915 := by
  unfold tailWord_4440305
  simp only [CollatzResearch.WordTrace]
  refine ⟨161951228178540803564282369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107967485452360535709521579 161951228178540803564282369)
  ·
    refine ⟨121463421133905602673211777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161951228178540803564282369 121463421133905602673211777)
    ·
      refine ⟨91097565850429202004908833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121463421133905602673211777 91097565850429202004908833)
      ·
        refine ⟨68323174387821901503681625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91097565850429202004908833 68323174387821901503681625)
        ·
          refine ⟨51242380790866426127761219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68323174387821901503681625 51242380790866426127761219)
          ·
            refine ⟨76863571186299639191641829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51242380790866426127761219 76863571186299639191641829)
            ·
              refine ⟨14411919597431182348432843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76863571186299639191641829 14411919597431182348432843)
              ·
                refine ⟨21617879396146773522649265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14411919597431182348432843 21617879396146773522649265)
                ·
                  refine ⟨16213409547110080141986949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21617879396146773522649265 16213409547110080141986949)
                  ·
                    refine ⟨3040014290083140026622553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16213409547110080141986949 3040014290083140026622553)
                    ·
                      refine ⟨2280010717562355019966915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3040014290083140026622553 2280010717562355019966915)
                      ·
                        rfl

theorem cell23_4440305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 4, 2].length) (baseStart_4440305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440305 prefixEnd_4440305 := by exact prefixLift 4440305
  have htrace : WordTrace (prefixWord ++ tailWord_4440305) baseStart_4440305 baseEnd_4440305 := by
    simpa [prefixWord, tailWord_4440305, baseEnd_4440305] using wordTrace_append hprefix tailTrace_4440305
  have hstable : (prefixWord ++ tailWord_4440305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440305).length < 2 ^ (prefixWord ++ tailWord_4440305).sum := by decide
  have hdescent : baseEnd_4440305 < baseStart_4440305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440311 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 12]
def baseStart_4440311 : Nat := 118140960795 + 4440311 * 2 ^ 59
def prefixEnd_4440311 : Nat := 4983230072969 + 3 ^ 40 * 4440311 * 2
def baseEnd_4440311 : Nat := 253334866494031332943543

theorem tailTrace_4440311 : CollatzResearch.WordTrace tailWord_4440311 prefixEnd_4440311 253334866494031332943543 := by
  unfold tailWord_4440311
  simp only [CollatzResearch.WordTrace]
  refine ⟨161951447016519066589000787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107967631344346044392667191 161951447016519066589000787)
  ·
    refine ⟨242927170524778599883501181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161951447016519066589000787 242927170524778599883501181)
    ·
      refine ⟨91097688946791974956312943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 242927170524778599883501181 91097688946791974956312943)
      ·
        refine ⟨136646533420187962434469415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91097688946791974956312943 136646533420187962434469415)
        ·
          refine ⟨204969800130281943651704123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136646533420187962434469415 204969800130281943651704123)
          ·
            refine ⟨307454700195422915477556185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204969800130281943651704123 307454700195422915477556185)
            ·
              refine ⟨230591025146567186608167139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 307454700195422915477556185 230591025146567186608167139)
              ·
                refine ⟨345886537719850779912250709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 230591025146567186608167139 345886537719850779912250709)
                ·
                  refine ⟨253334866494031332943543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 345886537719850779912250709 253334866494031332943543)
                  ·
                    rfl

theorem cell23_4440311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 12].length) (baseStart_4440311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440311 prefixEnd_4440311 := by exact prefixLift 4440311
  have htrace : WordTrace (prefixWord ++ tailWord_4440311) baseStart_4440311 baseEnd_4440311 := by
    simpa [prefixWord, tailWord_4440311, baseEnd_4440311] using wordTrace_append hprefix tailTrace_4440311
  have hstable : (prefixWord ++ tailWord_4440311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440311).length < 2 ^ (prefixWord ++ tailWord_4440311).sum := by decide
  have hdescent : baseEnd_4440311 < baseStart_4440311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440328 : List Nat := [2, 1, 3, 2, 3, 1, 1, 2, 8]
def baseStart_4440328 : Nat := 118140960795 + 4440328 * 2 ^ 59
def prefixEnd_4440328 : Nat := 4983230072969 + 3 ^ 40 * 4440328 * 2
def baseEnd_4440328 : Nat := 253335836401934269997701

theorem tailTrace_4440328 : CollatzResearch.WordTrace tailWord_4440328 prefixEnd_4440328 253335836401934269997701 := by
  unfold tailWord_4440328
  simp only [CollatzResearch.WordTrace]
  refine ⟨80976033528728739246184819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107968044704971652328246425 80976033528728739246184819)
  ·
    refine ⟨121464050293093108869277229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80976033528728739246184819 121464050293093108869277229)
    ·
      refine ⟨45549018859909915825978961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121464050293093108869277229 45549018859909915825978961)
      ·
        refine ⟨34161764144932436869484221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45549018859909915825978961 34161764144932436869484221)
        ·
          refine ⟨12810661554349663826056583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34161764144932436869484221 12810661554349663826056583)
          ·
            refine ⟨19215992331524495739084875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12810661554349663826056583 19215992331524495739084875)
            ·
              refine ⟨28823988497286743608627313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19215992331524495739084875 28823988497286743608627313)
              ·
                refine ⟨21617991372965057706470485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28823988497286743608627313 21617991372965057706470485)
                ·
                  refine ⟨253335836401934269997701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21617991372965057706470485 253335836401934269997701)
                  ·
                    rfl

theorem cell23_4440328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 8].length) (baseStart_4440328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440328 prefixEnd_4440328 := by exact prefixLift 4440328
  have htrace : WordTrace (prefixWord ++ tailWord_4440328) baseStart_4440328 baseEnd_4440328 := by
    simpa [prefixWord, tailWord_4440328, baseEnd_4440328] using wordTrace_append hprefix tailTrace_4440328
  have hstable : (prefixWord ++ tailWord_4440328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440328).length < 2 ^ (prefixWord ++ tailWord_4440328).sum := by decide
  have hdescent : baseEnd_4440328 < baseStart_4440328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440349 : List Nat := [1, 4, 2, 3, 2, 2, 1, 1, 3, 4]
def baseStart_4440349 : Nat := 118140960795 + 4440349 * 2 ^ 59
def prefixEnd_4440349 : Nat := 4983230072969 + 3 ^ 40 * 4440349 * 2
def baseEnd_4440349 : Nat := 760011103570384282605571

theorem tailTrace_4440349 : CollatzResearch.WordTrace tailWord_4440349 prefixEnd_4440349 760011103570384282605571 := by
  unfold tailWord_4440349
  simp only [CollatzResearch.WordTrace]
  refine ⟨161952832990381399078884101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107968555326920932719256067 161952832990381399078884101)
  ·
    refine ⟨30366156185696512327290769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161952832990381399078884101 30366156185696512327290769)
    ·
      refine ⟨22774617139272384245468077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30366156185696512327290769 22774617139272384245468077)
      ·
        refine ⟨8540481427227144092050529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22774617139272384245468077 8540481427227144092050529)
        ·
          refine ⟨6405361070420358069037897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8540481427227144092050529 6405361070420358069037897)
          ·
            refine ⟨4804020802815268551778423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6405361070420358069037897 4804020802815268551778423)
            ·
              refine ⟨7206031204222902827667635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4804020802815268551778423 7206031204222902827667635)
              ·
                refine ⟨10809046806334354241501453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7206031204222902827667635 10809046806334354241501453)
                ·
                  refine ⟨4053392552375382840563045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10809046806334354241501453 4053392552375382840563045)
                  ·
                    refine ⟨760011103570384282605571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4053392552375382840563045 760011103570384282605571)
                    ·
                      rfl

theorem cell23_4440349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_4440349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440349 prefixEnd_4440349 := by exact prefixLift 4440349
  have htrace : WordTrace (prefixWord ++ tailWord_4440349) baseStart_4440349 baseEnd_4440349 := by
    simpa [prefixWord, tailWord_4440349, baseEnd_4440349] using wordTrace_append hprefix tailTrace_4440349
  have hstable : (prefixWord ++ tailWord_4440349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440349).length < 2 ^ (prefixWord ++ tailWord_4440349).sum := by decide
  have hdescent : baseEnd_4440349 < baseStart_4440349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440362 : List Nat := [3, 1, 4, 2, 2, 1, 1, 3, 6]
def baseStart_4440362 : Nat := 118140960795 + 4440362 * 2 ^ 59
def prefixEnd_4440362 : Nat := 4983230072969 + 3 ^ 40 * 4440362 * 2
def baseEnd_4440362 : Nat := 253337776217740144106017

theorem tailTrace_4440362 : CollatzResearch.WordTrace tailWord_4440362 prefixEnd_4440362 253337776217740144106017 := by
  unfold tailWord_4440362
  simp only [CollatzResearch.WordTrace]
  refine ⟨40488326784833575574776835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107968871426222868199404893 40488326784833575574776835)
  ·
    refine ⟨60732490177250363362165253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40488326784833575574776835 60732490177250363362165253)
    ·
      refine ⟨11387341908234443130405985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60732490177250363362165253 11387341908234443130405985)
      ·
        refine ⟨8540506431175832347804489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11387341908234443130405985 8540506431175832347804489)
        ·
          refine ⟨6405379823381874260853367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8540506431175832347804489 6405379823381874260853367)
          ·
            refine ⟨9608069735072811391280051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6405379823381874260853367 9608069735072811391280051)
            ·
              refine ⟨14412104602609217086920077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9608069735072811391280051 14412104602609217086920077)
              ·
                refine ⟨5404539225978456407595029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14412104602609217086920077 5404539225978456407595029)
                ·
                  refine ⟨253337776217740144106017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5404539225978456407595029 253337776217740144106017)
                  ·
                    rfl

theorem cell23_4440362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 6].length) (baseStart_4440362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440362 prefixEnd_4440362 := by exact prefixLift 4440362
  have htrace : WordTrace (prefixWord ++ tailWord_4440362) baseStart_4440362 baseEnd_4440362 := by
    simpa [prefixWord, tailWord_4440362, baseEnd_4440362] using wordTrace_append hprefix tailTrace_4440362
  have hstable : (prefixWord ++ tailWord_4440362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440362).length < 2 ^ (prefixWord ++ tailWord_4440362).sum := by decide
  have hdescent : baseEnd_4440362 < baseStart_4440362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440408 : List Nat := [2, 1, 2, 2, 1, 1, 2, 4, 1, 1, 6]
def baseStart_4440408 : Nat := 118140960795 + 4440408 * 2 ^ 59
def prefixEnd_4440408 : Nat := 4983230072969 + 3 ^ 40 * 4440408 * 2
def baseEnd_4440408 : Nat := 2280063606069768116978941

theorem tailTrace_4440408 : CollatzResearch.WordTrace tailWord_4440408 prefixEnd_4440408 2280063606069768116978941 := by
  unfold tailWord_4440408
  simp only [CollatzResearch.WordTrace]
  refine ⟨80977492448583826077640939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107969989931445101436854585 80977492448583826077640939)
  ·
    refine ⟨121466238672875739116461409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80977492448583826077640939 121466238672875739116461409)
    ·
      refine ⟨91099679004656804337346057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121466238672875739116461409 91099679004656804337346057)
      ·
        refine ⟨68324759253492603253009543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91099679004656804337346057 68324759253492603253009543)
        ·
          refine ⟨102487138880238904879514315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68324759253492603253009543 102487138880238904879514315)
          ·
            refine ⟨153730708320358357319271473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102487138880238904879514315 153730708320358357319271473)
            ·
              refine ⟨115298031240268767989453605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153730708320358357319271473 115298031240268767989453605)
              ·
                refine ⟨21618380857550393998022551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 115298031240268767989453605 21618380857550393998022551)
                ·
                  refine ⟨32427571286325590997033827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21618380857550393998022551 32427571286325590997033827)
                  ·
                    refine ⟨48641356929488386495550741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32427571286325590997033827 48641356929488386495550741)
                    ·
                      refine ⟨2280063606069768116978941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48641356929488386495550741 2280063606069768116978941)
                      ·
                        rfl

theorem cell23_4440408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_4440408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440408 prefixEnd_4440408 := by exact prefixLift 4440408
  have htrace : WordTrace (prefixWord ++ tailWord_4440408) baseStart_4440408 baseEnd_4440408 := by
    simpa [prefixWord, tailWord_4440408, baseEnd_4440408] using wordTrace_append hprefix tailTrace_4440408
  have hstable : (prefixWord ++ tailWord_4440408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440408).length < 2 ^ (prefixWord ++ tailWord_4440408).sum := by decide
  have hdescent : baseEnd_4440408 < baseStart_4440408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440415 : List Nat := [1, 1, 2, 3, 1, 2, 3, 2, 3, 2, 3]
def baseStart_4440415 : Nat := 118140960795 + 4440415 * 2 ^ 59
def prefixEnd_4440415 : Nat := 4983230072969 + 3 ^ 40 * 4440415 * 2
def baseEnd_4440415 : Nat := 2280067200434349589591409

theorem tailTrace_4440415 : CollatzResearch.WordTrace tailWord_4440415 prefixEnd_4440415 2280067200434349589591409 := by
  unfold tailWord_4440415
  simp only [CollatzResearch.WordTrace]
  refine ⟨161955240208142292350786699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107970160138761528233857799 161955240208142292350786699)
  ·
    refine ⟨242932860312213438526180049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161955240208142292350786699 242932860312213438526180049)
    ·
      refine ⟨182199645234160078894635037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242932860312213438526180049 182199645234160078894635037)
      ·
        refine ⟨68324866962810029585488139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182199645234160078894635037 68324866962810029585488139)
        ·
          refine ⟨102487300444215044378232209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68324866962810029585488139 102487300444215044378232209)
          ·
            refine ⟨76865475333161283283674157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102487300444215044378232209 76865475333161283283674157)
            ·
              refine ⟨28824553249935481231377809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76865475333161283283674157 28824553249935481231377809)
              ·
                refine ⟨21618414937451610923533357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28824553249935481231377809 21618414937451610923533357)
                ·
                  refine ⟨8106905601544354096325009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21618414937451610923533357 8106905601544354096325009)
                  ·
                    refine ⟨6080179201158265572243757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8106905601544354096325009 6080179201158265572243757)
                    ·
                      refine ⟨2280067200434349589591409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6080179201158265572243757 2280067200434349589591409)
                      ·
                        rfl

theorem cell23_4440415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_4440415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440415 prefixEnd_4440415 := by exact prefixLift 4440415
  have htrace : WordTrace (prefixWord ++ tailWord_4440415) baseStart_4440415 baseEnd_4440415 := by
    simpa [prefixWord, tailWord_4440415, baseEnd_4440415] using wordTrace_append hprefix tailTrace_4440415
  have hstable : (prefixWord ++ tailWord_4440415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440415).length < 2 ^ (prefixWord ++ tailWord_4440415).sum := by decide
  have hdescent : baseEnd_4440415 < baseStart_4440415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440425 : List Nat := [1, 2, 1, 1, 1, 3, 6, 1, 1, 2, 4]
def baseStart_4440425 : Nat := 118140960795 + 4440425 * 2 ^ 59
def prefixEnd_4440425 : Nat := 4983230072969 + 3 ^ 40 * 4440425 * 2
def baseEnd_4440425 : Nat := 2280072335240894550466363

theorem tailTrace_4440425 : CollatzResearch.WordTrace tailWord_4440425 prefixEnd_4440425 2280072335240894550466363 := by
  unfold tailWord_4440425
  simp only [CollatzResearch.WordTrace]
  refine ⟨161955604938106064058650729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107970403292070709372433819 161955604938106064058650729)
  ·
    refine ⟨121466703703579548043988047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161955604938106064058650729 121466703703579548043988047)
    ·
      refine ⟨182200055555369322065982071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121466703703579548043988047 182200055555369322065982071)
      ·
        refine ⟨273300083333053983098973107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182200055555369322065982071 273300083333053983098973107)
        ·
          refine ⟨409950124999580974648459661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273300083333053983098973107 409950124999580974648459661)
          ·
            refine ⟨153731296874842865493172373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 409950124999580974648459661 153731296874842865493172373)
            ·
              refine ⟨7206154541008259319992455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 153731296874842865493172373 7206154541008259319992455)
              ·
                refine ⟨10809231811512388979988683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7206154541008259319992455 10809231811512388979988683)
                ·
                  refine ⟨16213847717268583469983025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10809231811512388979988683 16213847717268583469983025)
                  ·
                    refine ⟨12160385787951437602487269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16213847717268583469983025 12160385787951437602487269)
                    ·
                      refine ⟨2280072335240894550466363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12160385787951437602487269 2280072335240894550466363)
                      ·
                        rfl

theorem cell23_4440425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 2, 4].length) (baseStart_4440425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440425 prefixEnd_4440425 := by exact prefixLift 4440425
  have htrace : WordTrace (prefixWord ++ tailWord_4440425) baseStart_4440425 baseEnd_4440425 := by
    simpa [prefixWord, tailWord_4440425, baseEnd_4440425] using wordTrace_append hprefix tailTrace_4440425
  have hstable : (prefixWord ++ tailWord_4440425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440425).length < 2 ^ (prefixWord ++ tailWord_4440425).sum := by decide
  have hdescent : baseEnd_4440425 < baseStart_4440425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440429 : List Nat := [1, 5, 1, 1, 1, 2, 3, 2, 3, 2, 2]
def baseStart_4440429 : Nat := 118140960795 + 4440429 * 2 ^ 59
def prefixEnd_4440429 : Nat := 4983230072969 + 3 ^ 40 * 4440429 * 2
def baseEnd_4440429 : Nat := 2280074389163512534816345

theorem tailTrace_4440429 : CollatzResearch.WordTrace tailWord_4440429 prefixEnd_4440429 2280074389163512534816345 := by
  unfold tailWord_4440429
  simp only [CollatzResearch.WordTrace]
  refine ⟨161955750830091572741796341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107970500553394381827864227 161955750830091572741796341)
  ·
    refine ⟨15183351640321084944543407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 161955750830091572741796341 15183351640321084944543407)
    ·
      refine ⟨22775027460481627416815111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15183351640321084944543407 22775027460481627416815111)
      ·
        refine ⟨34162541190722441125222667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22775027460481627416815111 34162541190722441125222667)
        ·
          refine ⟨51243811786083661687834001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34162541190722441125222667 51243811786083661687834001)
          ·
            refine ⟨38432858839562746265875501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51243811786083661687834001 38432858839562746265875501)
            ·
              refine ⟨14412322064836029849703313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38432858839562746265875501 14412322064836029849703313)
              ·
                refine ⟨10809241548627022387277485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14412322064836029849703313 10809241548627022387277485)
                ·
                  refine ⟨4053465580735133395229057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10809241548627022387277485 4053465580735133395229057)
                  ·
                    refine ⟨3040099185551350046421793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4053465580735133395229057 3040099185551350046421793)
                    ·
                      refine ⟨2280074389163512534816345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3040099185551350046421793 2280074389163512534816345)
                      ·
                        rfl

theorem cell23_4440429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_4440429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440429 prefixEnd_4440429 := by exact prefixLift 4440429
  have htrace : WordTrace (prefixWord ++ tailWord_4440429) baseStart_4440429 baseEnd_4440429 := by
    simpa [prefixWord, tailWord_4440429, baseEnd_4440429] using wordTrace_append hprefix tailTrace_4440429
  have hstable : (prefixWord ++ tailWord_4440429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440429).length < 2 ^ (prefixWord ++ tailWord_4440429).sum := by decide
  have hdescent : baseEnd_4440429 < baseStart_4440429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440449 : List Nat := [1, 2, 4, 3, 1, 2, 1, 3, 1, 2, 3]
def baseStart_4440449 : Nat := 118140960795 + 4440449 * 2 ^ 59
def prefixEnd_4440449 : Nat := 4983230072969 + 3 ^ 40 * 4440449 * 2
def baseEnd_4440449 : Nat := 2280084658776602456566253

theorem tailTrace_4440449 : CollatzResearch.WordTrace tailWord_4440449 prefixEnd_4440449 2280084658776602456566253 := by
  unfold tailWord_4440449
  simp only [CollatzResearch.WordTrace]
  refine ⟨161956480290019116157524401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107970986860012744105016267 161956480290019116157524401)
  ·
    refine ⟨121467360217514337118143301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161956480290019116157524401 121467360217514337118143301)
    ·
      refine ⟨22775130040783938209651869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121467360217514337118143301 22775130040783938209651869)
      ·
        refine ⟨8540673765293976828619451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22775130040783938209651869 8540673765293976828619451)
        ·
          refine ⟨12811010647940965242929177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8540673765293976828619451 12811010647940965242929177)
          ·
            refine ⟨9608257985955723932196883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12811010647940965242929177 9608257985955723932196883)
            ·
              refine ⟨14412386978933585898295325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9608257985955723932196883 14412386978933585898295325)
              ·
                refine ⟨5404645117100094711860747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14412386978933585898295325 5404645117100094711860747)
                ·
                  refine ⟨8106967675650142067791121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5404645117100094711860747 8106967675650142067791121)
                  ·
                    refine ⟨6080225756737606550843341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8106967675650142067791121 6080225756737606550843341)
                    ·
                      refine ⟨2280084658776602456566253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6080225756737606550843341 2280084658776602456566253)
                      ·
                        rfl

theorem cell23_4440449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_4440449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440449 prefixEnd_4440449 := by exact prefixLift 4440449
  have htrace : WordTrace (prefixWord ++ tailWord_4440449) baseStart_4440449 baseEnd_4440449 := by
    simpa [prefixWord, tailWord_4440449, baseEnd_4440449] using wordTrace_append hprefix tailTrace_4440449
  have hstable : (prefixWord ++ tailWord_4440449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440449).length < 2 ^ (prefixWord ++ tailWord_4440449).sum := by decide
  have hdescent : baseEnd_4440449 < baseStart_4440449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440505 : List Nat := [1, 2, 1, 4, 3, 1, 1, 1, 1, 3, 5]
def baseStart_4440505 : Nat := 118140960795 + 4440505 * 2 ^ 59
def prefixEnd_4440505 : Nat := 4983230072969 + 3 ^ 40 * 4440505 * 2
def baseEnd_4440505 : Nat := 2280113413693254237465995

theorem tailTrace_4440505 : CollatzResearch.WordTrace tailWord_4440505 prefixEnd_4440505 2280113413693254237465995 := by
  unfold tailWord_4440505
  simp only [CollatzResearch.WordTrace]
  refine ⟨161958522777816237721562969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107972348518544158481041979 161958522777816237721562969)
  ·
    refine ⟨121468892083362178291172227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161958522777816237721562969 121468892083362178291172227)
    ·
      refine ⟨182203338125043267436758341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121468892083362178291172227 182203338125043267436758341)
      ·
        refine ⟨34163125898445612644392189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 182203338125043267436758341 34163125898445612644392189)
        ·
          refine ⟨12811172211917104741647071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34163125898445612644392189 12811172211917104741647071)
          ·
            refine ⟨19216758317875657112470607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12811172211917104741647071 19216758317875657112470607)
            ·
              refine ⟨28825137476813485668705911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19216758317875657112470607 28825137476813485668705911)
              ·
                refine ⟨43237706215220228503058867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28825137476813485668705911 43237706215220228503058867)
                ·
                  refine ⟨64856559322830342754588301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43237706215220228503058867 64856559322830342754588301)
                  ·
                    refine ⟨24321209746061378532970613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64856559322830342754588301 24321209746061378532970613)
                    ·
                      refine ⟨2280113413693254237465995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24321209746061378532970613 2280113413693254237465995)
                      ·
                        rfl

theorem cell23_4440505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_4440505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440505 prefixEnd_4440505 := by exact prefixLift 4440505
  have htrace : WordTrace (prefixWord ++ tailWord_4440505) baseStart_4440505 baseEnd_4440505 := by
    simpa [prefixWord, tailWord_4440505, baseEnd_4440505] using wordTrace_append hprefix tailTrace_4440505
  have hstable : (prefixWord ++ tailWord_4440505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440505).length < 2 ^ (prefixWord ++ tailWord_4440505).sum := by decide
  have hdescent : baseEnd_4440505 < baseStart_4440505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440519 : List Nat := [1, 1, 4, 1, 1, 4, 2, 1, 4, 2, 2]
def baseStart_4440519 : Nat := 118140960795 + 4440519 * 2 ^ 59
def prefixEnd_4440519 : Nat := 4983230072969 + 3 ^ 40 * 4440519 * 2
def baseEnd_4440519 : Nat := 2280120602422417182690931

theorem tailTrace_4440519 : CollatzResearch.WordTrace tailWord_4440519 prefixEnd_4440519 2280120602422417182690931 := by
  unfold tailWord_4440519
  simp only [CollatzResearch.WordTrace]
  refine ⟨161959033399765518112572611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107972688933177012075048407 161959033399765518112572611)
  ·
    refine ⟨242938550099648277168858917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161959033399765518112572611 242938550099648277168858917)
    ·
      refine ⟨45550978143684051969161047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 242938550099648277168858917 45550978143684051969161047)
      ·
        refine ⟨68326467215526077953741571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45550978143684051969161047 68326467215526077953741571)
        ·
          refine ⟨102489700823289116930612357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68326467215526077953741571 102489700823289116930612357)
          ·
            refine ⟨19216818904366709424489817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102489700823289116930612357 19216818904366709424489817)
            ·
              refine ⟨14412614178275032068367363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19216818904366709424489817 14412614178275032068367363)
              ·
                refine ⟨21618921267412548102551045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14412614178275032068367363 21618921267412548102551045)
                ·
                  refine ⟨4053547737639852769228321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21618921267412548102551045 4053547737639852769228321)
                  ·
                    refine ⟨3040160803229889576921241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4053547737639852769228321 3040160803229889576921241)
                    ·
                      refine ⟨2280120602422417182690931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3040160803229889576921241 2280120602422417182690931)
                      ·
                        rfl

theorem cell23_4440519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 4, 2, 2].length) (baseStart_4440519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440519 prefixEnd_4440519 := by exact prefixLift 4440519
  have htrace : WordTrace (prefixWord ++ tailWord_4440519) baseStart_4440519 baseEnd_4440519 := by
    simpa [prefixWord, tailWord_4440519, baseEnd_4440519] using wordTrace_append hprefix tailTrace_4440519
  have hstable : (prefixWord ++ tailWord_4440519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440519).length < 2 ^ (prefixWord ++ tailWord_4440519).sum := by decide
  have hdescent : baseEnd_4440519 < baseStart_4440519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440530 : List Nat := [3, 2, 2, 4, 1, 2, 2, 1, 2, 1, 3]
def baseStart_4440530 : Nat := 118140960795 + 4440530 * 2 ^ 59
def prefixEnd_4440530 : Nat := 4983230072969 + 3 ^ 40 * 4440530 * 2
def baseEnd_4440530 : Nat := 2280126250709616639653381

theorem tailTrace_4440530 : CollatzResearch.WordTrace tailWord_4440530 prefixEnd_4440530 2280126250709616639653381 := by
  unfold tailWord_4440530
  simp only [CollatzResearch.WordTrace]
  refine ⟨40489858650681416747805761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107972956401817111327482029 40489858650681416747805761)
  ·
    refine ⟨30367393988011062560854321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40489858650681416747805761 30367393988011062560854321)
    ·
      refine ⟨22775545491008296920640741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30367393988011062560854321 22775545491008296920640741)
      ·
        refine ⟨4270414779564055672620139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22775545491008296920640741 4270414779564055672620139)
        ·
          refine ⟨6405622169346083508930209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4270414779564055672620139 6405622169346083508930209)
          ·
            refine ⟨4804216627009562631697657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6405622169346083508930209 4804216627009562631697657)
            ·
              refine ⟨3603162470257171973773243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4804216627009562631697657 3603162470257171973773243)
              ·
                refine ⟨5404743705385757960659865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3603162470257171973773243 5404743705385757960659865)
                ·
                  refine ⟨4053557779039318470494899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5404743705385757960659865 4053557779039318470494899)
                  ·
                    refine ⟨6080336668558977705742349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4053557779039318470494899 6080336668558977705742349)
                    ·
                      refine ⟨2280126250709616639653381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6080336668558977705742349 2280126250709616639653381)
                      ·
                        rfl

theorem cell23_4440530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_4440530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440530 prefixEnd_4440530 := by exact prefixLift 4440530
  have htrace : WordTrace (prefixWord ++ tailWord_4440530) baseStart_4440530 baseEnd_4440530 := by
    simpa [prefixWord, tailWord_4440530, baseEnd_4440530] using wordTrace_append hprefix tailTrace_4440530
  have hstable : (prefixWord ++ tailWord_4440530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440530).length < 2 ^ (prefixWord ++ tailWord_4440530).sum := by decide
  have hdescent : baseEnd_4440530 < baseStart_4440530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440602 : List Nat := [3, 1, 1, 3, 1, 1, 3, 1, 5, 4]
def baseStart_4440602 : Nat := 118140960795 + 4440602 * 2 ^ 59
def prefixEnd_4440602 : Nat := 4983230072969 + 3 ^ 40 * 4440602 * 2
def baseEnd_4440602 : Nat := 760054407105580119317683

theorem tailTrace_4440602 : CollatzResearch.WordTrace tailWord_4440602 prefixEnd_4440602 760054407105580119317683 := by
  unfold tailWord_4440602
  simp only [CollatzResearch.WordTrace]
  refine ⟨40490515164616205821961015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107974707105643215525229373 40490515164616205821961015)
  ·
    refine ⟨60735772746924308732941523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40490515164616205821961015 60735772746924308732941523)
    ·
      refine ⟨91103659120386463099412285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60735772746924308732941523 91103659120386463099412285)
      ·
        refine ⟨34163872170144923662279607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91103659120386463099412285 34163872170144923662279607)
        ·
          refine ⟨51245808255217385493419411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34163872170144923662279607 51245808255217385493419411)
          ·
            refine ⟨76868712382826078240129117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51245808255217385493419411 76868712382826078240129117)
            ·
              refine ⟨28825767143559779340048419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76868712382826078240129117 28825767143559779340048419)
              ·
                refine ⟨43238650715339669010072629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28825767143559779340048419 43238650715339669010072629)
                ·
                  refine ⟨4053623504563093969694309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43238650715339669010072629 4053623504563093969694309)
                  ·
                    refine ⟨760054407105580119317683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4053623504563093969694309 760054407105580119317683)
                    ·
                      rfl

theorem cell23_4440602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 5, 4].length) (baseStart_4440602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440602 prefixEnd_4440602 := by exact prefixLift 4440602
  have htrace : WordTrace (prefixWord ++ tailWord_4440602) baseStart_4440602 baseEnd_4440602 := by
    simpa [prefixWord, tailWord_4440602, baseEnd_4440602] using wordTrace_append hprefix tailTrace_4440602
  have hstable : (prefixWord ++ tailWord_4440602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440602).length < 2 ^ (prefixWord ++ tailWord_4440602).sum := by decide
  have hdescent : baseEnd_4440602 < baseStart_4440602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440636 : List Nat := [2, 2, 2, 2, 3, 1, 2, 4, 1, 4]
def baseStart_4440636 : Nat := 118140960795 + 4440636 * 2 ^ 59
def prefixEnd_4440636 : Nat := 4983230072969 + 3 ^ 40 * 4440636 * 2
def baseEnd_4440636 : Nat := 760060226552997741642631

theorem tailTrace_4440636 : CollatzResearch.WordTrace tailWord_4440636 prefixEnd_4440636 760060226552997741642631 := by
  unfold tailWord_4440636
  simp only [CollatzResearch.WordTrace]
  refine ⟨80981650370170823547290881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107975533826894431396387841 80981650370170823547290881)
  ·
    refine ⟨60736237777628117660468161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80981650370170823547290881 60736237777628117660468161)
    ·
      refine ⟨45552178333221088245351121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60736237777628117660468161 45552178333221088245351121)
      ·
        refine ⟨34164133749915816184013341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45552178333221088245351121 34164133749915816184013341)
        ·
          refine ⟨12811550156218431069005003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34164133749915816184013341 12811550156218431069005003)
          ·
            refine ⟨19217325234327646603507505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12811550156218431069005003 19217325234327646603507505)
            ·
              refine ⟨14412993925745734952630629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19217325234327646603507505 14412993925745734952630629)
              ·
                refine ⟨2702436361077325303618243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14412993925745734952630629 2702436361077325303618243)
                ·
                  refine ⟨4053654541615987955427365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2702436361077325303618243 4053654541615987955427365)
                  ·
                    refine ⟨760060226552997741642631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4053654541615987955427365 760060226552997741642631)
                    ·
                      rfl

theorem cell23_4440636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 4, 1, 4].length) (baseStart_4440636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440636 prefixEnd_4440636 := by exact prefixLift 4440636
  have htrace : WordTrace (prefixWord ++ tailWord_4440636) baseStart_4440636 baseEnd_4440636 := by
    simpa [prefixWord, tailWord_4440636, baseEnd_4440636] using wordTrace_append hprefix tailTrace_4440636
  have hstable : (prefixWord ++ tailWord_4440636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440636).length < 2 ^ (prefixWord ++ tailWord_4440636).sum := by decide
  have hdescent : baseEnd_4440636 < baseStart_4440636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440646 : List Nat := [6, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3]
def baseStart_4440646 : Nat := 118140960795 + 4440646 * 2 ^ 59
def prefixEnd_4440646 : Nat := 4983230072969 + 3 ^ 40 * 4440646 * 2
def baseEnd_4440646 : Nat := 2280185814465538185802847

theorem tailTrace_4440646 : CollatzResearch.WordTrace tailWord_4440646 prefixEnd_4440646 2280185814465538185802847 := by
  unfold tailWord_4440646
  simp only [CollatzResearch.WordTrace]
  refine ⟨5061364545947044337576431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 107975776980203612534963861 5061364545947044337576431)
  ·
    refine ⟨7592046818920566506364647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5061364545947044337576431 7592046818920566506364647)
    ·
      refine ⟨11388070228380849759546971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7592046818920566506364647 11388070228380849759546971)
      ·
        refine ⟨17082105342571274639320457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11388070228380849759546971 17082105342571274639320457)
        ·
          refine ⟨12811579006928455979490343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17082105342571274639320457 12811579006928455979490343)
          ·
            refine ⟨19217368510392683969235515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12811579006928455979490343 19217368510392683969235515)
            ·
              refine ⟨28826052765589025953853273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19217368510392683969235515 28826052765589025953853273)
              ·
                refine ⟨21619539574191769465389955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28826052765589025953853273 21619539574191769465389955)
                ·
                  refine ⟨32429309361287654198084933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21619539574191769465389955 32429309361287654198084933)
                  ·
                    refine ⟨6080495505241435162140925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32429309361287654198084933 6080495505241435162140925)
                    ·
                      refine ⟨2280185814465538185802847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6080495505241435162140925 2280185814465538185802847)
                      ·
                        rfl

theorem cell23_4440646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_4440646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440646 prefixEnd_4440646 := by exact prefixLift 4440646
  have htrace : WordTrace (prefixWord ++ tailWord_4440646) baseStart_4440646 baseEnd_4440646 := by
    simpa [prefixWord, tailWord_4440646, baseEnd_4440646] using wordTrace_append hprefix tailTrace_4440646
  have hstable : (prefixWord ++ tailWord_4440646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440646).length < 2 ^ (prefixWord ++ tailWord_4440646).sum := by decide
  have hdescent : baseEnd_4440646 < baseStart_4440646 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440655 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 7]
def baseStart_4440655 : Nat := 118140960795 + 4440655 * 2 ^ 59
def prefixEnd_4440655 : Nat := 4983230072969 + 3 ^ 40 * 4440655 * 2
def baseEnd_4440655 : Nat := 2280190435791428650590305

theorem tailTrace_4440655 : CollatzResearch.WordTrace tailWord_4440655 prefixEnd_4440655 2280190435791428650590305 := by
  unfold tailWord_4440655
  simp only [CollatzResearch.WordTrace]
  refine ⟨161963993727272813339523419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107975995818181875559682279 161963993727272813339523419)
  ·
    refine ⟨242945990590909220009285129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161963993727272813339523419 242945990590909220009285129)
    ·
      refine ⟨182209492943181915006963847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242945990590909220009285129 182209492943181915006963847)
      ·
        refine ⟨273314239414772872510445771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182209492943181915006963847 273314239414772872510445771)
        ·
          refine ⟨409971359122159308765668657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273314239414772872510445771 409971359122159308765668657)
          ·
            refine ⟨307478519341619481574251493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 409971359122159308765668657 307478519341619481574251493)
            ·
              refine ⟨57652222376553652795172155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 307478519341619481574251493 57652222376553652795172155)
              ·
                refine ⟨86478333564830479192758233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57652222376553652795172155 86478333564830479192758233)
                ·
                  refine ⟨64858750173622859394568675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86478333564830479192758233 64858750173622859394568675)
                  ·
                    refine ⟨97288125260434289091853013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 64858750173622859394568675 97288125260434289091853013)
                    ·
                      refine ⟨2280190435791428650590305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 97288125260434289091853013 2280190435791428650590305)
                      ·
                        rfl

theorem cell23_4440655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 7].length) (baseStart_4440655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440655 prefixEnd_4440655 := by exact prefixLift 4440655
  have htrace : WordTrace (prefixWord ++ tailWord_4440655) baseStart_4440655 baseEnd_4440655 := by
    simpa [prefixWord, tailWord_4440655, baseEnd_4440655] using wordTrace_append hprefix tailTrace_4440655
  have hstable : (prefixWord ++ tailWord_4440655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440655).length < 2 ^ (prefixWord ++ tailWord_4440655).sum := by decide
  have hdescent : baseEnd_4440655 < baseStart_4440655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440686 : List Nat := [4, 1, 2, 2, 2, 1, 1, 1, 4, 3, 2]
def baseStart_4440686 : Nat := 118140960795 + 4440686 * 2 ^ 59
def prefixEnd_4440686 : Nat := 4983230072969 + 3 ^ 40 * 4440686 * 2
def baseEnd_4440686 : Nat := 2280206353691718029302663

theorem tailTrace_4440686 : CollatzResearch.WordTrace tailWord_4440686 prefixEnd_4440686 2280206353691718029302663 := by
  unfold tailWord_4440686
  simp only [CollatzResearch.WordTrace]
  refine ⟨20245640548770063204237739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107976749593440337089267941 20245640548770063204237739)
  ·
    refine ⟨30368460823155094806356609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20245640548770063204237739 30368460823155094806356609)
    ·
      refine ⟨22776345617366321104767457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30368460823155094806356609 22776345617366321104767457)
      ·
        refine ⟨17082259213024740828575593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22776345617366321104767457 17082259213024740828575593)
        ·
          refine ⟨12811694409768555621431695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17082259213024740828575593 12811694409768555621431695)
          ·
            refine ⟨19217541614652833432147543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12811694409768555621431695 19217541614652833432147543)
            ·
              refine ⟨28826312421979250148221315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19217541614652833432147543 28826312421979250148221315)
              ·
                refine ⟨43239468632968875222331973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28826312421979250148221315 43239468632968875222331973)
                ·
                  refine ⟨8107400368681664104187245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43239468632968875222331973 8107400368681664104187245)
                  ·
                    refine ⟨3040275138255624039070217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8107400368681664104187245 3040275138255624039070217)
                    ·
                      refine ⟨2280206353691718029302663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3040275138255624039070217 2280206353691718029302663)
                      ·
                        rfl

theorem cell23_4440686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_4440686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440686 prefixEnd_4440686 := by exact prefixLift 4440686
  have htrace : WordTrace (prefixWord ++ tailWord_4440686) baseStart_4440686 baseEnd_4440686 := by
    simpa [prefixWord, tailWord_4440686, baseEnd_4440686] using wordTrace_append hprefix tailTrace_4440686
  have hstable : (prefixWord ++ tailWord_4440686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440686).length < 2 ^ (prefixWord ++ tailWord_4440686).sum := by decide
  have hdescent : baseEnd_4440686 < baseStart_4440686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440736 : List Nat := [2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 5]
def baseStart_4440736 : Nat := 118140960795 + 4440736 * 2 ^ 59
def prefixEnd_4440736 : Nat := 4983230072969 + 3 ^ 40 * 4440736 * 2
def baseEnd_4440736 : Nat := 2280232027724442833677433

theorem tailTrace_4440736 : CollatzResearch.WordTrace tailWord_4440736 prefixEnd_4440736 2280232027724442833677433 := by
  unfold tailWord_4440736
  simp only [CollatzResearch.WordTrace]
  refine ⟨80983474019989682086611031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107977965359986242782148041 80983474019989682086611031)
  ·
    refine ⟨121475211029984523129916547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80983474019989682086611031 121475211029984523129916547)
    ·
      refine ⟨182212816544976784694874821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121475211029984523129916547 182212816544976784694874821)
      ·
        refine ⟨34164903102183147130289029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 182212816544976784694874821 34164903102183147130289029)
        ·
          refine ⟨6405919331659340086929193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34164903102183147130289029 6405919331659340086929193)
          ·
            refine ⟨4804439498744505065196895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6405919331659340086929193 4804439498744505065196895)
            ·
              refine ⟨7206659248116757597795343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4804439498744505065196895 7206659248116757597795343)
              ·
                refine ⟨10809988872175136396693015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7206659248116757597795343 10809988872175136396693015)
                ·
                  refine ⟨16214983308262704595039523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10809988872175136396693015 16214983308262704595039523)
                  ·
                    refine ⟨24322474962394056892559285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16214983308262704595039523 24322474962394056892559285)
                    ·
                      refine ⟨2280232027724442833677433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24322474962394056892559285 2280232027724442833677433)
                      ·
                        rfl

theorem cell23_4440736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_4440736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440736 prefixEnd_4440736 := by exact prefixLift 4440736
  have htrace : WordTrace (prefixWord ++ tailWord_4440736) baseStart_4440736 baseEnd_4440736 := by
    simpa [prefixWord, tailWord_4440736, baseEnd_4440736] using wordTrace_append hprefix tailTrace_4440736
  have hstable : (prefixWord ++ tailWord_4440736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440736).length < 2 ^ (prefixWord ++ tailWord_4440736).sum := by decide
  have hdescent : baseEnd_4440736 < baseStart_4440736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440766 : List Nat := [4, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3]
def baseStart_4440766 : Nat := 118140960795 + 4440766 * 2 ^ 59
def prefixEnd_4440766 : Nat := 4983230072969 + 3 ^ 40 * 4440766 * 2
def baseEnd_4440766 : Nat := 2280247432144077716302295

theorem tailTrace_4440766 : CollatzResearch.WordTrace tailWord_4440766 prefixEnd_4440766 2280247432144077716302295 := by
  unfold tailWord_4440766
  simp only [CollatzResearch.WordTrace]
  refine ⟨20246005278733834912101769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107978694819913786197876101 20246005278733834912101769)
  ·
    refine ⟨15184503959050376184076327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20246005278733834912101769 15184503959050376184076327)
    ·
      refine ⟨22776755938575564276114491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15184503959050376184076327 22776755938575564276114491)
      ·
        refine ⟨34165133907863346414171737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22776755938575564276114491 34165133907863346414171737)
        ·
          refine ⟨25623850430897509810628803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34165133907863346414171737 25623850430897509810628803)
          ·
            refine ⟨38435775646346264715943205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25623850430897509810628803 38435775646346264715943205)
            ·
              refine ⟨7206707933689924634239351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38435775646346264715943205 7206707933689924634239351)
              ·
                refine ⟨10810061900534886951359027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7206707933689924634239351 10810061900534886951359027)
                ·
                  refine ⟨16215092850802330427038541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10810061900534886951359027 16215092850802330427038541)
                  ·
                    refine ⟨6080659819050873910139453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16215092850802330427038541 6080659819050873910139453)
                    ·
                      refine ⟨2280247432144077716302295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6080659819050873910139453 2280247432144077716302295)
                      ·
                        rfl

theorem cell23_4440766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_4440766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440766 prefixEnd_4440766 := by exact prefixLift 4440766
  have htrace : WordTrace (prefixWord ++ tailWord_4440766) baseStart_4440766 baseEnd_4440766 := by
    simpa [prefixWord, tailWord_4440766, baseEnd_4440766] using wordTrace_append hprefix tailTrace_4440766
  have hstable : (prefixWord ++ tailWord_4440766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440766).length < 2 ^ (prefixWord ++ tailWord_4440766).sum := by decide
  have hdescent : baseEnd_4440766 < baseStart_4440766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440776 : List Nat := [2, 1, 3, 1, 2, 3, 2, 1, 3, 3, 2]
def baseStart_4440776 : Nat := 118140960795 + 4440776 * 2 ^ 59
def prefixEnd_4440776 : Nat := 4983230072969 + 3 ^ 40 * 4440776 * 2
def baseEnd_4440776 : Nat := 2280252566950622677177249

theorem tailTrace_4440776 : CollatzResearch.WordTrace tailWord_4440776 prefixEnd_4440776 2280252566950622677177249 := by
  unfold tailWord_4440776
  simp only [CollatzResearch.WordTrace]
  refine ⟨80984203479917225502339091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107978937973222967336452121 80984203479917225502339091)
  ·
    refine ⟨121476305219875838253508637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80984203479917225502339091 121476305219875838253508637)
    ·
      refine ⟨45553614457453439345065739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121476305219875838253508637 45553614457453439345065739)
      ·
        refine ⟨68330421686180159017598609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45553614457453439345065739 68330421686180159017598609)
        ·
          refine ⟨51247816264635119263198957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68330421686180159017598609 51247816264635119263198957)
          ·
            refine ⟨19217931099238169723699609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51247816264635119263198957 19217931099238169723699609)
            ·
              refine ⟨14413448324428627292774707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19217931099238169723699609 14413448324428627292774707)
              ·
                refine ⟨21620172486642940939162061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14413448324428627292774707 21620172486642940939162061)
                ·
                  refine ⟨8107564682491102852185773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21620172486642940939162061 8107564682491102852185773)
                  ·
                    refine ⟨3040336755934163569569665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8107564682491102852185773 3040336755934163569569665)
                    ·
                      refine ⟨2280252566950622677177249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3040336755934163569569665 2280252566950622677177249)
                      ·
                        rfl

theorem cell23_4440776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 3, 3, 2].length) (baseStart_4440776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440776 prefixEnd_4440776 := by exact prefixLift 4440776
  have htrace : WordTrace (prefixWord ++ tailWord_4440776) baseStart_4440776 baseEnd_4440776 := by
    simpa [prefixWord, tailWord_4440776, baseEnd_4440776] using wordTrace_append hprefix tailTrace_4440776
  have hstable : (prefixWord ++ tailWord_4440776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440776).length < 2 ^ (prefixWord ++ tailWord_4440776).sum := by decide
  have hdescent : baseEnd_4440776 < baseStart_4440776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440863 : List Nat := [1, 1, 2, 4, 2, 3, 3, 2, 5]
def baseStart_4440863 : Nat := 118140960795 + 4440863 * 2 ^ 59
def prefixEnd_4440863 : Nat := 4983230072969 + 3 ^ 40 * 4440863 * 2
def baseEnd_4440863 : Nat := 253366359974173759643261

theorem tailTrace_4440863 : CollatzResearch.WordTrace tailWord_4440863 prefixEnd_4440863 253366359974173759643261 := by
  unfold tailWord_4440863
  simp only [CollatzResearch.WordTrace]
  refine ⟨161971580110519264863095243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107981053407012843242063495 161971580110519264863095243)
  ·
    refine ⟨242957370165778897294642865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161971580110519264863095243 242957370165778897294642865)
    ·
      refine ⟨182218027624334172970982149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242957370165778897294642865 182218027624334172970982149)
      ·
        refine ⟨34165880179562657432059153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 182218027624334172970982149 34165880179562657432059153)
        ·
          refine ⟨25624410134671993074044365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34165880179562657432059153 25624410134671993074044365)
          ·
            refine ⟨9609153800501997402766637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25624410134671993074044365 9609153800501997402766637)
            ·
              refine ⟨3603432675188249026037489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9609153800501997402766637 3603432675188249026037489)
              ·
                refine ⟨2702574506391186769528117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3603432675188249026037489 2702574506391186769528117)
                ·
                  refine ⟨253366359974173759643261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2702574506391186769528117 253366359974173759643261)
                  ·
                    rfl

theorem cell23_4440863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 2, 5].length) (baseStart_4440863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440863 prefixEnd_4440863 := by exact prefixLift 4440863
  have htrace : WordTrace (prefixWord ++ tailWord_4440863) baseStart_4440863 baseEnd_4440863 := by
    simpa [prefixWord, tailWord_4440863, baseEnd_4440863] using wordTrace_append hprefix tailTrace_4440863
  have hstable : (prefixWord ++ tailWord_4440863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440863).length < 2 ^ (prefixWord ++ tailWord_4440863).sum := by decide
  have hdescent : baseEnd_4440863 < baseStart_4440863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440869 : List Nat := [1, 3, 1, 2, 3, 1, 3, 1, 1, 2, 5]
def baseStart_4440869 : Nat := 118140960795 + 4440869 * 2 ^ 59
def prefixEnd_4440869 : Nat := 4983230072969 + 3 ^ 40 * 4440869 * 2
def baseEnd_4440869 : Nat := 2280300320651490813314321

theorem tailTrace_4440869 : CollatzResearch.WordTrace tailWord_4440869 prefixEnd_4440869 2280300320651490813314321 := by
  unfold tailWord_4440869
  simp only [CollatzResearch.WordTrace]
  refine ⟨161971798948497527887813661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107981199298998351925209107 161971798948497527887813661)
  ·
    refine ⟨60739424605686572957930123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161971798948497527887813661 60739424605686572957930123)
    ·
      refine ⟨91109136908529859436895185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60739424605686572957930123 91109136908529859436895185)
      ·
        refine ⟨68331852681397394577671389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91109136908529859436895185 68331852681397394577671389)
        ·
          refine ⟨25624444755524022966626771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68331852681397394577671389 25624444755524022966626771)
          ·
            refine ⟨38436667133286034449940157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25624444755524022966626771 38436667133286034449940157)
            ·
              refine ⟨14413750174982262918727559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38436667133286034449940157 14413750174982262918727559)
              ·
                refine ⟨21620625262473394378091339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14413750174982262918727559 21620625262473394378091339)
                ·
                  refine ⟨32430937893710091567137009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21620625262473394378091339 32430937893710091567137009)
                  ·
                    refine ⟨24323203420282568675352757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32430937893710091567137009 24323203420282568675352757)
                    ·
                      refine ⟨2280300320651490813314321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24323203420282568675352757 2280300320651490813314321)
                      ·
                        rfl

theorem cell23_4440869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_4440869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440869 prefixEnd_4440869 := by exact prefixLift 4440869
  have htrace : WordTrace (prefixWord ++ tailWord_4440869) baseStart_4440869 baseEnd_4440869 := by
    simpa [prefixWord, tailWord_4440869, baseEnd_4440869] using wordTrace_append hprefix tailTrace_4440869
  have hstable : (prefixWord ++ tailWord_4440869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440869).length < 2 ^ (prefixWord ++ tailWord_4440869).sum := by decide
  have hdescent : baseEnd_4440869 < baseStart_4440869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440893 : List Nat := [1, 4, 1, 4, 2, 1, 2, 1, 2, 5]
def baseStart_4440893 : Nat := 118140960795 + 4440893 * 2 ^ 59
def prefixEnd_4440893 : Nat := 4983230072969 + 3 ^ 40 * 4440893 * 2
def baseEnd_4440893 : Nat := 760104214729066239804737

theorem tailTrace_4440893 : CollatzResearch.WordTrace tailWord_4440893 prefixEnd_4440893 760104214729066239804737 := by
  unfold tailWord_4440893
  simp only [CollatzResearch.WordTrace]
  refine ⟨161972674300410579986687333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107981782866940386657791555 161972674300410579986687333)
  ·
    refine ⟨30369876431326983747503875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161972674300410579986687333 30369876431326983747503875)
    ·
      refine ⟨45554814646990475621255813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30369876431326983747503875 45554814646990475621255813)
      ·
        refine ⟨8541527746310714178985465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45554814646990475621255813 8541527746310714178985465)
        ·
          refine ⟨6406145809733035634239099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8541527746310714178985465 6406145809733035634239099)
          ·
            refine ⟨9609218714599553451358649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6406145809733035634239099 9609218714599553451358649)
            ·
              refine ⟨7206914035949665088518987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9609218714599553451358649 7206914035949665088518987)
              ·
                refine ⟨10810371053924497632778481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7206914035949665088518987 10810371053924497632778481)
                ·
                  refine ⟨8107778290443373224583861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10810371053924497632778481 8107778290443373224583861)
                  ·
                    refine ⟨760104214729066239804737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8107778290443373224583861 760104214729066239804737)
                    ·
                      rfl

theorem cell23_4440893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_4440893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440893 prefixEnd_4440893 := by exact prefixLift 4440893
  have htrace : WordTrace (prefixWord ++ tailWord_4440893) baseStart_4440893 baseEnd_4440893 := by
    simpa [prefixWord, tailWord_4440893, baseEnd_4440893] using wordTrace_append hprefix tailTrace_4440893
  have hstable : (prefixWord ++ tailWord_4440893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440893).length < 2 ^ (prefixWord ++ tailWord_4440893).sum := by decide
  have hdescent : baseEnd_4440893 < baseStart_4440893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440930 : List Nat := [3, 3, 2, 1, 3, 1, 1, 1, 2, 4, 2]
def baseStart_4440930 : Nat := 118140960795 + 4440930 * 2 ^ 59
def prefixEnd_4440930 : Nat := 4983230072969 + 3 ^ 40 * 4440930 * 2
def baseEnd_4440930 : Nat := 2280331642971415074651541

theorem tailTrace_4440930 : CollatzResearch.WordTrace tailWord_4440930 prefixEnd_4440930 2280331642971415074651541 := by
  unfold tailWord_4440930
  simp only [CollatzResearch.WordTrace]
  refine ⟨40493505950319133826446061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107982682534184356870522829 40493505950319133826446061)
  ·
    refine ⟨15185064731369675184917273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40493505950319133826446061 15185064731369675184917273)
    ·
      refine ⟨11388798548527256388687955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15185064731369675184917273 11388798548527256388687955)
      ·
        refine ⟨17083197822790884583031933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11388798548527256388687955 17083197822790884583031933)
        ·
          refine ⟨6406199183546581718636975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17083197822790884583031933 6406199183546581718636975)
          ·
            refine ⟨9609298775319872577955463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6406199183546581718636975 9609298775319872577955463)
            ·
              refine ⟨14413948162979808866933195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9609298775319872577955463 14413948162979808866933195)
              ·
                refine ⟨21620922244469713300399793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14413948162979808866933195 21620922244469713300399793)
                ·
                  refine ⟨16215691683352284975299845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21620922244469713300399793 16215691683352284975299845)
                  ·
                    refine ⟨3040442190628553432868721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16215691683352284975299845 3040442190628553432868721)
                    ·
                      refine ⟨2280331642971415074651541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3040442190628553432868721 2280331642971415074651541)
                      ·
                        rfl

theorem cell23_4440930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_4440930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440930 prefixEnd_4440930 := by exact prefixLift 4440930
  have htrace : WordTrace (prefixWord ++ tailWord_4440930) baseStart_4440930 baseEnd_4440930 := by
    simpa [prefixWord, tailWord_4440930, baseEnd_4440930] using wordTrace_append hprefix tailTrace_4440930
  have hstable : (prefixWord ++ tailWord_4440930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440930).length < 2 ^ (prefixWord ++ tailWord_4440930).sum := by decide
  have hdescent : baseEnd_4440930 < baseStart_4440930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440936 : List Nat := [2, 1, 4, 2, 1, 2, 2, 3, 6]
def baseStart_4440936 : Nat := 118140960795 + 4440936 * 2 ^ 59
def prefixEnd_4440936 : Nat := 4983230072969 + 3 ^ 40 * 4440936 * 2
def baseEnd_4440936 : Nat := 253370524872815783464057

theorem tailTrace_4440936 : CollatzResearch.WordTrace tailWord_4440936 prefixEnd_4440936 253370524872815783464057 := by
  unfold tailWord_4440936
  simp only [CollatzResearch.WordTrace]
  refine ⟨80987121319627399165251331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107982828426169865553668441 80987121319627399165251331)
  ·
    refine ⟨121480681979441098747876997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80987121319627399165251331 121480681979441098747876997)
    ·
      refine ⟨22777627871145206015226937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121480681979441098747876997 22777627871145206015226937)
      ·
        refine ⟨17083220903358904511420203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22777627871145206015226937 17083220903358904511420203)
        ·
          refine ⟨25624831355038356767130305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17083220903358904511420203 25624831355038356767130305)
          ·
            refine ⟨19218623516278767575347729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25624831355038356767130305 19218623516278767575347729)
            ·
              refine ⟨14413967637209075681510797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19218623516278767575347729 14413967637209075681510797)
              ·
                refine ⟨5405237863953403380566549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14413967637209075681510797 5405237863953403380566549)
                ·
                  refine ⟨253370524872815783464057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5405237863953403380566549 253370524872815783464057)
                  ·
                    rfl

theorem cell23_4440936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 6].length) (baseStart_4440936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440936 prefixEnd_4440936 := by exact prefixLift 4440936
  have htrace : WordTrace (prefixWord ++ tailWord_4440936) baseStart_4440936 baseEnd_4440936 := by
    simpa [prefixWord, tailWord_4440936, baseEnd_4440936] using wordTrace_append hprefix tailTrace_4440936
  have hstable : (prefixWord ++ tailWord_4440936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440936).length < 2 ^ (prefixWord ++ tailWord_4440936).sum := by decide
  have hdescent : baseEnd_4440936 < baseStart_4440936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440950 : List Nat := [5, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3]
def baseStart_4440950 : Nat := 118140960795 + 4440950 * 2 ^ 59
def prefixEnd_4440950 : Nat := 4983230072969 + 3 ^ 40 * 4440950 * 2
def baseEnd_4440950 : Nat := 2280341912584504996401449

theorem tailTrace_4440950 : CollatzResearch.WordTrace tailWord_4440950 prefixEnd_4440950 2280341912584504996401449 := by
  unfold tailWord_4440950
  simp only [CollatzResearch.WordTrace]
  refine ⟨10123422078825254920094519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107983168840802719147674869 10123422078825254920094519)
  ·
    refine ⟨15185133118237882380141779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10123422078825254920094519 15185133118237882380141779)
    ·
      refine ⟨22777699677356823570212669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15185133118237882380141779 22777699677356823570212669)
      ·
        refine ⟨8541637379008808838829751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22777699677356823570212669 8541637379008808838829751)
        ·
          refine ⟨12812456068513213258244627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8541637379008808838829751 12812456068513213258244627)
          ·
            refine ⟨19218684102769819887366941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12812456068513213258244627 19218684102769819887366941)
            ·
              refine ⟨7207006538538682457762603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19218684102769819887366941 7207006538538682457762603)
              ·
                refine ⟨10810509807808023686643905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7207006538538682457762603 10810509807808023686643905)
                ·
                  refine ⟨8107882355856017764982929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10810509807808023686643905 8107882355856017764982929)
                  ·
                    refine ⟨6080911766892013323737197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8107882355856017764982929 6080911766892013323737197)
                    ·
                      refine ⟨2280341912584504996401449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6080911766892013323737197 2280341912584504996401449)
                      ·
                        rfl

theorem cell23_4440950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_4440950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440950 prefixEnd_4440950 := by exact prefixLift 4440950
  have htrace : WordTrace (prefixWord ++ tailWord_4440950) baseStart_4440950 baseEnd_4440950 := by
    simpa [prefixWord, tailWord_4440950, baseEnd_4440950] using wordTrace_append hprefix tailTrace_4440950
  have hstable : (prefixWord ++ tailWord_4440950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440950).length < 2 ^ (prefixWord ++ tailWord_4440950).sum := by decide
  have hdescent : baseEnd_4440950 < baseStart_4440950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4440980 : List Nat := [2, 4, 2, 1, 1, 1, 4, 1, 3, 1, 3]
def baseStart_4440980 : Nat := 118140960795 + 4440980 * 2 ^ 59
def prefixEnd_4440980 : Nat := 4983230072969 + 3 ^ 40 * 4440980 * 2
def baseEnd_4440980 : Nat := 2280357317004139879026311

theorem tailTrace_4440980 : CollatzResearch.WordTrace tailWord_4440980 prefixEnd_4440980 2280357317004139879026311 := by
  unfold tailWord_4440980
  simp only [CollatzResearch.WordTrace]
  refine ⟨80987923725547696922552197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107983898300730262563402929 80987923725547696922552197)
  ·
    refine ⟨15185235698540193172978537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80987923725547696922552197 15185235698540193172978537)
    ·
      refine ⟨11388926773905144879733903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15185235698540193172978537 11388926773905144879733903)
      ·
        refine ⟨17083390160857717319600855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11388926773905144879733903 17083390160857717319600855)
        ·
          refine ⟨25625085241286575979401283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17083390160857717319600855 25625085241286575979401283)
          ·
            refine ⟨38437627861929863969101925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25625085241286575979401283 38437627861929863969101925)
            ·
              refine ⟨7207055224111849494206611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38437627861929863969101925 7207055224111849494206611)
              ·
                refine ⟨10810582836167774241309917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7207055224111849494206611 10810582836167774241309917)
                ·
                  refine ⟨4053968563562915340491219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10810582836167774241309917 4053968563562915340491219)
                  ·
                    refine ⟨6080952845344373010736829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4053968563562915340491219 6080952845344373010736829)
                    ·
                      refine ⟨2280357317004139879026311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6080952845344373010736829 2280357317004139879026311)
                      ·
                        rfl

theorem cell23_4440980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_4440980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4440980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4440980 prefixEnd_4440980 := by exact prefixLift 4440980
  have htrace : WordTrace (prefixWord ++ tailWord_4440980) baseStart_4440980 baseEnd_4440980 := by
    simpa [prefixWord, tailWord_4440980, baseEnd_4440980] using wordTrace_append hprefix tailTrace_4440980
  have hstable : (prefixWord ++ tailWord_4440980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4440980).length < 2 ^ (prefixWord ++ tailWord_4440980).sum := by decide
  have hdescent : baseEnd_4440980 < baseStart_4440980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4440980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441070 : List Nat := [4, 1, 2, 1, 4, 1, 1, 2, 1, 3, 3]
def baseStart_4441070 : Nat := 118140960795 + 4441070 * 2 ^ 59
def prefixEnd_4441070 : Nat := 4983230072969 + 3 ^ 40 * 4441070 * 2
def baseEnd_4441070 : Nat := 2280403530263044526900897

theorem tailTrace_4441070 : CollatzResearch.WordTrace tailWord_4441070 prefixEnd_4441070 2280403530263044526900897 := by
  unfold tailWord_4441070
  simp only [CollatzResearch.WordTrace]
  refine ⟨20247391252596167401985083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107986086680512892810587109 20247391252596167401985083)
  ·
    refine ⟨30371086878894251102977625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20247391252596167401985083 30371086878894251102977625)
    ·
      refine ⟨22778315159170688327233219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30371086878894251102977625 22778315159170688327233219)
      ·
        refine ⟨34167472738756032490849829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22778315159170688327233219 34167472738756032490849829)
        ·
          refine ⟨6406401138516756092034343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34167472738756032490849829 6406401138516756092034343)
          ·
            refine ⟨9609601707775134138051515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6406401138516756092034343 9609601707775134138051515)
            ·
              refine ⟨14414402561662701207077273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9609601707775134138051515 14414402561662701207077273)
              ·
                refine ⟨10810801921247025905307955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14414402561662701207077273 10810801921247025905307955)
                ·
                  refine ⟨16216202881870538857961933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10810801921247025905307955 16216202881870538857961933)
                  ·
                    refine ⟨6081076080701452071735725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16216202881870538857961933 6081076080701452071735725)
                    ·
                      refine ⟨2280403530263044526900897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6081076080701452071735725 2280403530263044526900897)
                      ·
                        rfl

theorem cell23_4441070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_4441070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441070 prefixEnd_4441070 := by exact prefixLift 4441070
  have htrace : WordTrace (prefixWord ++ tailWord_4441070) baseStart_4441070 baseEnd_4441070 := by
    simpa [prefixWord, tailWord_4441070, baseEnd_4441070] using wordTrace_append hprefix tailTrace_4441070
  have hstable : (prefixWord ++ tailWord_4441070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441070).length < 2 ^ (prefixWord ++ tailWord_4441070).sum := by decide
  have hdescent : baseEnd_4441070 < baseStart_4441070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441074 : List Nat := [3, 2, 1, 5, 1, 1, 3, 1, 1, 2, 3]
def baseStart_4441074 : Nat := 118140960795 + 4441074 * 2 ^ 59
def prefixEnd_4441074 : Nat := 4983230072969 + 3 ^ 40 * 4441074 * 2
def baseEnd_4441074 : Nat := 2280405584185662511250879

theorem tailTrace_4441074 : CollatzResearch.WordTrace tailWord_4441074 prefixEnd_4441074 2280405584185662511250879 := by
  unfold tailWord_4441074
  simp only [CollatzResearch.WordTrace]
  refine ⟨40494818978188711974756569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107986183941836565266017517 40494818978188711974756569)
  ·
    refine ⟨30371114233641533981067427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40494818978188711974756569 30371114233641533981067427)
    ·
      refine ⟨45556671350462300971601141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30371114233641533981067427 45556671350462300971601141)
      ·
        refine ⟨4270937939105840716087607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45556671350462300971601141 4270937939105840716087607)
        ·
          refine ⟨6406406908658761074131411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4270937939105840716087607 6406406908658761074131411)
          ·
            refine ⟨9609610362988141611197117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6406406908658761074131411 9609610362988141611197117)
            ·
              refine ⟨3603603886120553104198919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9609610362988141611197117 3603603886120553104198919)
              ·
                refine ⟨5405405829180829656298379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3603603886120553104198919 5405405829180829656298379)
                ·
                  refine ⟨8108108743771244484447569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5405405829180829656298379 8108108743771244484447569)
                  ·
                    refine ⟨6081081557828433363335677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8108108743771244484447569 6081081557828433363335677)
                    ·
                      refine ⟨2280405584185662511250879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6081081557828433363335677 2280405584185662511250879)
                      ·
                        rfl

theorem cell23_4441074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_4441074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441074 prefixEnd_4441074 := by exact prefixLift 4441074
  have htrace : WordTrace (prefixWord ++ tailWord_4441074) baseStart_4441074 baseEnd_4441074 := by
    simpa [prefixWord, tailWord_4441074, baseEnd_4441074] using wordTrace_append hprefix tailTrace_4441074
  have hstable : (prefixWord ++ tailWord_4441074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441074).length < 2 ^ (prefixWord ++ tailWord_4441074).sum := by decide
  have hdescent : baseEnd_4441074 < baseStart_4441074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441093 : List Nat := [1, 3, 1, 1, 2, 3, 1, 2, 3, 4, 2]
def baseStart_4441093 : Nat := 118140960795 + 4441093 * 2 ^ 59
def prefixEnd_4441093 : Nat := 4983230072969 + 3 ^ 40 * 4441093 * 2
def baseEnd_4441093 : Nat := 2280415340318097936913291

theorem tailTrace_4441093 : CollatzResearch.WordTrace tailWord_4441093 prefixEnd_4441093 2280415340318097936913291 := by
  unfold tailWord_4441093
  simp only [CollatzResearch.WordTrace]
  refine ⟨161979968899686014143967933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107986645933124009429311955 161979968899686014143967933)
  ·
    refine ⟨60742488337382255303987975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161979968899686014143967933 60742488337382255303987975)
    ·
      refine ⟨91113732506073382955981963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60742488337382255303987975 91113732506073382955981963)
      ·
        refine ⟨136670598759110074433972945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91113732506073382955981963 136670598759110074433972945)
        ·
          refine ⟨102502949069332555825479709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136670598759110074433972945 102502949069332555825479709)
          ·
            refine ⟨38438605900999708434554891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102502949069332555825479709 38438605900999708434554891)
            ·
              refine ⟨57657908851499562651832337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38438605900999708434554891 57657908851499562651832337)
              ·
                refine ⟨43243431638624671988874253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57657908851499562651832337 43243431638624671988874253)
                ·
                  refine ⟨16216286864484251995827845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43243431638624671988874253 16216286864484251995827845)
                  ·
                    refine ⟨3040553787090797249217721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16216286864484251995827845 3040553787090797249217721)
                    ·
                      refine ⟨2280415340318097936913291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3040553787090797249217721 2280415340318097936913291)
                      ·
                        rfl

theorem cell23_4441093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 4, 2].length) (baseStart_4441093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441093 prefixEnd_4441093 := by exact prefixLift 4441093
  have htrace : WordTrace (prefixWord ++ tailWord_4441093) baseStart_4441093 baseEnd_4441093 := by
    simpa [prefixWord, tailWord_4441093, baseEnd_4441093] using wordTrace_append hprefix tailTrace_4441093
  have hstable : (prefixWord ++ tailWord_4441093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441093).length < 2 ^ (prefixWord ++ tailWord_4441093).sum := by decide
  have hdescent : baseEnd_4441093 < baseStart_4441093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441127 : List Nat := [1, 1, 7, 1, 1, 1, 2, 2, 1, 4, 2]
def baseStart_4441127 : Nat := 118140960795 + 4441127 * 2 ^ 59
def prefixEnd_4441127 : Nat := 4983230072969 + 3 ^ 40 * 4441127 * 2
def baseEnd_4441127 : Nat := 2280432798660350803888135

theorem tailTrace_4441127 : CollatzResearch.WordTrace tailWord_4441127 prefixEnd_4441127 2280432798660350803888135 := by
  unfold tailWord_4441127
  simp only [CollatzResearch.WordTrace]
  refine ⟨161981208981562837950705635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107987472654375225300470423 161981208981562837950705635)
  ·
    refine ⟨242971813472344256926058453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161981208981562837950705635 242971813472344256926058453)
    ·
      refine ⟨5694651878258068521704495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 242971813472344256926058453 5694651878258068521704495)
      ·
        refine ⟨8541977817387102782556743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5694651878258068521704495 8541977817387102782556743)
        ·
          refine ⟨12812966726080654173835115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8541977817387102782556743 12812966726080654173835115)
          ·
            refine ⟨19219450089120981260752673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12812966726080654173835115 19219450089120981260752673)
            ·
              refine ⟨14414587566840735945564505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19219450089120981260752673 14414587566840735945564505)
              ·
                refine ⟨10810940675130551959173379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14414587566840735945564505 10810940675130551959173379)
                ·
                  refine ⟨16216411012695827938760069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10810940675130551959173379 16216411012695827938760069)
                  ·
                    refine ⟨3040577064880467738517513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16216411012695827938760069 3040577064880467738517513)
                    ·
                      refine ⟨2280432798660350803888135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3040577064880467738517513 2280432798660350803888135)
                      ·
                        rfl

theorem cell23_4441127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_4441127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441127 prefixEnd_4441127 := by exact prefixLift 4441127
  have htrace : WordTrace (prefixWord ++ tailWord_4441127) baseStart_4441127 baseEnd_4441127 := by
    simpa [prefixWord, tailWord_4441127, baseEnd_4441127] using wordTrace_append hprefix tailTrace_4441127
  have hstable : (prefixWord ++ tailWord_4441127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441127).length < 2 ^ (prefixWord ++ tailWord_4441127).sum := by decide
  have hdescent : baseEnd_4441127 < baseStart_4441127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441140 : List Nat := [2, 5, 1, 2, 1, 1, 1, 2, 2, 2, 4]
def baseStart_4441140 : Nat := 118140960795 + 4441140 * 2 ^ 59
def prefixEnd_4441140 : Nat := 4983230072969 + 3 ^ 40 * 4441140 * 2
def baseEnd_4441140 : Nat := 2280439473908859253025575

theorem tailTrace_4441140 : CollatzResearch.WordTrace tailWord_4441140 prefixEnd_4441140 2280439473908859253025575 := by
  unfold tailWord_4441140
  simp only [CollatzResearch.WordTrace]
  refine ⟨80990841565257870585464437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107987788753677160780619249 80990841565257870585464437)
  ·
    refine ⟨7592891396742925367387291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80990841565257870585464437 7592891396742925367387291)
    ·
      refine ⟨11389337095114388051080937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7592891396742925367387291 11389337095114388051080937)
      ·
        refine ⟨8542002821335791038310703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11389337095114388051080937 8542002821335791038310703)
        ·
          refine ⟨12813004232003686557466055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8542002821335791038310703 12813004232003686557466055)
          ·
            refine ⟨19219506348005529836199083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12813004232003686557466055 19219506348005529836199083)
            ·
              refine ⟨28829259522008294754298625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19219506348005529836199083 28829259522008294754298625)
              ·
                refine ⟨21621944641506221065723969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28829259522008294754298625 21621944641506221065723969)
                ·
                  refine ⟨16216458481129665799292977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21621944641506221065723969 16216458481129665799292977)
                  ·
                    refine ⟨12162343860847249349469733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16216458481129665799292977 12162343860847249349469733)
                    ·
                      refine ⟨2280439473908859253025575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12162343860847249349469733 2280439473908859253025575)
                      ·
                        rfl

theorem cell23_4441140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_4441140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441140 prefixEnd_4441140 := by exact prefixLift 4441140
  have htrace : WordTrace (prefixWord ++ tailWord_4441140) baseStart_4441140 baseEnd_4441140 := by
    simpa [prefixWord, tailWord_4441140, baseEnd_4441140] using wordTrace_append hprefix tailTrace_4441140
  have hstable : (prefixWord ++ tailWord_4441140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441140).length < 2 ^ (prefixWord ++ tailWord_4441140).sum := by decide
  have hdescent : baseEnd_4441140 < baseStart_4441140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441144 : List Nat := [2, 1, 2, 1, 5, 3, 1, 2, 2, 2, 2]
def baseStart_4441144 : Nat := 118140960795 + 4441144 * 2 ^ 59
def prefixEnd_4441144 : Nat := 4983230072969 + 3 ^ 40 * 4441144 * 2
def baseEnd_4441144 : Nat := 2280441527831477237375557

theorem tailTrace_4441144 : CollatzResearch.WordTrace tailWord_4441144 prefixEnd_4441144 2280441527831477237375557 := by
  unfold tailWord_4441144
  simp only [CollatzResearch.WordTrace]
  refine ⟨80990914511250624927037243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107987886015000833236049657 80990914511250624927037243)
  ·
    refine ⟨121486371766875937390555865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80990914511250624927037243 121486371766875937390555865)
    ·
      refine ⟨91114778825156953042916899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121486371766875937390555865 91114778825156953042916899)
      ·
        refine ⟨136672168237735429564375349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91114778825156953042916899 136672168237735429564375349)
        ·
          refine ⟨12813015772287696521660189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 136672168237735429564375349 12813015772287696521660189)
          ·
            refine ⟨4804880914607886195622571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12813015772287696521660189 4804880914607886195622571)
            ·
              refine ⟨7207321371911829293433857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4804880914607886195622571 7207321371911829293433857)
              ·
                refine ⟨5405491028933871970075393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7207321371911829293433857 5405491028933871970075393)
                ·
                  refine ⟨4054118271700403977556545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5405491028933871970075393 4054118271700403977556545)
                  ·
                    refine ⟨3040588703775302983167409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4054118271700403977556545 3040588703775302983167409)
                    ·
                      refine ⟨2280441527831477237375557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3040588703775302983167409 2280441527831477237375557)
                      ·
                        rfl

theorem cell23_4441144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 2, 2, 2].length) (baseStart_4441144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441144 prefixEnd_4441144 := by exact prefixLift 4441144
  have htrace : WordTrace (prefixWord ++ tailWord_4441144) baseStart_4441144 baseEnd_4441144 := by
    simpa [prefixWord, tailWord_4441144, baseEnd_4441144] using wordTrace_append hprefix tailTrace_4441144
  have hstable : (prefixWord ++ tailWord_4441144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441144).length < 2 ^ (prefixWord ++ tailWord_4441144).sum := by decide
  have hdescent : baseEnd_4441144 < baseStart_4441144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441150 : List Nat := [4, 2, 1, 3, 1, 2, 2, 1, 7]
def baseStart_4441150 : Nat := 118140960795 + 4441150 * 2 ^ 59
def prefixEnd_4441150 : Nat := 4983230072969 + 3 ^ 40 * 4441150 * 2
def baseEnd_4441150 : Nat := 253382734301711579322281

theorem tailTrace_4441150 : CollatzResearch.WordTrace tailWord_4441150 prefixEnd_4441150 253382734301711579322281 := by
  unfold tailWord_4441150
  simp only [CollatzResearch.WordTrace]
  refine ⟨20247755982559939109849113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107988031906986341919195269 20247755982559939109849113)
  ·
    refine ⟨15185816986919954332386835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20247755982559939109849113 15185816986919954332386835)
    ·
      refine ⟨22778725480379931498580253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15185816986919954332386835 22778725480379931498580253)
      ·
        refine ⟨8542022055142474311967595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22778725480379931498580253 8542022055142474311967595)
        ·
          refine ⟨12813033082713711467951393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8542022055142474311967595 12813033082713711467951393)
          ·
            refine ⟨9609774812035283600963545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12813033082713711467951393 9609774812035283600963545)
            ·
              refine ⟨7207331109026462700722659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9609774812035283600963545 7207331109026462700722659)
              ·
                refine ⟨10810996663539694051083989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7207331109026462700722659 10810996663539694051083989)
                ·
                  refine ⟨253382734301711579322281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10810996663539694051083989 253382734301711579322281)
                  ·
                    rfl

theorem cell23_4441150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_4441150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441150 prefixEnd_4441150 := by exact prefixLift 4441150
  have htrace : WordTrace (prefixWord ++ tailWord_4441150) baseStart_4441150 baseEnd_4441150 := by
    simpa [prefixWord, tailWord_4441150, baseEnd_4441150] using wordTrace_append hprefix tailTrace_4441150
  have hstable : (prefixWord ++ tailWord_4441150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441150).length < 2 ^ (prefixWord ++ tailWord_4441150).sum := by decide
  have hdescent : baseEnd_4441150 < baseStart_4441150 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441176 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 2, 8]
def baseStart_4441176 : Nat := 118140960795 + 4441176 * 2 ^ 59
def prefixEnd_4441176 : Nat := 4983230072969 + 3 ^ 40 * 4441176 * 2
def baseEnd_4441176 : Nat := 760152653070807037391803

theorem tailTrace_4441176 : CollatzResearch.WordTrace tailWord_4441176 prefixEnd_4441176 760152653070807037391803 := by
  unfold tailWord_4441176
  simp only [CollatzResearch.WordTrace]
  refine ⟨80991498079192659659619691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107988664105590212879492921 80991498079192659659619691)
  ·
    refine ⟨121487247118788989489429537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80991498079192659659619691 121487247118788989489429537)
    ·
      refine ⟨91115435339091742117072153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121487247118788989489429537 91115435339091742117072153)
      ·
        refine ⟨68336576504318806587804115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91115435339091742117072153 68336576504318806587804115)
        ·
          refine ⟨102504864756478209881706173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68336576504318806587804115 102504864756478209881706173)
          ·
            refine ⟨38439324283679328705639815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102504864756478209881706173 38439324283679328705639815)
            ·
              refine ⟨57658986425518993058459723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38439324283679328705639815 57658986425518993058459723)
              ·
                refine ⟨86488479638278489587689585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57658986425518993058459723 86488479638278489587689585)
                ·
                  refine ⟨64866359728708867190767189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86488479638278489587689585 64866359728708867190767189)
                  ·
                    refine ⟨760152653070807037391803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 64866359728708867190767189 760152653070807037391803)
                    ·
                      rfl

theorem cell23_4441176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 2, 8].length) (baseStart_4441176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441176 prefixEnd_4441176 := by exact prefixLift 4441176
  have htrace : WordTrace (prefixWord ++ tailWord_4441176) baseStart_4441176 baseEnd_4441176 := by
    simpa [prefixWord, tailWord_4441176, baseEnd_4441176] using wordTrace_append hprefix tailTrace_4441176
  have hstable : (prefixWord ++ tailWord_4441176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441176).length < 2 ^ (prefixWord ++ tailWord_4441176).sum := by decide
  have hdescent : baseEnd_4441176 < baseStart_4441176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441183 : List Nat := [1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 4]
def baseStart_4441183 : Nat := 118140960795 + 4441183 * 2 ^ 59
def prefixEnd_4441183 : Nat := 4983230072969 + 3 ^ 40 * 4441183 * 2
def baseEnd_4441183 : Nat := 2280461553577002584787877

theorem tailTrace_4441183 : CollatzResearch.WordTrace tailWord_4441183 prefixEnd_4441183 2280461553577002584787877 := by
  unfold tailWord_4441183
  simp only [CollatzResearch.WordTrace]
  refine ⟨161983251469359959514744203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107988834312906639676496135 161983251469359959514744203)
  ·
    refine ⟨242974877204039939272116305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161983251469359959514744203 242974877204039939272116305)
    ·
      refine ⟨182231157903029954454087229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242974877204039939272116305 182231157903029954454087229)
      ·
        refine ⟨68336684213636232920282711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182231157903029954454087229 68336684213636232920282711)
        ·
          refine ⟨102505026320454349380424067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68336684213636232920282711 102505026320454349380424067)
          ·
            refine ⟨153757539480681524070636101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102505026320454349380424067 153757539480681524070636101)
            ·
              refine ⟨28829538652627785763244269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 153757539480681524070636101 28829538652627785763244269)
              ·
                refine ⟨10811076994735419661216601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28829538652627785763244269 10811076994735419661216601)
                ·
                  refine ⟨8108307746051564745912451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10811076994735419661216601 8108307746051564745912451)
                  ·
                    refine ⟨12162461619077347118868677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8108307746051564745912451 12162461619077347118868677)
                    ·
                      refine ⟨2280461553577002584787877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12162461619077347118868677 2280461553577002584787877)
                      ·
                        rfl

theorem cell23_4441183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_4441183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441183 prefixEnd_4441183 := by exact prefixLift 4441183
  have htrace : WordTrace (prefixWord ++ tailWord_4441183) baseStart_4441183 baseEnd_4441183 := by
    simpa [prefixWord, tailWord_4441183, baseEnd_4441183] using wordTrace_append hprefix tailTrace_4441183
  have hstable : (prefixWord ++ tailWord_4441183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441183).length < 2 ^ (prefixWord ++ tailWord_4441183).sum := by decide
  have hdescent : baseEnd_4441183 < baseStart_4441183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441260 : List Nat := [2, 2, 1, 1, 1, 1, 1, 5, 4, 3, 2]
def baseStart_4441260 : Nat := 118140960795 + 4441260 * 2 ^ 59
def prefixEnd_4441260 : Nat := 4983230072969 + 3 ^ 40 * 4441260 * 2
def baseEnd_4441260 : Nat := 2280501091587398783525023

theorem tailTrace_4441260 : CollatzResearch.WordTrace tailWord_4441260 prefixEnd_4441260 2280501091587398783525023 := by
  unfold tailWord_4441260
  simp only [CollatzResearch.WordTrace]
  refine ⟨80993029945040500832648617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107990706593387334443531489 80993029945040500832648617)
  ·
    refine ⟨60744772458780375624486463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80993029945040500832648617 60744772458780375624486463)
    ·
      refine ⟨91117158688170563436729695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60744772458780375624486463 91117158688170563436729695)
      ·
        refine ⟨136675738032255845155094543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91117158688170563436729695 136675738032255845155094543)
        ·
          refine ⟨205013607048383767732641815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136675738032255845155094543 205013607048383767732641815)
          ·
            refine ⟨307520410572575651598962723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205013607048383767732641815 307520410572575651598962723)
            ·
              refine ⟨461280615858863477398444085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307520410572575651598962723 461280615858863477398444085)
              ·
                refine ⟨43245057736768451006104133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 461280615858863477398444085 43245057736768451006104133)
                ·
                  refine ⟨8108448325644084563644525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43245057736768451006104133 8108448325644084563644525)
                  ·
                    refine ⟨3040668122116531711366697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8108448325644084563644525 3040668122116531711366697)
                    ·
                      refine ⟨2280501091587398783525023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3040668122116531711366697 2280501091587398783525023)
                      ·
                        rfl

theorem cell23_4441260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 3, 2].length) (baseStart_4441260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441260 prefixEnd_4441260 := by exact prefixLift 4441260
  have htrace : WordTrace (prefixWord ++ tailWord_4441260) baseStart_4441260 baseEnd_4441260 := by
    simpa [prefixWord, tailWord_4441260, baseEnd_4441260] using wordTrace_append hprefix tailTrace_4441260
  have hstable : (prefixWord ++ tailWord_4441260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441260).length < 2 ^ (prefixWord ++ tailWord_4441260).sum := by decide
  have hdescent : baseEnd_4441260 < baseStart_4441260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441284 : List Nat := [2, 3, 3, 1, 3, 1, 1, 2, 3, 1, 3]
def baseStart_4441284 : Nat := 118140960795 + 4441284 * 2 ^ 59
def prefixEnd_4441284 : Nat := 4983230072969 + 3 ^ 40 * 4441284 * 2
def baseEnd_4441284 : Nat := 2280513415123106689624913

theorem tailTrace_4441284 : CollatzResearch.WordTrace tailWord_4441284 prefixEnd_4441284 2280513415123106689624913 := by
  unfold tailWord_4441284
  simp only [CollatzResearch.WordTrace]
  refine ⟨80993467620997026882085453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107991290161329369176113937 80993467620997026882085453)
  ·
    refine ⟨30372550357873885080782045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80993467620997026882085453 30372550357873885080782045)
    ·
      refine ⟨11389706384202706905293267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30372550357873885080782045 11389706384202706905293267)
      ·
        refine ⟨17084559576304060357939901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11389706384202706905293267 17084559576304060357939901)
        ·
          refine ⟨6406709841114022634227463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17084559576304060357939901 6406709841114022634227463)
          ·
            refine ⟨9610064761671033951341195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6406709841114022634227463 9610064761671033951341195)
            ·
              refine ⟨14415097142506550927011793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9610064761671033951341195 14415097142506550927011793)
              ·
                refine ⟨10811322856879913195258845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14415097142506550927011793 10811322856879913195258845)
                ·
                  refine ⟨4054246071329967448222067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10811322856879913195258845 4054246071329967448222067)
                  ·
                    refine ⟨6081369106994951172333101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4054246071329967448222067 6081369106994951172333101)
                    ·
                      refine ⟨2280513415123106689624913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6081369106994951172333101 2280513415123106689624913)
                      ·
                        rfl

theorem cell23_4441284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_4441284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441284 prefixEnd_4441284 := by exact prefixLift 4441284
  have htrace : WordTrace (prefixWord ++ tailWord_4441284) baseStart_4441284 baseEnd_4441284 := by
    simpa [prefixWord, tailWord_4441284, baseEnd_4441284] using wordTrace_append hprefix tailTrace_4441284
  have hstable : (prefixWord ++ tailWord_4441284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441284).length < 2 ^ (prefixWord ++ tailWord_4441284).sum := by decide
  have hdescent : baseEnd_4441284 < baseStart_4441284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441290 : List Nat := [3, 1, 2, 1, 3, 2, 2, 1, 3, 1, 4]
def baseStart_4441290 : Nat := 118140960795 + 4441290 * 2 ^ 59
def prefixEnd_4441290 : Nat := 4983230072969 + 3 ^ 40 * 4441290 * 2
def baseEnd_4441290 : Nat := 2280516496007033666149885

theorem tailTrace_4441290 : CollatzResearch.WordTrace tailWord_4441290 prefixEnd_4441290 2280516496007033666149885 := by
  unfold tailWord_4441290
  simp only [CollatzResearch.WordTrace]
  refine ⟨40496788519993079197222331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107991436053314877859259549 40496788519993079197222331)
  ·
    refine ⟨60745182779989618795833497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40496788519993079197222331 60745182779989618795833497)
    ·
      refine ⟨45558887084992214096875123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60745182779989618795833497 45558887084992214096875123)
      ·
        refine ⟨68338330627488321145312685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45558887084992214096875123 68338330627488321145312685)
        ·
          refine ⟨25626873985308120429492257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68338330627488321145312685 25626873985308120429492257)
          ·
            refine ⟨19220155488981090322119193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25626873985308120429492257 19220155488981090322119193)
            ·
              refine ⟨14415116616735817741589395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19220155488981090322119193 14415116616735817741589395)
              ·
                refine ⟨21622674925103726612384093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14415116616735817741589395 21622674925103726612384093)
                ·
                  refine ⟨8108503096913897479644035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21622674925103726612384093 8108503096913897479644035)
                  ·
                    refine ⟨12162754645370846219466053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8108503096913897479644035 12162754645370846219466053)
                    ·
                      refine ⟨2280516496007033666149885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12162754645370846219466053 2280516496007033666149885)
                      ·
                        rfl

theorem cell23_4441290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_4441290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441290 prefixEnd_4441290 := by exact prefixLift 4441290
  have htrace : WordTrace (prefixWord ++ tailWord_4441290) baseStart_4441290 baseEnd_4441290 := by
    simpa [prefixWord, tailWord_4441290, baseEnd_4441290] using wordTrace_append hprefix tailTrace_4441290
  have hstable : (prefixWord ++ tailWord_4441290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441290).length < 2 ^ (prefixWord ++ tailWord_4441290).sum := by decide
  have hdescent : baseEnd_4441290 < baseStart_4441290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441301 : List Nat := [1, 3, 2, 4, 1, 2, 2, 3, 1, 1, 3]
def baseStart_4441301 : Nat := 118140960795 + 4441301 * 2 ^ 59
def prefixEnd_4441301 : Nat := 4983230072969 + 3 ^ 40 * 4441301 * 2
def baseEnd_4441301 : Nat := 2280522144294233123112335

theorem tailTrace_4441301 : CollatzResearch.WordTrace tailWord_4441301 prefixEnd_4441301 2280522144294233123112335 := by
  unfold tailWord_4441301
  simp only [CollatzResearch.WordTrace]
  refine ⟨161987555282932465667539757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107991703521954977111693171 161987555282932465667539757)
  ·
    refine ⟨60745333231099674625327409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161987555282932465667539757 60745333231099674625327409)
    ·
      refine ⟨45558999923324755968995557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60745333231099674625327409 45558999923324755968995557)
      ·
        refine ⟨8542312485623391744186667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45558999923324755968995557 8542312485623391744186667)
        ·
          refine ⟨12813468728435087616280001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8542312485623391744186667 12813468728435087616280001)
          ·
            refine ⟨9610101546326315712210001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12813468728435087616280001 9610101546326315712210001)
            ·
              refine ⟨7207576159744736784157501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9610101546326315712210001 7207576159744736784157501)
              ·
                refine ⟨2702841059904276294059063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7207576159744736784157501 2702841059904276294059063)
                ·
                  refine ⟨4054261589856414441088595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2702841059904276294059063 4054261589856414441088595)
                  ·
                    refine ⟨6081392384784621661632893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4054261589856414441088595 6081392384784621661632893)
                    ·
                      refine ⟨2280522144294233123112335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6081392384784621661632893 2280522144294233123112335)
                      ·
                        rfl

theorem cell23_4441301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_4441301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441301 prefixEnd_4441301 := by exact prefixLift 4441301
  have htrace : WordTrace (prefixWord ++ tailWord_4441301) baseStart_4441301 baseEnd_4441301 := by
    simpa [prefixWord, tailWord_4441301, baseEnd_4441301] using wordTrace_append hprefix tailTrace_4441301
  have hstable : (prefixWord ++ tailWord_4441301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441301).length < 2 ^ (prefixWord ++ tailWord_4441301).sum := by decide
  have hdescent : baseEnd_4441301 < baseStart_4441301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441304 : List Nat := [2, 1, 2, 2, 5, 2, 2, 1, 1, 5]
def baseStart_4441304 : Nat := 118140960795 + 4441304 * 2 ^ 59
def prefixEnd_4441304 : Nat := 4983230072969 + 3 ^ 40 * 4441304 * 2
def baseEnd_4441304 : Nat := 760174561578732203791607

theorem tailTrace_4441304 : CollatzResearch.WordTrace tailWord_4441304 prefixEnd_4441304 760174561578732203791607 := by
  unfold tailWord_4441304
  simp only [CollatzResearch.WordTrace]
  refine ⟨80993832350960798589949483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107991776467947731453265977 80993832350960798589949483)
  ·
    refine ⟨121490748526441197884924225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80993832350960798589949483 121490748526441197884924225)
    ·
      refine ⟨91118061394830898413693169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121490748526441197884924225 91118061394830898413693169)
      ·
        refine ⟨68338546046123173810269877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91118061394830898413693169 68338546046123173810269877)
        ·
          refine ⟨6406738691824047544712801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68338546046123173810269877 6406738691824047544712801)
          ·
            refine ⟨4805054018868035658534601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6406738691824047544712801 4805054018868035658534601)
            ·
              refine ⟨3603790514151026743900951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4805054018868035658534601 3603790514151026743900951)
              ·
                refine ⟨5405685771226540115851427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3603790514151026743900951 5405685771226540115851427)
                ·
                  refine ⟨8108528656839810173777141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5405685771226540115851427 8108528656839810173777141)
                  ·
                    refine ⟨760174561578732203791607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8108528656839810173777141 760174561578732203791607)
                    ·
                      rfl

theorem cell23_4441304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 1, 5].length) (baseStart_4441304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441304 prefixEnd_4441304 := by exact prefixLift 4441304
  have htrace : WordTrace (prefixWord ++ tailWord_4441304) baseStart_4441304 baseEnd_4441304 := by
    simpa [prefixWord, tailWord_4441304, baseEnd_4441304] using wordTrace_append hprefix tailTrace_4441304
  have hstable : (prefixWord ++ tailWord_4441304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441304).length < 2 ^ (prefixWord ++ tailWord_4441304).sum := by decide
  have hdescent : baseEnd_4441304 < baseStart_4441304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441313 : List Nat := [1, 2, 3, 1, 3, 3, 10]
def baseStart_4441313 : Nat := 118140960795 + 4441313 * 2 ^ 59
def prefixEnd_4441313 : Nat := 4983230072969 + 3 ^ 40 * 4441313 * 2
def baseEnd_4441313 : Nat := 28154670445210951557559

theorem tailTrace_4441313 : CollatzResearch.WordTrace tailWord_4441313 prefixEnd_4441313 28154670445210951557559 := by
  unfold tailWord_4441313
  simp only [CollatzResearch.WordTrace]
  refine ⟨161987992958888991716976593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107991995305925994477984395 161987992958888991716976593)
  ·
    refine ⟨121490994719166743787732445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161987992958888991716976593 121490994719166743787732445)
    ·
      refine ⟨45559123019687528920399667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121490994719166743787732445 45559123019687528920399667)
      ·
        refine ⟨68338684529531293380599501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45559123019687528920399667 68338684529531293380599501)
        ·
          refine ⟨25627006698574235017724813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68338684529531293380599501 25627006698574235017724813)
          ·
            refine ⟨9610127511965338131646805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25627006698574235017724813 9610127511965338131646805)
            ·
              refine ⟨28154670445210951557559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9610127511965338131646805 28154670445210951557559)
              ·
                rfl

theorem cell23_4441313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 10].length) (baseStart_4441313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441313 prefixEnd_4441313 := by exact prefixLift 4441313
  have htrace : WordTrace (prefixWord ++ tailWord_4441313) baseStart_4441313 baseEnd_4441313 := by
    simpa [prefixWord, tailWord_4441313, baseEnd_4441313] using wordTrace_append hprefix tailTrace_4441313
  have hstable : (prefixWord ++ tailWord_4441313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441313).length < 2 ^ (prefixWord ++ tailWord_4441313).sum := by decide
  have hdescent : baseEnd_4441313 < baseStart_4441313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441317 : List Nat := [1, 3, 1, 4, 3, 1, 1, 1, 4, 4]
def baseStart_4441317 : Nat := 118140960795 + 4441317 * 2 ^ 59
def prefixEnd_4441317 : Nat := 4983230072969 + 3 ^ 40 * 4441317 * 2
def baseEnd_4441317 : Nat := 760176786661568353504087

theorem tailTrace_4441317 : CollatzResearch.WordTrace tailWord_4441317 prefixEnd_4441317 760176786661568353504087 := by
  unfold tailWord_4441317
  simp only [CollatzResearch.WordTrace]
  refine ⟨161988138850874500400122205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107992092567249666933414803 161988138850874500400122205)
  ·
    refine ⟨60745552069077937650045827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161988138850874500400122205 60745552069077937650045827)
    ·
      refine ⟨91118328103616906475068741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60745552069077937650045827 91118328103616906475068741)
      ·
        refine ⟨17084686519428169964075389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91118328103616906475068741 17084686519428169964075389)
        ·
          refine ⟨6406757444785563736528271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17084686519428169964075389 6406757444785563736528271)
          ·
            refine ⟨9610136167178345604792407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6406757444785563736528271 9610136167178345604792407)
            ·
              refine ⟨14415204250767518407188611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9610136167178345604792407 14415204250767518407188611)
              ·
                refine ⟨21622806376151277610782917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14415204250767518407188611 21622806376151277610782917)
                ·
                  refine ⟨4054276195528364552021797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21622806376151277610782917 4054276195528364552021797)
                  ·
                    refine ⟨760176786661568353504087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4054276195528364552021797 760176786661568353504087)
                    ·
                      rfl

theorem cell23_4441317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 4, 4].length) (baseStart_4441317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441317 prefixEnd_4441317 := by exact prefixLift 4441317
  have htrace : WordTrace (prefixWord ++ tailWord_4441317) baseStart_4441317 baseEnd_4441317 := by
    simpa [prefixWord, tailWord_4441317, baseEnd_4441317] using wordTrace_append hprefix tailTrace_4441317
  have hstable : (prefixWord ++ tailWord_4441317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441317).length < 2 ^ (prefixWord ++ tailWord_4441317).sum := by decide
  have hdescent : baseEnd_4441317 < baseStart_4441317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441324 : List Nat := [2, 2, 1, 1, 2, 5, 2, 1, 3, 2, 2]
def baseStart_4441324 : Nat := 118140960795 + 4441324 * 2 ^ 59
def prefixEnd_4441324 : Nat := 4983230072969 + 3 ^ 40 * 4441324 * 2
def baseEnd_4441324 : Nat := 2280533954349286533124729

theorem tailTrace_4441324 : CollatzResearch.WordTrace tailWord_4441324 prefixEnd_4441324 2280533954349286533124729 := by
  unfold tailWord_4441324
  simp only [CollatzResearch.WordTrace]
  refine ⟨80994197080924570297813513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107992262774566093730418017 80994197080924570297813513)
  ·
    refine ⟨60745647810693427723360135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80994197080924570297813513 60745647810693427723360135)
    ·
      refine ⟨91118471716040141585040203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60745647810693427723360135 91118471716040141585040203)
      ·
        refine ⟨136677707574060212377560305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91118471716040141585040203 136677707574060212377560305)
        ·
          refine ⟨102508280680545159283170229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136677707574060212377560305 102508280680545159283170229)
          ·
            refine ⟨9610151313801108682797209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102508280680545159283170229 9610151313801108682797209)
            ·
              refine ⟨7207613485350831512097907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9610151313801108682797209 7207613485350831512097907)
              ·
                refine ⟨10811420228026247268146861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7207613485350831512097907 10811420228026247268146861)
                ·
                  refine ⟨4054282585509842725555073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10811420228026247268146861 4054282585509842725555073)
                  ·
                    refine ⟨3040711939132382044166305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4054282585509842725555073 3040711939132382044166305)
                    ·
                      refine ⟨2280533954349286533124729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3040711939132382044166305 2280533954349286533124729)
                      ·
                        rfl

theorem cell23_4441324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 2, 2].length) (baseStart_4441324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441324 prefixEnd_4441324 := by exact prefixLift 4441324
  have htrace : WordTrace (prefixWord ++ tailWord_4441324) baseStart_4441324 baseEnd_4441324 := by
    simpa [prefixWord, tailWord_4441324, baseEnd_4441324] using wordTrace_append hprefix tailTrace_4441324
  have hstable : (prefixWord ++ tailWord_4441324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441324).length < 2 ^ (prefixWord ++ tailWord_4441324).sum := by decide
  have hdescent : baseEnd_4441324 < baseStart_4441324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441353 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 1, 4, 5]
def baseStart_4441353 : Nat := 118140960795 + 4441353 * 2 ^ 59
def prefixEnd_4441353 : Nat := 4983230072969 + 3 ^ 40 * 4441353 * 2
def baseEnd_4441353 : Nat := 2280548845288266919662095

theorem tailTrace_4441353 : CollatzResearch.WordTrace tailWord_4441353 prefixEnd_4441353 2280548845288266919662095 := by
  unfold tailWord_4441353
  simp only [CollatzResearch.WordTrace]
  refine ⟨161989451878744078548432713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107992967919162719032288475 161989451878744078548432713)
  ·
    refine ⟨121492088909058058911324535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161989451878744078548432713 121492088909058058911324535)
    ·
      refine ⟨182238133363587088366986803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121492088909058058911324535 182238133363587088366986803)
      ·
        refine ⟨273357200045380632550480205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182238133363587088366986803 273357200045380632550480205)
        ·
          refine ⟨102508950017017737206430077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 273357200045380632550480205 102508950017017737206430077)
          ·
            refine ⟨38440856256381651452411279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102508950017017737206430077 38440856256381651452411279)
            ·
              refine ⟨57661284384572477178616919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38440856256381651452411279 57661284384572477178616919)
              ·
                refine ⟨86491926576858715767925379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57661284384572477178616919 86491926576858715767925379)
                ·
                  refine ⟨129737889865288073651888069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86491926576858715767925379 129737889865288073651888069)
                  ·
                    refine ⟨24325854349741513809729013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 129737889865288073651888069 24325854349741513809729013)
                    ·
                      refine ⟨2280548845288266919662095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24325854349741513809729013 2280548845288266919662095)
                      ·
                        rfl

theorem cell23_4441353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 4, 5].length) (baseStart_4441353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441353 prefixEnd_4441353 := by exact prefixLift 4441353
  have htrace : WordTrace (prefixWord ++ tailWord_4441353) baseStart_4441353 baseEnd_4441353 := by
    simpa [prefixWord, tailWord_4441353, baseEnd_4441353] using wordTrace_append hprefix tailTrace_4441353
  have hstable : (prefixWord ++ tailWord_4441353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441353).length < 2 ^ (prefixWord ++ tailWord_4441353).sum := by decide
  have hdescent : baseEnd_4441353 < baseStart_4441353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4441358 : List Nat := [4, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2]
def baseStart_4441358 : Nat := 118140960795 + 4441358 * 2 ^ 59
def prefixEnd_4441358 : Nat := 4983230072969 + 3 ^ 40 * 4441358 * 2
def baseEnd_4441358 : Nat := 2280551412691539400099573

theorem tailTrace_4441358 : CollatzResearch.WordTrace tailWord_4441358 prefixEnd_4441358 2280551412691539400099573 := by
  unfold tailWord_4441358
  simp only [CollatzResearch.WordTrace]
  refine ⟨20248704280465745550295591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107993089495817309601576485 20248704280465745550295591)
  ·
    refine ⟨30373056420698618325443387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20248704280465745550295591 30373056420698618325443387)
    ·
      refine ⟨45559584631047927488165081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30373056420698618325443387 45559584631047927488165081)
      ·
        refine ⟨34169688473285945616123811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45559584631047927488165081 34169688473285945616123811)
        ·
          refine ⟨51254532709928918424185717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34169688473285945616123811 51254532709928918424185717)
          ·
            refine ⟨4805112441555836102267411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51254532709928918424185717 4805112441555836102267411)
            ·
              refine ⟨7207668662333754153401117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4805112441555836102267411 7207668662333754153401117)
              ·
                refine ⟨2702875748375157807525419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7207668662333754153401117 2702875748375157807525419)
                ·
                  refine ⟨4054313622562736711288129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2702875748375157807525419 4054313622562736711288129)
                  ·
                    refine ⟨3040735216922052533466097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4054313622562736711288129 3040735216922052533466097)
                    ·
                      refine ⟨2280551412691539400099573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3040735216922052533466097 2280551412691539400099573)
                      ·
                        rfl

theorem cell23_4441358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2].length) (baseStart_4441358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4441358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4441358 prefixEnd_4441358 := by exact prefixLift 4441358
  have htrace : WordTrace (prefixWord ++ tailWord_4441358) baseStart_4441358 baseEnd_4441358 := by
    simpa [prefixWord, tailWord_4441358, baseEnd_4441358] using wordTrace_append hprefix tailTrace_4441358
  have hstable : (prefixWord ++ tailWord_4441358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4441358).length < 2 ^ (prefixWord ++ tailWord_4441358).sum := by decide
  have hdescent : baseEnd_4441358 < baseStart_4441358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4441358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
