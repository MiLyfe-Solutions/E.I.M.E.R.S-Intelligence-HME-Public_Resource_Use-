import V185TrunkScan21Chunk069

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_848010 : List Nat := [3, 1, 2, 3, 1, 2, 1, 8]
def baseStart_848010 : Nat := 118140960795 + 848010 * 2 ^ 59
def prefixEnd_848010 : Nat := 4983230072969 + 3 ^ 40 * 848010 * 2
def baseEnd_848010 : Nat := 64509145158419613433345

theorem tailTrace_848010 : CollatzResearch.WordTrace tailWord_848010 prefixEnd_848010 64509145158419613433345 := by
  unfold tailWord_848010
  simp only [CollatzResearch.WordTrace]
  refine ⟨7732366414453018355679371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20619643771874715615144989 7732366414453018355679371)
  ·
    refine ⟨11598549621679527533519057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7732366414453018355679371 11598549621679527533519057)
    ·
      refine ⟨8698912216259645650139293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11598549621679527533519057 8698912216259645650139293)
      ·
        refine ⟨3262092081097367118802235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8698912216259645650139293 3262092081097367118802235)
        ·
          refine ⟨4893138121646050678203353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3262092081097367118802235 4893138121646050678203353)
          ·
            refine ⟨3669853591234538008652515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4893138121646050678203353 3669853591234538008652515)
            ·
              refine ⟨5504780386851807012978773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3669853591234538008652515 5504780386851807012978773)
              ·
                refine ⟨64509145158419613433345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5504780386851807012978773 64509145158419613433345)
                ·
                  rfl

theorem cell21_848010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 8].length) (baseStart_848010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_848010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_848010 prefixEnd_848010 := by exact prefixLift 848010
  have htrace : WordTrace (prefixWord ++ tailWord_848010) baseStart_848010 baseEnd_848010 := by
    simpa [prefixWord, tailWord_848010, baseEnd_848010] using wordTrace_append hprefix tailTrace_848010
  have hstable : (prefixWord ++ tailWord_848010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848010).length < 2 ^ (prefixWord ++ tailWord_848010).sum := by decide
  have hdescent : baseEnd_848010 < baseStart_848010 := by decide
  rcases family_descends (prefixWord ++ tailWord_848010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848100 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 9]
def baseStart_848100 : Nat := 118140960795 + 848100 * 2 ^ 59
def prefixEnd_848100 : Nat := 4983230072969 + 3 ^ 40 * 848100 * 2
def baseEnd_848100 : Nat := 193547974701438683799851

theorem tailTrace_848100 : CollatzResearch.WordTrace tailWord_848100 prefixEnd_848100 193547974701438683799851 := by
  unfold tailWord_848100
  simp only [CollatzResearch.WordTrace]
  refine ⟨15466374113743009396746877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20621832151657345862329169 15466374113743009396746877)
  ·
    refine ⟨5799890292653628523780079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15466374113743009396746877 5799890292653628523780079)
    ·
      refine ⟨8699835438980442785670119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5799890292653628523780079 8699835438980442785670119)
      ·
        refine ⟨13049753158470664178505179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8699835438980442785670119 13049753158470664178505179)
        ·
          refine ⟨19574629737705996267757769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13049753158470664178505179 19574629737705996267757769)
          ·
            refine ⟨14680972303279497200818327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19574629737705996267757769 14680972303279497200818327)
            ·
              refine ⟨22021458454919245801227491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14680972303279497200818327 22021458454919245801227491)
              ·
                refine ⟨33032187682378868701841237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22021458454919245801227491 33032187682378868701841237)
                ·
                  refine ⟨193547974701438683799851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 33032187682378868701841237 193547974701438683799851)
                  ·
                    rfl

theorem cell21_848100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_848100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_848100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_848100 prefixEnd_848100 := by exact prefixLift 848100
  have htrace : WordTrace (prefixWord ++ tailWord_848100) baseStart_848100 baseEnd_848100 := by
    simpa [prefixWord, tailWord_848100, baseEnd_848100] using wordTrace_append hprefix tailTrace_848100
  have hstable : (prefixWord ++ tailWord_848100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848100).length < 2 ^ (prefixWord ++ tailWord_848100).sum := by decide
  have hdescent : baseEnd_848100 < baseStart_848100 := by decide
  rcases family_descends (prefixWord ++ tailWord_848100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848151 : List Nat := [1, 1, 3, 4, 1, 4, 1, 3, 3]
def baseStart_848151 : Nat := 118140960795 + 848151 * 2 ^ 59
def prefixEnd_848151 : Nat := 4983230072969 + 3 ^ 40 * 848151 * 2
def baseEnd_848151 : Nat := 193559613596273928449747

theorem tailTrace_848151 : CollatzResearch.WordTrace tailWord_848151 prefixEnd_848151 193559613596273928449747 := by
  unfold tailWord_848151
  simp only [CollatzResearch.WordTrace]
  refine ⟨30934608350301254503600307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20623072233534169669066871 30934608350301254503600307)
  ·
    refine ⟨46401912525451881755400461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30934608350301254503600307 46401912525451881755400461)
    ·
      refine ⟨17400717197044455658275173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46401912525451881755400461 17400717197044455658275173)
      ·
        refine ⟨3262634474445835435926595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17400717197044455658275173 3262634474445835435926595)
        ·
          refine ⟨4893951711668753153889893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3262634474445835435926595 4893951711668753153889893)
          ·
            refine ⟨917615945937891216354355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4893951711668753153889893 917615945937891216354355)
            ·
              refine ⟨1376423918906836824531533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 917615945937891216354355 1376423918906836824531533)
              ·
                refine ⟨516158969590063809199325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1376423918906836824531533 516158969590063809199325)
                ·
                  refine ⟨193559613596273928449747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 516158969590063809199325 193559613596273928449747)
                  ·
                    rfl

theorem cell21_848151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 3, 3].length) (baseStart_848151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_848151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_848151 prefixEnd_848151 := by exact prefixLift 848151
  have htrace : WordTrace (prefixWord ++ tailWord_848151) baseStart_848151 baseEnd_848151 := by
    simpa [prefixWord, tailWord_848151, baseEnd_848151] using wordTrace_append hprefix tailTrace_848151
  have hstable : (prefixWord ++ tailWord_848151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848151).length < 2 ^ (prefixWord ++ tailWord_848151).sum := by decide
  have hdescent : baseEnd_848151 < baseStart_848151 := by decide
  rcases family_descends (prefixWord ++ tailWord_848151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848162 : List Nat := [3, 3, 1, 1, 3, 1, 9]
def baseStart_848162 : Nat := 118140960795 + 848162 * 2 ^ 59
def prefixEnd_848162 : Nat := 4983230072969 + 3 ^ 40 * 848162 * 2
def baseEnd_848162 : Nat := 21506902660682261529599

theorem tailTrace_848162 : CollatzResearch.WordTrace tailWord_848162 prefixEnd_848162 21506902660682261529599 := by
  unfold tailWord_848162
  simp only [CollatzResearch.WordTrace]
  refine ⟨7733752388315350845562685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20623339702174268921500493 7733752388315350845562685)
  ·
    refine ⟨2900157145618256567086007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7733752388315350845562685 2900157145618256567086007)
    ·
      refine ⟨4350235718427384850629011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2900157145618256567086007 4350235718427384850629011)
      ·
        refine ⟨6525353577641077275943517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4350235718427384850629011 6525353577641077275943517)
        ·
          refine ⟨2447007591615403978478819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6525353577641077275943517 2447007591615403978478819)
          ·
            refine ⟨3670511387423105967718229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2447007591615403978478819 3670511387423105967718229)
            ·
              refine ⟨21506902660682261529599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3670511387423105967718229 21506902660682261529599)
              ·
                rfl

theorem cell21_848162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 9].length) (baseStart_848162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_848162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_848162 prefixEnd_848162 := by exact prefixLift 848162
  have htrace : WordTrace (prefixWord ++ tailWord_848162) baseStart_848162 baseEnd_848162 := by
    simpa [prefixWord, tailWord_848162, baseEnd_848162] using wordTrace_append hprefix tailTrace_848162
  have hstable : (prefixWord ++ tailWord_848162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848162).length < 2 ^ (prefixWord ++ tailWord_848162).sum := by decide
  have hdescent : baseEnd_848162 < baseStart_848162 := by decide
  rcases family_descends (prefixWord ++ tailWord_848162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848168 : List Nat := [2, 1, 5, 1, 3, 1, 3, 2, 3]
def baseStart_848168 : Nat := 118140960795 + 848168 * 2 ^ 59
def prefixEnd_848168 : Nat := 4983230072969 + 3 ^ 40 * 848168 * 2
def baseEnd_848168 : Nat := 193563493227885676666379

theorem tailTrace_848168 : CollatzResearch.WordTrace tailWord_848168 prefixEnd_848168 193563493227885676666379 := by
  unfold tailWord_848168
  simp only [CollatzResearch.WordTrace]
  refine ⟨15467614195619833203484579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20623485594159777604646105 15467614195619833203484579)
  ·
    refine ⟨23201421293429749805226869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15467614195619833203484579 23201421293429749805226869)
    ·
      refine ⟨2175133246259039044240019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23201421293429749805226869 2175133246259039044240019)
      ·
        refine ⟨3262699869388558566360029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2175133246259039044240019 3262699869388558566360029)
        ·
          refine ⟨1223512451020709462385011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3262699869388558566360029 1223512451020709462385011)
          ·
            refine ⟨1835268676531064193577517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1223512451020709462385011 1835268676531064193577517)
            ·
              refine ⟨688225753699149072591569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1835268676531064193577517 688225753699149072591569)
              ·
                refine ⟨516169315274361804443677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 688225753699149072591569 516169315274361804443677)
                ·
                  refine ⟨193563493227885676666379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 516169315274361804443677 193563493227885676666379)
                  ·
                    rfl

theorem cell21_848168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 2, 3].length) (baseStart_848168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_848168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_848168 prefixEnd_848168 := by exact prefixLift 848168
  have htrace : WordTrace (prefixWord ++ tailWord_848168) baseStart_848168 baseEnd_848168 := by
    simpa [prefixWord, tailWord_848168, baseEnd_848168] using wordTrace_append hprefix tailTrace_848168
  have hstable : (prefixWord ++ tailWord_848168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848168).length < 2 ^ (prefixWord ++ tailWord_848168).sum := by decide
  have hdescent : baseEnd_848168 < baseStart_848168 := by decide
  rcases family_descends (prefixWord ++ tailWord_848168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848176 : List Nat := [2, 1, 1, 1, 2, 2, 2, 5, 5]
def baseStart_848176 : Nat := 118140960795 + 848176 * 2 ^ 59
def prefixEnd_848176 : Nat := 4983230072969 + 3 ^ 40 * 848176 * 2
def baseEnd_848176 : Nat := 193565318936879440533029

theorem tailTrace_848176 : CollatzResearch.WordTrace tailWord_848176 prefixEnd_848176 193565318936879440533029 := by
  unfold tailWord_848176
  simp only [CollatzResearch.WordTrace]
  refine ⟨15467760087605341886630191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20623680116807122515506921 15467760087605341886630191)
  ·
    refine ⟨23201640131408012829945287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15467760087605341886630191 23201640131408012829945287)
    ·
      refine ⟨34802460197112019244917931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23201640131408012829945287 34802460197112019244917931)
      ·
        refine ⟨52203690295668028867376897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34802460197112019244917931 52203690295668028867376897)
        ·
          refine ⟨39152767721751021650532673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52203690295668028867376897 39152767721751021650532673)
          ·
            refine ⟨29364575791313266237899505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39152767721751021650532673 29364575791313266237899505)
            ·
              refine ⟨22023431843484949678424629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29364575791313266237899505 22023431843484949678424629)
              ·
                refine ⟨2064696735326714032352309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22023431843484949678424629 2064696735326714032352309)
                ·
                  refine ⟨193565318936879440533029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2064696735326714032352309 193565318936879440533029)
                  ·
                    rfl

theorem cell21_848176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 5].length) (baseStart_848176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_848176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_848176 prefixEnd_848176 := by exact prefixLift 848176
  have htrace : WordTrace (prefixWord ++ tailWord_848176) baseStart_848176 baseEnd_848176 := by
    simpa [prefixWord, tailWord_848176, baseEnd_848176] using wordTrace_append hprefix tailTrace_848176
  have hstable : (prefixWord ++ tailWord_848176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848176).length < 2 ^ (prefixWord ++ tailWord_848176).sum := by decide
  have hdescent : baseEnd_848176 < baseStart_848176 := by decide
  rcases family_descends (prefixWord ++ tailWord_848176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848286 : List Nat := [4, 3, 1, 2, 1, 1, 1, 3, 5]
def baseStart_848286 : Nat := 118140960795 + 848286 * 2 ^ 59
def prefixEnd_848286 : Nat := 4983230072969 + 3 ^ 40 * 848286 * 2
def baseEnd_848286 : Nat := 193590422435543693699471

theorem tailTrace_848286 : CollatzResearch.WordTrace tailWord_848286 prefixEnd_848286 193590422435543693699471 := by
  unfold tailWord_848286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3867441525601521569970589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20626354803208115039843141 3867441525601521569970589)
  ·
    refine ⟨1450290572100570588738971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3867441525601521569970589 1450290572100570588738971)
    ·
      refine ⟨2175435858150855883108457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1450290572100570588738971 2175435858150855883108457)
      ·
        refine ⟨1631576893613141912331343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2175435858150855883108457 1631576893613141912331343)
        ·
          refine ⟨2447365340419712868497015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1631576893613141912331343 2447365340419712868497015)
          ·
            refine ⟨3671048010629569302745523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2447365340419712868497015 3671048010629569302745523)
            ·
              refine ⟨5506572015944353954118285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3671048010629569302745523 5506572015944353954118285)
              ·
                refine ⟨2064964505979132732794357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5506572015944353954118285 2064964505979132732794357)
                ·
                  refine ⟨193590422435543693699471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2064964505979132732794357 193590422435543693699471)
                  ·
                    rfl

theorem cell21_848286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_848286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_848286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_848286 prefixEnd_848286 := by exact prefixLift 848286
  have htrace : WordTrace (prefixWord ++ tailWord_848286) baseStart_848286 baseEnd_848286 := by
    simpa [prefixWord, tailWord_848286, baseEnd_848286] using wordTrace_append hprefix tailTrace_848286
  have hstable : (prefixWord ++ tailWord_848286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848286).length < 2 ^ (prefixWord ++ tailWord_848286).sum := by decide
  have hdescent : baseEnd_848286 < baseStart_848286 := by decide
  rcases family_descends (prefixWord ++ tailWord_848286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848480 : List Nat := [2, 1, 1, 3, 2, 1, 4, 2, 5]
def baseStart_848480 : Nat := 118140960795 + 848480 * 2 ^ 59
def prefixEnd_848480 : Nat := 4983230072969 + 3 ^ 40 * 848480 * 2
def baseEnd_848480 : Nat := 193634695878642467465741

theorem tailTrace_848480 : CollatzResearch.WordTrace tailWord_848480 prefixEnd_848480 193634695878642467465741 := by
  unfold tailWord_848480
  simp only [CollatzResearch.WordTrace]
  refine ⟨15473303983054671846163447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20631071977406229128217929 15473303983054671846163447)
  ·
    refine ⟨23209955974582007769245171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15473303983054671846163447 23209955974582007769245171)
    ·
      refine ⟨34814933961873011653867757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23209955974582007769245171 34814933961873011653867757)
      ·
        refine ⟨13055600235702379370200409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34814933961873011653867757 13055600235702379370200409)
        ·
          refine ⟨9791700176776784527650307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13055600235702379370200409 9791700176776784527650307)
          ·
            refine ⟨14687550265165176791475461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9791700176776784527650307 14687550265165176791475461)
            ·
              refine ⟨2753915674718470648401649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14687550265165176791475461 2753915674718470648401649)
              ·
                refine ⟨2065436756038852986301237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2753915674718470648401649 2065436756038852986301237)
                ·
                  refine ⟨193634695878642467465741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2065436756038852986301237 193634695878642467465741)
                  ·
                    rfl

theorem cell21_848480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 5].length) (baseStart_848480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_848480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_848480 prefixEnd_848480 := by exact prefixLift 848480
  have htrace : WordTrace (prefixWord ++ tailWord_848480) baseStart_848480 baseEnd_848480 := by
    simpa [prefixWord, tailWord_848480, baseEnd_848480] using wordTrace_append hprefix tailTrace_848480
  have hstable : (prefixWord ++ tailWord_848480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848480).length < 2 ^ (prefixWord ++ tailWord_848480).sum := by decide
  have hdescent : baseEnd_848480 < baseStart_848480 := by decide
  rcases family_descends (prefixWord ++ tailWord_848480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848539 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 11]
def baseStart_848539 : Nat := 118140960795 + 848539 * 2 ^ 59
def prefixEnd_848539 : Nat := 4983230072969 + 3 ^ 40 * 848539 * 2
def baseEnd_848539 : Nat := 193648160482471475982287

theorem tailTrace_848539 : CollatzResearch.WordTrace tailWord_848539 prefixEnd_848539 193648160482471475982287 := by
  unfold tailWord_848539
  simp only [CollatzResearch.WordTrace]
  refine ⟨30948759872895596768724671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20632506581930397845816447 30948759872895596768724671)
  ·
    refine ⟨46423139809343395153087007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30948759872895596768724671 46423139809343395153087007)
    ·
      refine ⟨69634709714015092729630511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46423139809343395153087007 69634709714015092729630511)
      ·
        refine ⟨104452064571022639094445767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69634709714015092729630511 104452064571022639094445767)
        ·
          refine ⟨156678096856533958641668651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104452064571022639094445767 156678096856533958641668651)
          ·
            refine ⟨235017145284800937962502977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156678096856533958641668651 235017145284800937962502977)
            ·
              refine ⟨176262858963600703471877233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235017145284800937962502977 176262858963600703471877233)
              ·
                refine ⟨132197144222700527603907925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176262858963600703471877233 132197144222700527603907925)
                ·
                  refine ⟨193648160482471475982287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 132197144222700527603907925 193648160482471475982287)
                  ·
                    rfl

theorem cell21_848539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 11].length) (baseStart_848539 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_848539 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_848539 prefixEnd_848539 := by exact prefixLift 848539
  have htrace : WordTrace (prefixWord ++ tailWord_848539) baseStart_848539 baseEnd_848539 := by
    simpa [prefixWord, tailWord_848539, baseEnd_848539] using wordTrace_append hprefix tailTrace_848539
  have hstable : (prefixWord ++ tailWord_848539).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848539).length < 2 ^ (prefixWord ++ tailWord_848539).sum := by decide
  have hdescent : baseEnd_848539 < baseStart_848539 := by decide
  rcases family_descends (prefixWord ++ tailWord_848539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848542 : List Nat := [4, 3, 1, 1, 1, 1, 1, 9]
def baseStart_848542 : Nat := 118140960795 + 848542 * 2 ^ 59
def prefixEnd_848542 : Nat := 4983230072969 + 3 ^ 40 * 848542 * 2
def baseEnd_848542 : Nat := 64549615041114712477427

theorem tailTrace_848542 : CollatzResearch.WordTrace tailWord_848542 prefixEnd_848542 64549615041114712477427 := by
  unfold tailWord_848542
  simp only [CollatzResearch.WordTrace]
  refine ⟨3868608661485591035135485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20632579527923152187389253 3868608661485591035135485)
  ·
    refine ⟨1450728248057096638175807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3868608661485591035135485 1450728248057096638175807)
    ·
      refine ⟨2176092372085644957263711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1450728248057096638175807 2176092372085644957263711)
      ·
        refine ⟨3264138558128467435895567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2176092372085644957263711 3264138558128467435895567)
        ·
          refine ⟨4896207837192701153843351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3264138558128467435895567 4896207837192701153843351)
          ·
            refine ⟨7344311755789051730765027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4896207837192701153843351 7344311755789051730765027)
            ·
              refine ⟨11016467633683577596147541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7344311755789051730765027 11016467633683577596147541)
              ·
                refine ⟨64549615041114712477427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11016467633683577596147541 64549615041114712477427)
                ·
                  rfl

theorem cell21_848542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_848542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_848542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_848542 prefixEnd_848542 := by exact prefixLift 848542
  have htrace : WordTrace (prefixWord ++ tailWord_848542) baseStart_848542 baseEnd_848542 := by
    simpa [prefixWord, tailWord_848542, baseEnd_848542] using wordTrace_append hprefix tailTrace_848542
  have hstable : (prefixWord ++ tailWord_848542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848542).length < 2 ^ (prefixWord ++ tailWord_848542).sum := by decide
  have hdescent : baseEnd_848542 < baseStart_848542 := by decide
  rcases family_descends (prefixWord ++ tailWord_848542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848632 : List Nat := [2, 1, 2, 1, 1, 2, 6, 1, 5]
def baseStart_848632 : Nat := 118140960795 + 848632 * 2 ^ 59
def prefixEnd_848632 : Nat := 4983230072969 + 3 ^ 40 * 848632 * 2
def baseEnd_848632 : Nat := 193669384349523980932097

theorem tailTrace_848632 : CollatzResearch.WordTrace tailWord_848632 prefixEnd_848632 193669384349523980932097 := by
  unfold tailWord_848632
  simp only [CollatzResearch.WordTrace]
  refine ⟨15476075930779336825930075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20634767907705782434573433 15476075930779336825930075)
  ·
    refine ⟨23214113896169005238895113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15476075930779336825930075 23214113896169005238895113)
    ·
      refine ⟨17410585422126753929171335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23214113896169005238895113 17410585422126753929171335)
      ·
        refine ⟨26115878133190130893757003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17410585422126753929171335 26115878133190130893757003)
        ·
          refine ⟨39173817199785196340635505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26115878133190130893757003 39173817199785196340635505)
          ·
            refine ⟨29380362899838897255476629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39173817199785196340635505 29380362899838897255476629)
            ·
              refine ⟨1377204510929948308850467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29380362899838897255476629 1377204510929948308850467)
              ·
                refine ⟨2065806766394922463275701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1377204510929948308850467 2065806766394922463275701)
                ·
                  refine ⟨193669384349523980932097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2065806766394922463275701 193669384349523980932097)
                  ·
                    rfl

theorem cell21_848632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 5].length) (baseStart_848632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_848632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_848632 prefixEnd_848632 := by exact prefixLift 848632
  have htrace : WordTrace (prefixWord ++ tailWord_848632) baseStart_848632 baseEnd_848632 := by
    simpa [prefixWord, tailWord_848632, baseEnd_848632] using wordTrace_append hprefix tailTrace_848632
  have hstable : (prefixWord ++ tailWord_848632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848632).length < 2 ^ (prefixWord ++ tailWord_848632).sum := by decide
  have hdescent : baseEnd_848632 < baseStart_848632 := by decide
  rcases family_descends (prefixWord ++ tailWord_848632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848725 : List Nat := [1, 3, 2, 2, 2, 1, 2, 5, 3]
def baseStart_848725 : Nat := 118140960795 + 848725 * 2 ^ 59
def prefixEnd_848725 : Nat := 4983230072969 + 3 ^ 40 * 848725 * 2
def baseEnd_848725 : Nat := 193690608216576485881907

theorem tailTrace_848725 : CollatzResearch.WordTrace tailWord_848725 prefixEnd_848725 193690608216576485881907 := by
  unfold tailWord_848725
  simp only [CollatzResearch.WordTrace]
  refine ⟨30955543850221750534995629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20637029233481167023330419 30955543850221750534995629)
  ·
    refine ⟨11608328943833156450623361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30955543850221750534995629 11608328943833156450623361)
    ·
      refine ⟨8706246707874867337967521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11608328943833156450623361 8706246707874867337967521)
      ·
        refine ⟨6529685030906150503475641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8706246707874867337967521 6529685030906150503475641)
        ·
          refine ⟨4897263773179612877606731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6529685030906150503475641 4897263773179612877606731)
          ·
            refine ⟨7345895659769419316410097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4897263773179612877606731 7345895659769419316410097)
            ·
              refine ⟨5509421744827064487307573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7345895659769419316410097 5509421744827064487307573)
              ·
                refine ⟨516508288577537295685085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5509421744827064487307573 516508288577537295685085)
                ·
                  refine ⟨193690608216576485881907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 516508288577537295685085 193690608216576485881907)
                  ·
                    rfl

theorem cell21_848725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 5, 3].length) (baseStart_848725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_848725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_848725 prefixEnd_848725 := by exact prefixLift 848725
  have htrace : WordTrace (prefixWord ++ tailWord_848725) baseStart_848725 baseEnd_848725 := by
    simpa [prefixWord, tailWord_848725, baseEnd_848725] using wordTrace_append hprefix tailTrace_848725
  have hstable : (prefixWord ++ tailWord_848725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848725).length < 2 ^ (prefixWord ++ tailWord_848725).sum := by decide
  have hdescent : baseEnd_848725 < baseStart_848725 := by decide
  rcases family_descends (prefixWord ++ tailWord_848725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848739 : List Nat := [1, 1, 1, 5, 3, 1, 1, 4, 4]
def baseStart_848739 : Nat := 118140960795 + 848739 * 2 ^ 59
def prefixEnd_848739 : Nat := 4983230072969 + 3 ^ 40 * 848739 * 2
def baseEnd_848739 : Nat := 193693803207315572648545

theorem tailTrace_848739 : CollatzResearch.WordTrace tailWord_848739 prefixEnd_848739 193693803207315572648545 := by
  unfold tailWord_848739
  simp only [CollatzResearch.WordTrace]
  refine ⟨30956054472171030926005271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20637369648114020617336847 30956054472171030926005271)
  ·
    refine ⟨46434081708256546389007907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30956054472171030926005271 46434081708256546389007907)
    ·
      refine ⟨69651122562384819583511861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46434081708256546389007907 69651122562384819583511861)
      ·
        refine ⟨6529792740223576835954237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69651122562384819583511861 6529792740223576835954237)
        ·
          refine ⟨2448672277583841313482839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6529792740223576835954237 2448672277583841313482839)
          ·
            refine ⟨3673008416375761970224259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2448672277583841313482839 3673008416375761970224259)
            ·
              refine ⟨5509512624563642955336389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3673008416375761970224259 5509512624563642955336389)
              ·
                refine ⟨1033033617105683054125573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5509512624563642955336389 1033033617105683054125573)
                ·
                  refine ⟨193693803207315572648545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1033033617105683054125573 193693803207315572648545)
                  ·
                    rfl

theorem cell21_848739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 4].length) (baseStart_848739 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_848739 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_848739 prefixEnd_848739 := by exact prefixLift 848739
  have htrace : WordTrace (prefixWord ++ tailWord_848739) baseStart_848739 baseEnd_848739 := by
    simpa [prefixWord, tailWord_848739, baseEnd_848739] using wordTrace_append hprefix tailTrace_848739
  have hstable : (prefixWord ++ tailWord_848739).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848739).length < 2 ^ (prefixWord ++ tailWord_848739).sum := by decide
  have hdescent : baseEnd_848739 < baseStart_848739 := by decide
  rcases family_descends (prefixWord ++ tailWord_848739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848753 : List Nat := [1, 2, 2, 2, 1, 4, 3, 6]
def baseStart_848753 : Nat := 118140960795 + 848753 * 2 ^ 59
def prefixEnd_848753 : Nat := 4983230072969 + 3 ^ 40 * 848753 * 2
def baseEnd_848753 : Nat := 64565666066018219805061

theorem tailTrace_848753 : CollatzResearch.WordTrace tailWord_848753 prefixEnd_848753 64565666066018219805061 := by
  unfold tailWord_848753
  simp only [CollatzResearch.WordTrace]
  refine ⟨30956565094120311317014913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20637710062746874211343275 30956565094120311317014913)
  ·
    refine ⟨23217423820590233487761185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30956565094120311317014913 23217423820590233487761185)
    ·
      refine ⟨17413067865442675115820889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23217423820590233487761185 17413067865442675115820889)
      ·
        refine ⟨13059800899082006336865667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17413067865442675115820889 13059800899082006336865667)
        ·
          refine ⟨19589701348623009505298501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13059800899082006336865667 19589701348623009505298501)
          ·
            refine ⟨3673069002866814282243469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19589701348623009505298501 3673069002866814282243469)
            ·
              refine ⟨1377400876075055355841301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3673069002866814282243469 1377400876075055355841301)
              ·
                refine ⟨64565666066018219805061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1377400876075055355841301 64565666066018219805061)
                ·
                  rfl

theorem cell21_848753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 6].length) (baseStart_848753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_848753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_848753 prefixEnd_848753 := by exact prefixLift 848753
  have htrace : WordTrace (prefixWord ++ tailWord_848753) baseStart_848753 baseEnd_848753 := by
    simpa [prefixWord, tailWord_848753, baseEnd_848753] using wordTrace_append hprefix tailTrace_848753
  have hstable : (prefixWord ++ tailWord_848753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848753).length < 2 ^ (prefixWord ++ tailWord_848753).sum := by decide
  have hdescent : baseEnd_848753 < baseStart_848753 := by decide
  rcases family_descends (prefixWord ++ tailWord_848753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848767 : List Nat := [1, 1, 2, 2, 1, 1, 5, 1, 7]
def baseStart_848767 : Nat := 118140960795 + 848767 * 2 ^ 59
def prefixEnd_848767 : Nat := 4983230072969 + 3 ^ 40 * 848767 * 2
def baseEnd_848767 : Nat := 193700193188793746181821

theorem tailTrace_848767 : CollatzResearch.WordTrace tailWord_848767 prefixEnd_848767 193700193188793746181821 := by
  unfold tailWord_848767
  simp only [CollatzResearch.WordTrace]
  refine ⟨30957075716069591708024555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20638050477379727805349703 30957075716069591708024555)
  ·
    refine ⟨46435613574104387562036833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30957075716069591708024555 46435613574104387562036833)
    ·
      refine ⟨34826710180578290671527625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46435613574104387562036833 34826710180578290671527625)
      ·
        refine ⟨26120032635433718003645719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34826710180578290671527625 26120032635433718003645719)
        ·
          refine ⟨39180048953150577005468579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26120032635433718003645719 39180048953150577005468579)
          ·
            refine ⟨58770073429725865508202869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39180048953150577005468579 58770073429725865508202869)
            ·
              refine ⟨5509694384036799891394019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58770073429725865508202869 5509694384036799891394019)
              ·
                refine ⟨8264541576055199837091029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5509694384036799891394019 8264541576055199837091029)
                ·
                  refine ⟨193700193188793746181821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8264541576055199837091029 193700193188793746181821)
                  ·
                    rfl

theorem cell21_848767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 7].length) (baseStart_848767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_848767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_848767 prefixEnd_848767 := by exact prefixLift 848767
  have htrace : WordTrace (prefixWord ++ tailWord_848767) baseStart_848767 baseEnd_848767 := by
    simpa [prefixWord, tailWord_848767, baseEnd_848767] using wordTrace_append hprefix tailTrace_848767
  have hstable : (prefixWord ++ tailWord_848767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848767).length < 2 ^ (prefixWord ++ tailWord_848767).sum := by decide
  have hdescent : baseEnd_848767 < baseStart_848767 := by decide
  rcases family_descends (prefixWord ++ tailWord_848767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848790 : List Nat := [5, 3, 1, 1, 1, 1, 3, 2, 4]
def baseStart_848790 : Nat := 118140960795 + 848790 * 2 ^ 59
def prefixEnd_848790 : Nat := 4983230072969 + 3 ^ 40 * 848790 * 2
def baseEnd_848790 : Nat := 193705442102150817298441

theorem tailTrace_848790 : CollatzResearch.WordTrace tailWord_848790 prefixEnd_848790 193705442102150817298441 := by
  unfold tailWord_848790
  simp only [CollatzResearch.WordTrace]
  refine ⟨1934869662186641664756989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20638609729990844424074549 1934869662186641664756989)
  ·
    refine ⟨725576123319990624283871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1934869662186641664756989 725576123319990624283871)
    ·
      refine ⟨1088364184979985936425807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 725576123319990624283871 1088364184979985936425807)
      ·
        refine ⟨1632546277469978904638711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1088364184979985936425807 1632546277469978904638711)
        ·
          refine ⟨2448819416204968356958067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1632546277469978904638711 2448819416204968356958067)
          ·
            refine ⟨3673229124307452535437101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2448819416204968356958067 3673229124307452535437101)
            ·
              refine ⟨1377460921615294700788913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3673229124307452535437101 1377460921615294700788913)
              ·
                refine ⟨1033095691211471025591685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1377460921615294700788913 1033095691211471025591685)
                ·
                  refine ⟨193705442102150817298441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1033095691211471025591685 193705442102150817298441)
                  ·
                    rfl

theorem cell21_848790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_848790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_848790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_848790 prefixEnd_848790 := by exact prefixLift 848790
  have htrace : WordTrace (prefixWord ++ tailWord_848790) baseStart_848790 baseEnd_848790 := by
    simpa [prefixWord, tailWord_848790, baseEnd_848790] using wordTrace_append hprefix tailTrace_848790
  have hstable : (prefixWord ++ tailWord_848790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848790).length < 2 ^ (prefixWord ++ tailWord_848790).sum := by decide
  have hdescent : baseEnd_848790 < baseStart_848790 := by decide
  rcases family_descends (prefixWord ++ tailWord_848790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848801 : List Nat := [1, 2, 3, 4, 1, 2, 2, 1, 5]
def baseStart_848801 : Nat := 118140960795 + 848801 * 2 ^ 59
def prefixEnd_848801 : Nat := 4983230072969 + 3 ^ 40 * 848801 * 2
def baseEnd_848801 : Nat := 193707952452017242615085

theorem tailTrace_848801 : CollatzResearch.WordTrace tailWord_848801 prefixEnd_848801 193707952452017242615085 := by
  unfold tailWord_848801
  simp only [CollatzResearch.WordTrace]
  refine ⟨30958315797946415514762257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20638877198630943676508171 30958315797946415514762257)
  ·
    refine ⟨23218736848459811636071693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30958315797946415514762257 23218736848459811636071693)
    ·
      refine ⟨8707026318172429363526885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23218736848459811636071693 8707026318172429363526885)
      ·
        refine ⟨1632567434657330505661291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8707026318172429363526885 1632567434657330505661291)
        ·
          refine ⟨2448851151985995758491937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1632567434657330505661291 2448851151985995758491937)
          ·
            refine ⟨1836638363989496818868953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2448851151985995758491937 1836638363989496818868953)
            ·
              refine ⟨1377478772992122614151715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1836638363989496818868953 1377478772992122614151715)
              ·
                refine ⟨2066218159488183921227573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1377478772992122614151715 2066218159488183921227573)
                ·
                  refine ⟨193707952452017242615085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2066218159488183921227573 193707952452017242615085)
                  ·
                    rfl

theorem cell21_848801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 5].length) (baseStart_848801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_848801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_848801 prefixEnd_848801 := by exact prefixLift 848801
  have htrace : WordTrace (prefixWord ++ tailWord_848801) baseStart_848801 baseEnd_848801 := by
    simpa [prefixWord, tailWord_848801, baseEnd_848801] using wordTrace_append hprefix tailTrace_848801
  have hstable : (prefixWord ++ tailWord_848801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848801).length < 2 ^ (prefixWord ++ tailWord_848801).sum := by decide
  have hdescent : baseEnd_848801 < baseStart_848801 := by decide
  rcases family_descends (prefixWord ++ tailWord_848801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848838 : List Nat := [6, 1, 3, 1, 2, 1, 7]
def baseStart_848838 : Nat := 118140960795 + 848838 * 2 ^ 59
def prefixEnd_848838 : Nat := 4983230072969 + 3 ^ 40 * 848838 * 2
def baseEnd_848838 : Nat := 21524044039568155610927

theorem tailTrace_848838 : CollatzResearch.WordTrace tailWord_848838 prefixEnd_848838 21524044039568155610927 := by
  unfold tailWord_848838
  simp only [CollatzResearch.WordTrace]
  refine ⟨967489540587886588558099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20639776865874913889239445 967489540587886588558099)
  ·
    refine ⟨1451234310881829882837149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 967489540587886588558099 1451234310881829882837149)
    ·
      refine ⟨544212866580686206063931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1451234310881829882837149 544212866580686206063931)
      ·
        refine ⟨816319299871029309095897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 544212866580686206063931 816319299871029309095897)
        ·
          refine ⟨612239474903271981821923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 816319299871029309095897 612239474903271981821923)
          ·
            refine ⟨918359212354907972732885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 612239474903271981821923 918359212354907972732885)
            ·
              refine ⟨21524044039568155610927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 918359212354907972732885 21524044039568155610927)
              ·
                rfl

theorem cell21_848838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 7].length) (baseStart_848838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_848838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_848838 prefixEnd_848838 := by exact prefixLift 848838
  have htrace : WordTrace (prefixWord ++ tailWord_848838) baseStart_848838 baseEnd_848838 := by
    simpa [prefixWord, tailWord_848838, baseEnd_848838] using wordTrace_append hprefix tailTrace_848838
  have hstable : (prefixWord ++ tailWord_848838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848838).length < 2 ^ (prefixWord ++ tailWord_848838).sum := by decide
  have hdescent : baseEnd_848838 < baseStart_848838 := by decide
  rcases family_descends (prefixWord ++ tailWord_848838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848866 : List Nat := [3, 3, 3, 1, 1, 3, 2, 1, 4]
def baseStart_848866 : Nat := 118140960795 + 848866 * 2 ^ 59
def prefixEnd_848866 : Nat := 4983230072969 + 3 ^ 40 * 848866 * 2
def baseEnd_848866 : Nat := 193722786337591574031619

theorem tailTrace_848866 : CollatzResearch.WordTrace tailWord_848866 prefixEnd_848866 193722786337591574031619 := by
  unfold tailWord_848866
  simp only [CollatzResearch.WordTrace]
  refine ⟨7740171635677732903969613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20640457695140621077252301 7740171635677732903969613)
  ·
    refine ⟨2902564363379149838988605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7740171635677732903969613 2902564363379149838988605)
    ·
      refine ⟨1088461636267181189620727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2902564363379149838988605 1088461636267181189620727)
      ·
        refine ⟨1632692454400771784431091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1088461636267181189620727 1632692454400771784431091)
        ·
          refine ⟨2449038681601157676646637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1632692454400771784431091 2449038681601157676646637)
          ·
            refine ⟨918389505600434128742489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2449038681601157676646637 918389505600434128742489)
            ·
              refine ⟨688792129200325596556867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 918389505600434128742489 688792129200325596556867)
              ·
                refine ⟨1033188193800488394835301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 688792129200325596556867 1033188193800488394835301)
                ·
                  refine ⟨193722786337591574031619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1033188193800488394835301 193722786337591574031619)
                  ·
                    rfl

theorem cell21_848866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_848866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_848866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_848866 prefixEnd_848866 := by exact prefixLift 848866
  have htrace : WordTrace (prefixWord ++ tailWord_848866) baseStart_848866 baseEnd_848866 := by
    simpa [prefixWord, tailWord_848866, baseEnd_848866] using wordTrace_append hprefix tailTrace_848866
  have hstable : (prefixWord ++ tailWord_848866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848866).length < 2 ^ (prefixWord ++ tailWord_848866).sum := by decide
  have hdescent : baseEnd_848866 < baseStart_848866 := by decide
  rcases family_descends (prefixWord ++ tailWord_848866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848953 : List Nat := [1, 2, 1, 5, 2, 1, 1, 5, 3]
def baseStart_848953 : Nat := 118140960795 + 848953 * 2 ^ 59
def prefixEnd_848953 : Nat := 4983230072969 + 3 ^ 40 * 848953 * 2
def baseEnd_848953 : Nat := 193742640922898756081441

theorem tailTrace_848953 : CollatzResearch.WordTrace tailWord_848953 prefixEnd_848953 193742640922898756081441 := by
  unfold tailWord_848953
  simp only [CollatzResearch.WordTrace]
  refine ⟨30963859693395745474295513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20642573128930496982863675 30963859693395745474295513)
  ·
    refine ⟨23222894770046809105721635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30963859693395745474295513 23222894770046809105721635)
    ·
      refine ⟨34834342155070213658582453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23222894770046809105721635 34834342155070213658582453)
      ·
        refine ⟨3265719577037832530492105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34834342155070213658582453 3265719577037832530492105)
        ·
          refine ⟨2449289682778374397869079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3265719577037832530492105 2449289682778374397869079)
          ·
            refine ⟨3673934524167561596803619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2449289682778374397869079 3673934524167561596803619)
            ·
              refine ⟨5510901786251342395205429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3673934524167561596803619 5510901786251342395205429)
              ·
                refine ⟨516647042461063349550509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5510901786251342395205429 516647042461063349550509)
                ·
                  refine ⟨193742640922898756081441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 516647042461063349550509 193742640922898756081441)
                  ·
                    rfl

theorem cell21_848953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 5, 3].length) (baseStart_848953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_848953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_848953 prefixEnd_848953 := by exact prefixLift 848953
  have htrace : WordTrace (prefixWord ++ tailWord_848953) baseStart_848953 baseEnd_848953 := by
    simpa [prefixWord, tailWord_848953, baseEnd_848953] using wordTrace_append hprefix tailTrace_848953
  have hstable : (prefixWord ++ tailWord_848953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848953).length < 2 ^ (prefixWord ++ tailWord_848953).sum := by decide
  have hdescent : baseEnd_848953 < baseStart_848953 := by decide
  rcases family_descends (prefixWord ++ tailWord_848953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848967 : List Nat := [1, 1, 4, 1, 3, 2, 3, 2, 4]
def baseStart_848967 : Nat := 118140960795 + 848967 * 2 ^ 59
def prefixEnd_848967 : Nat := 4983230072969 + 3 ^ 40 * 848967 * 2
def baseEnd_848967 : Nat := 193745835913637842848079

theorem tailTrace_848967 : CollatzResearch.WordTrace tailWord_848967 prefixEnd_848967 193745835913637842848079 := by
  unfold tailWord_848967
  simp only [CollatzResearch.WordTrace]
  refine ⟨30964370315345025865305155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20642913543563350576870103 30964370315345025865305155)
  ·
    refine ⟨46446555473017538797957733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30964370315345025865305155 46446555473017538797957733)
    ·
      refine ⟨8708729151190788524617075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46446555473017538797957733 8708729151190788524617075)
      ·
        refine ⟨13063093726786182786925613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8708729151190788524617075 13063093726786182786925613)
        ·
          refine ⟨4898660147544818545097105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13063093726786182786925613 4898660147544818545097105)
          ·
            refine ⟨3673995110658613908822829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4898660147544818545097105 3673995110658613908822829)
            ·
              refine ⟨1377748166496980215808561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3673995110658613908822829 1377748166496980215808561)
              ·
                refine ⟨1033311124872735161856421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1377748166496980215808561 1033311124872735161856421)
                ·
                  refine ⟨193745835913637842848079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1033311124872735161856421 193745835913637842848079)
                  ·
                    rfl

theorem cell21_848967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 4].length) (baseStart_848967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_848967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_848967 prefixEnd_848967 := by exact prefixLift 848967
  have htrace : WordTrace (prefixWord ++ tailWord_848967) baseStart_848967 baseEnd_848967 := by
    simpa [prefixWord, tailWord_848967, baseEnd_848967] using wordTrace_append hprefix tailTrace_848967
  have hstable : (prefixWord ++ tailWord_848967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848967).length < 2 ^ (prefixWord ++ tailWord_848967).sum := by decide
  have hdescent : baseEnd_848967 < baseStart_848967 := by decide
  rcases family_descends (prefixWord ++ tailWord_848967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849029 : List Nat := [1, 3, 1, 1, 6, 2, 1, 1, 5]
def baseStart_849029 : Nat := 118140960795 + 849029 * 2 ^ 59
def prefixEnd_849029 : Nat := 4983230072969 + 3 ^ 40 * 849029 * 2
def baseEnd_849029 : Nat := 193759985158339512814619

theorem tailTrace_849029 : CollatzResearch.WordTrace tailWord_849029 prefixEnd_849029 193759985158339512814619 := by
  unfold tailWord_849029
  simp only [CollatzResearch.WordTrace]
  refine ⟨30966631641120410454062141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20644421094080273636041427 30966631641120410454062141)
  ·
    refine ⟨11612486865420153920273303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30966631641120410454062141 11612486865420153920273303)
    ·
      refine ⟨17418730298130230880409955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11612486865420153920273303 17418730298130230880409955)
      ·
        refine ⟨26128095447195346320614933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17418730298130230880409955 26128095447195346320614933)
        ·
          refine ⟨1224754474087281858778825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 26128095447195346320614933 1224754474087281858778825)
          ·
            refine ⟨918565855565461394084119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1224754474087281858778825 918565855565461394084119)
            ·
              refine ⟨1377848783348192091126179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 918565855565461394084119 1377848783348192091126179)
              ·
                refine ⟨2066773175022288136689269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1377848783348192091126179 2066773175022288136689269)
                ·
                  refine ⟨193759985158339512814619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2066773175022288136689269 193759985158339512814619)
                  ·
                    rfl

theorem cell21_849029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 5].length) (baseStart_849029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_849029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_849029 prefixEnd_849029 := by exact prefixLift 849029
  have htrace : WordTrace (prefixWord ++ tailWord_849029) baseStart_849029 baseEnd_849029 := by
    simpa [prefixWord, tailWord_849029, baseEnd_849029] using wordTrace_append hprefix tailTrace_849029
  have hstable : (prefixWord ++ tailWord_849029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849029).length < 2 ^ (prefixWord ++ tailWord_849029).sum := by decide
  have hdescent : baseEnd_849029 < baseStart_849029 := by decide
  rcases family_descends (prefixWord ++ tailWord_849029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849043 : List Nat := [1, 1, 1, 2, 1, 2, 8, 1, 4]
def baseStart_849043 : Nat := 118140960795 + 849043 * 2 ^ 59
def prefixEnd_849043 : Nat := 4983230072969 + 3 ^ 40 * 849043 * 2
def baseEnd_849043 : Nat := 193763180149078599581257

theorem tailTrace_849043 : CollatzResearch.WordTrace tailWord_849043 prefixEnd_849043 193763180149078599581257 := by
  unfold tailWord_849043
  simp only [CollatzResearch.WordTrace]
  refine ⟨30967142263069690845071783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20644761508713127230047855 30967142263069690845071783)
  ·
    refine ⟨46450713394604536267607675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30967142263069690845071783 46450713394604536267607675)
    ·
      refine ⟨69676070091906804401411513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46450713394604536267607675 69676070091906804401411513)
      ·
        refine ⟨52257052568930103301058635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69676070091906804401411513 52257052568930103301058635)
        ·
          refine ⟨78385578853395154951587953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52257052568930103301058635 78385578853395154951587953)
          ·
            refine ⟨58789184140046366213690965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78385578853395154951587953 58789184140046366213690965)
            ·
              refine ⟨688935751641168354066691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 58789184140046366213690965 688935751641168354066691)
              ·
                refine ⟨1033403627461752531100037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 688935751641168354066691 1033403627461752531100037)
                ·
                  refine ⟨193763180149078599581257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1033403627461752531100037 193763180149078599581257)
                  ·
                    rfl

theorem cell21_849043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 4].length) (baseStart_849043 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_849043 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_849043 prefixEnd_849043 := by exact prefixLift 849043
  have htrace : WordTrace (prefixWord ++ tailWord_849043) baseStart_849043 baseEnd_849043 := by
    simpa [prefixWord, tailWord_849043, baseEnd_849043] using wordTrace_append hprefix tailTrace_849043
  have hstable : (prefixWord ++ tailWord_849043).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849043).length < 2 ^ (prefixWord ++ tailWord_849043).sum := by decide
  have hdescent : baseEnd_849043 < baseStart_849043 := by decide
  rcases family_descends (prefixWord ++ tailWord_849043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849133 : List Nat := [1, 5, 1, 2, 2, 2, 8]
def baseStart_849133 : Nat := 118140960795 + 849133 * 2 ^ 59
def prefixEnd_849133 : Nat := 4983230072969 + 3 ^ 40 * 849133 * 2
def baseEnd_849133 : Nat := 21531524375028715897897

theorem tailTrace_849133 : CollatzResearch.WordTrace tailWord_849133 prefixEnd_849133 21531524375028715897897 := by
  unfold tailWord_849133
  simp only [CollatzResearch.WordTrace]
  refine ⟨30970424832743636215848053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20646949888495757477232035 30970424832743636215848053)
  ·
    refine ⟨2903477328069715895235755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30970424832743636215848053 2903477328069715895235755)
    ·
      refine ⟨4355215992104573842853633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2903477328069715895235755 4355215992104573842853633)
      ·
        refine ⟨3266411994078430382140225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4355215992104573842853633 3266411994078430382140225)
        ·
          refine ⟨2449808995558822786605169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3266411994078430382140225 2449808995558822786605169)
          ·
            refine ⟨1837356746669117089953877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2449808995558822786605169 1837356746669117089953877)
            ·
              refine ⟨21531524375028715897897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1837356746669117089953877 21531524375028715897897)
              ·
                rfl

theorem cell21_849133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 8].length) (baseStart_849133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_849133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_849133 prefixEnd_849133 := by exact prefixLift 849133
  have htrace : WordTrace (prefixWord ++ tailWord_849133) baseStart_849133 baseEnd_849133 := by
    simpa [prefixWord, tailWord_849133, baseEnd_849133] using wordTrace_append hprefix tailTrace_849133
  have hstable : (prefixWord ++ tailWord_849133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849133).length < 2 ^ (prefixWord ++ tailWord_849133).sum := by decide
  have hdescent : baseEnd_849133 < baseStart_849133 := by decide
  rcases family_descends (prefixWord ++ tailWord_849133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849178 : List Nat := [3, 1, 1, 3, 3, 1, 1, 2, 6]
def baseStart_849178 : Nat := 118140960795 + 849178 * 2 ^ 59
def prefixEnd_849178 : Nat := 4983230072969 + 3 ^ 40 * 849178 * 2
def baseEnd_849178 : Nat := 193793988988348364830981

theorem tailTrace_849178 : CollatzResearch.WordTrace tailWord_849178 prefixEnd_849178 193793988988348364830981 := by
  unfold tailWord_849178
  simp only [CollatzResearch.WordTrace]
  refine ⟨7743016529395152225309047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20648044078387072600824125 7743016529395152225309047)
  ·
    refine ⟨11614524794092728337963571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7743016529395152225309047 11614524794092728337963571)
    ·
      refine ⟨17421787191139092506945357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11614524794092728337963571 17421787191139092506945357)
      ·
        refine ⟨6533170196677159690104509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17421787191139092506945357 6533170196677159690104509)
        ·
          refine ⟨2449938823753934883789191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6533170196677159690104509 2449938823753934883789191)
          ·
            refine ⟨3674908235630902325683787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2449938823753934883789191 3674908235630902325683787)
            ·
              refine ⟨5512362353446353488525681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3674908235630902325683787 5512362353446353488525681)
              ·
                refine ⟨4134271765084765116394261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5512362353446353488525681 4134271765084765116394261)
                ·
                  refine ⟨193793988988348364830981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4134271765084765116394261 193793988988348364830981)
                  ·
                    rfl

theorem cell21_849178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_849178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_849178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_849178 prefixEnd_849178 := by exact prefixLift 849178
  have htrace : WordTrace (prefixWord ++ tailWord_849178) baseStart_849178 baseEnd_849178 := by
    simpa [prefixWord, tailWord_849178, baseEnd_849178] using wordTrace_append hprefix tailTrace_849178
  have hstable : (prefixWord ++ tailWord_849178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849178).length < 2 ^ (prefixWord ++ tailWord_849178).sum := by decide
  have hdescent : baseEnd_849178 < baseStart_849178 := by decide
  rcases family_descends (prefixWord ++ tailWord_849178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849212 : List Nat := [2, 2, 2, 2, 1, 5, 2, 1, 4]
def baseStart_849212 : Nat := 118140960795 + 849212 * 2 ^ 59
def prefixEnd_849212 : Nat := 4983230072969 + 3 ^ 40 * 849212 * 2
def baseEnd_849212 : Nat := 193801748251571861264245

theorem tailTrace_849212 : CollatzResearch.WordTrace tailWord_849212 prefixEnd_849212 193801748251571861264245 := by
  unfold tailWord_849212
  simp only [CollatzResearch.WordTrace]
  refine ⟨15486653099728716353986945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20648870799638288471982593 15486653099728716353986945)
  ·
    refine ⟨11614989824796537265490209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15486653099728716353986945 11614989824796537265490209)
    ·
      refine ⟨8711242368597402949117657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11614989824796537265490209 8711242368597402949117657)
      ·
        refine ⟨6533431776448052211838243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8711242368597402949117657 6533431776448052211838243)
        ·
          refine ⟨9800147664672078317757365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6533431776448052211838243 9800147664672078317757365)
          ·
            refine ⟨918763843563007342289753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9800147664672078317757365 918763843563007342289753)
            ·
              refine ⟨689072882672255506717315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 918763843563007342289753 689072882672255506717315)
              ·
                refine ⟨1033609324008383260075973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 689072882672255506717315 1033609324008383260075973)
                ·
                  refine ⟨193801748251571861264245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1033609324008383260075973 193801748251571861264245)
                  ·
                    rfl

theorem cell21_849212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 4].length) (baseStart_849212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_849212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_849212 prefixEnd_849212 := by exact prefixLift 849212
  have htrace : WordTrace (prefixWord ++ tailWord_849212) baseStart_849212 baseEnd_849212 := by
    simpa [prefixWord, tailWord_849212, baseEnd_849212] using wordTrace_append hprefix tailTrace_849212
  have hstable : (prefixWord ++ tailWord_849212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849212).length < 2 ^ (prefixWord ++ tailWord_849212).sum := by decide
  have hdescent : baseEnd_849212 < baseStart_849212 := by decide
  rcases family_descends (prefixWord ++ tailWord_849212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849240 : List Nat := [2, 1, 2, 2, 1, 1, 4, 5, 3]
def baseStart_849240 : Nat := 118140960795 + 849240 * 2 ^ 59
def prefixEnd_849240 : Nat := 4983230072969 + 3 ^ 40 * 849240 * 2
def baseEnd_849240 : Nat := 193808138233050034797521

theorem tailTrace_849240 : CollatzResearch.WordTrace tailWord_849240 prefixEnd_849240 193808138233050034797521 := by
  unfold tailWord_849240
  simp only [CollatzResearch.WordTrace]
  refine ⟨15487163721677996744996587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20649551628903995659995449 15487163721677996744996587)
  ·
    refine ⟨23230745582516995117494881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15487163721677996744996587 23230745582516995117494881)
    ·
      refine ⟨17423059186887746338121161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23230745582516995117494881 17423059186887746338121161)
      ·
        refine ⟨13067294390165809753590871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17423059186887746338121161 13067294390165809753590871)
        ·
          refine ⟨19600941585248714630386307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13067294390165809753590871 19600941585248714630386307)
          ·
            refine ⟨29401412377873071945579461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19600941585248714630386307 29401412377873071945579461)
            ·
              refine ⟨5512764820851200989796149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29401412377873071945579461 5512764820851200989796149)
              ·
                refine ⟨516821701954800092793389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5512764820851200989796149 516821701954800092793389)
                ·
                  refine ⟨193808138233050034797521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 516821701954800092793389 193808138233050034797521)
                  ·
                    rfl

theorem cell21_849240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 5, 3].length) (baseStart_849240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_849240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_849240 prefixEnd_849240 := by exact prefixLift 849240
  have htrace : WordTrace (prefixWord ++ tailWord_849240) baseStart_849240 baseEnd_849240 := by
    simpa [prefixWord, tailWord_849240, baseEnd_849240] using wordTrace_append hprefix tailTrace_849240
  have hstable : (prefixWord ++ tailWord_849240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849240).length < 2 ^ (prefixWord ++ tailWord_849240).sum := by decide
  have hdescent : baseEnd_849240 < baseStart_849240 := by decide
  rcases family_descends (prefixWord ++ tailWord_849240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849420 : List Nat := [2, 2, 1, 2, 5, 9]
def baseStart_849420 : Nat := 118140960795 + 849420 * 2 ^ 59
def prefixEnd_849420 : Nat := 4983230072969 + 3 ^ 40 * 849420 * 2
def baseEnd_849420 : Nat := 7179600617978137844339

theorem tailTrace_849420 : CollatzResearch.WordTrace tailWord_849420 prefixEnd_849420 7179600617978137844339 := by
  unfold tailWord_849420
  simp only [CollatzResearch.WordTrace]
  refine ⟨15490446291351942115772857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20653928388469256154363809 15490446291351942115772857)
  ·
    refine ⟨11617834718513956586829643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15490446291351942115772857 11617834718513956586829643)
    ·
      refine ⟨17426752077770934880244465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11617834718513956586829643 17426752077770934880244465)
      ·
        refine ⟨13070064058328201160183349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17426752077770934880244465 13070064058328201160183349)
        ·
          refine ⟨1225318505468268858767189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13070064058328201160183349 1225318505468268858767189)
          ·
            refine ⟨7179600617978137844339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1225318505468268858767189 7179600617978137844339)
            ·
              rfl

theorem cell21_849420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 9].length) (baseStart_849420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_849420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_849420 prefixEnd_849420 := by exact prefixLift 849420
  have htrace : WordTrace (prefixWord ++ tailWord_849420) baseStart_849420 baseEnd_849420 := by
    simpa [prefixWord, tailWord_849420, baseEnd_849420] using wordTrace_append hprefix tailTrace_849420
  have hstable : (prefixWord ++ tailWord_849420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849420).length < 2 ^ (prefixWord ++ tailWord_849420).sum := by decide
  have hdescent : baseEnd_849420 < baseStart_849420 := by decide
  rcases family_descends (prefixWord ++ tailWord_849420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849454 : List Nat := [4, 1, 3, 1, 2, 2, 3, 5]
def baseStart_849454 : Nat := 118140960795 + 849454 * 2 ^ 59
def prefixEnd_849454 : Nat := 4983230072969 + 3 ^ 40 * 849454 * 2
def baseEnd_849454 : Nat := 64618991982877739410139

theorem tailTrace_849454 : CollatzResearch.WordTrace tailWord_849454 prefixEnd_849454 64618991982877739410139 := by
  unfold tailWord_849454
  simp only [CollatzResearch.WordTrace]
  refine ⟨3872766583072588504785427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20654755109720472025522277 3872766583072588504785427)
  ·
    refine ⟨5809149874608882757178141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3872766583072588504785427 5809149874608882757178141)
    ·
      refine ⟨2178431202978331033941803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5809149874608882757178141 2178431202978331033941803)
      ·
        refine ⟨3267646804467496550912705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2178431202978331033941803 3267646804467496550912705)
        ·
          refine ⟨2450735103350622413184529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3267646804467496550912705 2450735103350622413184529)
          ·
            refine ⟨1838051327512966809888397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2450735103350622413184529 1838051327512966809888397)
            ·
              refine ⟨689269247817362553708149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1838051327512966809888397 689269247817362553708149)
              ·
                refine ⟨64618991982877739410139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 689269247817362553708149 64618991982877739410139)
                ·
                  rfl

theorem cell21_849454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_849454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_849454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_849454 prefixEnd_849454 := by exact prefixLift 849454
  have htrace : WordTrace (prefixWord ++ tailWord_849454) baseStart_849454 baseEnd_849454 := by
    simpa [prefixWord, tailWord_849454, baseEnd_849454] using wordTrace_append hprefix tailTrace_849454
  have hstable : (prefixWord ++ tailWord_849454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849454).length < 2 ^ (prefixWord ++ tailWord_849454).sum := by decide
  have hdescent : baseEnd_849454 < baseStart_849454 := by decide
  rcases family_descends (prefixWord ++ tailWord_849454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849485 : List Nat := [1, 6, 1, 1, 3, 1, 2, 1, 5]
def baseStart_849485 : Nat := 118140960795 + 849485 * 2 ^ 59
def prefixEnd_849485 : Nat := 4983230072969 + 3 ^ 40 * 849485 * 2
def baseEnd_849485 : Nat := 193864050570984053213687

theorem tailTrace_849485 : CollatzResearch.WordTrace tailWord_849485 prefixEnd_849485 193864050570984053213687 := by
  unfold tailWord_849485
  simp only [CollatzResearch.WordTrace]
  refine ⟨30983263327468400332661909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20655508884978933555107939 30983263327468400332661909)
  ·
    refine ⟨1452340468475081265593527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30983263327468400332661909 1452340468475081265593527)
    ·
      refine ⟨2178510702712621898390291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1452340468475081265593527 2178510702712621898390291)
      ·
        refine ⟨3267766054068932847585437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2178510702712621898390291 3267766054068932847585437)
        ·
          refine ⟨1225412270275849817844539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3267766054068932847585437 1225412270275849817844539)
          ·
            refine ⟨1838118405413774726766809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1225412270275849817844539 1838118405413774726766809)
            ·
              refine ⟨1378588804060331045075107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1838118405413774726766809 1378588804060331045075107)
              ·
                refine ⟨2067883206090496567612661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1378588804060331045075107 2067883206090496567612661)
                ·
                  refine ⟨193864050570984053213687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2067883206090496567612661 193864050570984053213687)
                  ·
                    rfl

theorem cell21_849485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_849485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_849485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_849485 prefixEnd_849485 := by exact prefixLift 849485
  have htrace : WordTrace (prefixWord ++ tailWord_849485) baseStart_849485 baseEnd_849485 := by
    simpa [prefixWord, tailWord_849485, baseEnd_849485] using wordTrace_append hprefix tailTrace_849485
  have hstable : (prefixWord ++ tailWord_849485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849485).length < 2 ^ (prefixWord ++ tailWord_849485).sum := by decide
  have hdescent : baseEnd_849485 < baseStart_849485 := by decide
  rcases family_descends (prefixWord ++ tailWord_849485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849541 : List Nat := [1, 3, 1, 1, 4, 1, 1, 3, 6]
def baseStart_849541 : Nat := 118140960795 + 849541 * 2 ^ 59
def prefixEnd_849541 : Nat := 4983230072969 + 3 ^ 40 * 849541 * 2
def baseEnd_849541 : Nat := 193876830533940400280239

theorem tailTrace_849541 : CollatzResearch.WordTrace tailWord_849541 prefixEnd_849541 193876830533940400280239 := by
  unfold tailWord_849541
  simp only [CollatzResearch.WordTrace]
  refine ⟨30985305815265521896700477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20656870543510347931133651 30985305815265521896700477)
  ·
    refine ⟨11619489680724570711262679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30985305815265521896700477 11619489680724570711262679)
    ·
      refine ⟨17429234521086856066894019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11619489680724570711262679 17429234521086856066894019)
      ·
        refine ⟨26143851781630284100341029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17429234521086856066894019 26143851781630284100341029)
        ·
          refine ⟨4901972209055678268813943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26143851781630284100341029 4901972209055678268813943)
          ·
            refine ⟨7352958313583517403220915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4901972209055678268813943 7352958313583517403220915)
            ·
              refine ⟨11029437470375276104831373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7352958313583517403220915 11029437470375276104831373)
              ·
                refine ⟨4136039051390728539311765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11029437470375276104831373 4136039051390728539311765)
                ·
                  refine ⟨193876830533940400280239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4136039051390728539311765 193876830533940400280239)
                  ·
                    rfl

theorem cell21_849541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_849541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_849541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_849541 prefixEnd_849541 := by exact prefixLift 849541
  have htrace : WordTrace (prefixWord ++ tailWord_849541) baseStart_849541 baseEnd_849541 := by
    simpa [prefixWord, tailWord_849541, baseEnd_849541] using wordTrace_append hprefix tailTrace_849541
  have hstable : (prefixWord ++ tailWord_849541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849541).length < 2 ^ (prefixWord ++ tailWord_849541).sum := by decide
  have hdescent : baseEnd_849541 < baseStart_849541 := by decide
  rcases family_descends (prefixWord ++ tailWord_849541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849572 : List Nat := [2, 3, 1, 2, 2, 2, 2, 7]
def baseStart_849572 : Nat := 118140960795 + 849572 * 2 ^ 59
def prefixEnd_849572 : Nat := 4983230072969 + 3 ^ 40 * 849572 * 2
def baseEnd_849572 : Nat := 64627968385430411754503

theorem tailTrace_849572 : CollatzResearch.WordTrace tailWord_849572 prefixEnd_849572 64627968385430411754503 := by
  unfold tailWord_849572
  simp only [CollatzResearch.WordTrace]
  refine ⟨15493218239076607095539485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20657624318768809460719313 15493218239076607095539485)
  ·
    refine ⟨5809956839653727660827307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15493218239076607095539485 5809956839653727660827307)
    ·
      refine ⟨8714935259480591491240961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5809956839653727660827307 8714935259480591491240961)
      ·
        refine ⟨6536201444610443618430721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8714935259480591491240961 6536201444610443618430721)
        ·
          refine ⟨4902151083457832713823041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6536201444610443618430721 4902151083457832713823041)
          ·
            refine ⟨3676613312593374535367281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4902151083457832713823041 3676613312593374535367281)
            ·
              refine ⟨2757459984445030901525461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3676613312593374535367281 2757459984445030901525461)
              ·
                refine ⟨64627968385430411754503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2757459984445030901525461 64627968385430411754503)
                ·
                  rfl

theorem cell21_849572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 7].length) (baseStart_849572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_849572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_849572 prefixEnd_849572 := by exact prefixLift 849572
  have htrace : WordTrace (prefixWord ++ tailWord_849572) baseStart_849572 baseEnd_849572 := by
    simpa [prefixWord, tailWord_849572, baseEnd_849572] using wordTrace_append hprefix tailTrace_849572
  have hstable : (prefixWord ++ tailWord_849572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849572).length < 2 ^ (prefixWord ++ tailWord_849572).sum := by decide
  have hdescent : baseEnd_849572 < baseStart_849572 := by decide
  rcases family_descends (prefixWord ++ tailWord_849572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849589 : List Nat := [1, 3, 3, 3, 3, 8]
def baseStart_849589 : Nat := 118140960795 + 849589 * 2 ^ 59
def prefixEnd_849589 : Nat := 4983230072969 + 3 ^ 40 * 849589 * 2
def baseEnd_849589 : Nat := 7181029066218629017783

theorem tailTrace_849589 : CollatzResearch.WordTrace tailWord_849589 prefixEnd_849589 7181029066218629017783 := by
  unfold tailWord_849589
  simp only [CollatzResearch.WordTrace]
  refine ⟨30987056519091626094447821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20658037679394417396298547 30987056519091626094447821)
  ·
    refine ⟨11620146194659359785417933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30987056519091626094447821 11620146194659359785417933)
    ·
      refine ⟨4357554822997259919531725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11620146194659359785417933 4357554822997259919531725)
      ·
        refine ⟨1634083058623972469824397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4357554822997259919531725 1634083058623972469824397)
        ·
          refine ⟨612781146983989676184149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1634083058623972469824397 612781146983989676184149)
          ·
            refine ⟨7181029066218629017783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 612781146983989676184149 7181029066218629017783)
            ·
              rfl

theorem cell21_849589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 8].length) (baseStart_849589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_849589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_849589 prefixEnd_849589 := by exact prefixLift 849589
  have htrace : WordTrace (prefixWord ++ tailWord_849589) baseStart_849589 baseEnd_849589 := by
    simpa [prefixWord, tailWord_849589, baseEnd_849589] using wordTrace_append hprefix tailTrace_849589
  have hstable : (prefixWord ++ tailWord_849589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849589).length < 2 ^ (prefixWord ++ tailWord_849589).sum := by decide
  have hdescent : baseEnd_849589 < baseStart_849589 := by decide
  rcases family_descends (prefixWord ++ tailWord_849589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849620 : List Nat := [2, 4, 1, 3, 1, 2, 1, 2, 5]
def baseStart_849620 : Nat := 118140960795 + 849620 * 2 ^ 59
def prefixEnd_849620 : Nat := 4983230072969 + 3 ^ 40 * 849620 * 2
def baseEnd_849620 : Nat := 193894859410253818463411

theorem tailTrace_849620 : CollatzResearch.WordTrace tailWord_849620 prefixEnd_849620 193894859410253818463411 := by
  unfold tailWord_849620
  simp only [CollatzResearch.WordTrace]
  refine ⟨15494093590989659194413157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20658791454652878925884209 15494093590989659194413157)
  ·
    refine ⟨2905142548310561098952467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15494093590989659194413157 2905142548310561098952467)
    ·
      refine ⟨4357713822465841648428701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2905142548310561098952467 4357713822465841648428701)
      ·
        refine ⟨1634142683424690618160763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4357713822465841648428701 1634142683424690618160763)
        ·
          refine ⟨2451214025137035927241145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1634142683424690618160763 2451214025137035927241145)
          ·
            refine ⟨1838410518852776945430859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2451214025137035927241145 1838410518852776945430859)
            ·
              refine ⟨2757615778279165418146289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1838410518852776945430859 2757615778279165418146289)
              ·
                refine ⟨2068211833709374063609717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2757615778279165418146289 2068211833709374063609717)
                ·
                  refine ⟨193894859410253818463411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2068211833709374063609717 193894859410253818463411)
                  ·
                    rfl

theorem cell21_849620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_849620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_849620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_849620 prefixEnd_849620 := by exact prefixLift 849620
  have htrace : WordTrace (prefixWord ++ tailWord_849620) baseStart_849620 baseEnd_849620 := by
    simpa [prefixWord, tailWord_849620, baseEnd_849620] using wordTrace_append hprefix tailTrace_849620
  have hstable : (prefixWord ++ tailWord_849620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849620).length < 2 ^ (prefixWord ++ tailWord_849620).sum := by decide
  have hdescent : baseEnd_849620 < baseStart_849620 := by decide
  rcases family_descends (prefixWord ++ tailWord_849620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849682 : List Nat := [3, 2, 4, 1, 1, 1, 4, 5]
def baseStart_849682 : Nat := 118140960795 + 849682 * 2 ^ 59
def prefixEnd_849682 : Nat := 4983230072969 + 3 ^ 40 * 849682 * 2
def baseEnd_849682 : Nat := 64636336218318496143317

theorem tailTrace_849682 : CollatzResearch.WordTrace tailWord_849682 prefixEnd_849682 64636336218318496143317 := by
  unfold tailWord_849682
  simp only [CollatzResearch.WordTrace]
  refine ⟨7747612126938675744395825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20660299005169801985055533 7747612126938675744395825)
  ·
    refine ⟨5810709095204006808296869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7747612126938675744395825 5810709095204006808296869)
    ·
      refine ⟨1089507955350751276555663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5810709095204006808296869 1089507955350751276555663)
      ·
        refine ⟨1634261933026126914833495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1089507955350751276555663 1634261933026126914833495)
        ·
          refine ⟨2451392899539190372250243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1634261933026126914833495 2451392899539190372250243)
          ·
            refine ⟨3677089349308785558375365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2451392899539190372250243 3677089349308785558375365)
            ·
              refine ⟨689454252995397292195381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3677089349308785558375365 689454252995397292195381)
              ·
                refine ⟨64636336218318496143317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 689454252995397292195381 64636336218318496143317)
                ·
                  rfl

theorem cell21_849682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 5].length) (baseStart_849682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_849682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_849682 prefixEnd_849682 := by exact prefixLift 849682
  have htrace : WordTrace (prefixWord ++ tailWord_849682) baseStart_849682 baseEnd_849682 := by
    simpa [prefixWord, tailWord_849682, baseEnd_849682] using wordTrace_append hprefix tailTrace_849682
  have hstable : (prefixWord ++ tailWord_849682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849682).length < 2 ^ (prefixWord ++ tailWord_849682).sum := by decide
  have hdescent : baseEnd_849682 < baseStart_849682 := by decide
  rcases family_descends (prefixWord ++ tailWord_849682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849713 : List Nat := [1, 2, 2, 3, 2, 3, 3, 2, 3]
def baseStart_849713 : Nat := 118140960795 + 849713 * 2 ^ 59
def prefixEnd_849713 : Nat := 4983230072969 + 3 ^ 40 * 849713 * 2
def baseEnd_849713 : Nat := 193916083277306323413221

theorem tailTrace_849713 : CollatzResearch.WordTrace tailWord_849713 prefixEnd_849713 193916083277306323413221 := by
  unfold tailWord_849713
  simp only [CollatzResearch.WordTrace]
  refine ⟨30991579170642395271961793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20661052780428263514641195 30991579170642395271961793)
  ·
    refine ⟨23243684377981796453971345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30991579170642395271961793 23243684377981796453971345)
    ·
      refine ⟨17432763283486347340478509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23243684377981796453971345 17432763283486347340478509)
      ·
        refine ⟨6537286231307380252679441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17432763283486347340478509 6537286231307380252679441)
        ·
          refine ⟨4902964673480535189509581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6537286231307380252679441 4902964673480535189509581)
          ·
            refine ⟨1838611752555200696066093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4902964673480535189509581 1838611752555200696066093)
            ·
              refine ⟨689479407208200261024785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1838611752555200696066093 689479407208200261024785)
              ·
                refine ⟨517109555406150195768589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 689479407208200261024785 517109555406150195768589)
                ·
                  refine ⟨193916083277306323413221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 517109555406150195768589 193916083277306323413221)
                  ·
                    rfl

theorem cell21_849713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 2, 3].length) (baseStart_849713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_849713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_849713 prefixEnd_849713 := by exact prefixLift 849713
  have htrace : WordTrace (prefixWord ++ tailWord_849713) baseStart_849713 baseEnd_849713 := by
    simpa [prefixWord, tailWord_849713, baseEnd_849713] using wordTrace_append hprefix tailTrace_849713
  have hstable : (prefixWord ++ tailWord_849713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849713).length < 2 ^ (prefixWord ++ tailWord_849713).sum := by decide
  have hdescent : baseEnd_849713 < baseStart_849713 := by decide
  rcases family_descends (prefixWord ++ tailWord_849713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849738 : List Nat := [3, 1, 2, 1, 1, 1, 4, 1, 7]
def baseStart_849738 : Nat := 118140960795 + 849738 * 2 ^ 59
def prefixEnd_849738 : Nat := 4983230072969 + 3 ^ 40 * 849738 * 2
def baseEnd_849738 : Nat := 193921788617911835496503

theorem tailTrace_849738 : CollatzResearch.WordTrace tailWord_849738 prefixEnd_849738 193921788617911835496503 := by
  unfold tailWord_849738
  simp only [CollatzResearch.WordTrace]
  refine ⟨7748122748887956135405467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20661660663701216361081245 7748122748887956135405467)
  ·
    refine ⟨11622184123331934203108201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7748122748887956135405467 11622184123331934203108201)
    ·
      refine ⟨8716638092498950652331151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11622184123331934203108201 8716638092498950652331151)
      ·
        refine ⟨13074957138748425978496727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8716638092498950652331151 13074957138748425978496727)
        ·
          refine ⟨19612435708122638967745091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13074957138748425978496727 19612435708122638967745091)
          ·
            refine ⟨29418653562183958451617637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19612435708122638967745091 29418653562183958451617637)
            ·
              refine ⟨5515997542909492209678307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29418653562183958451617637 5515997542909492209678307)
              ·
                refine ⟨8273996314364238314517461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5515997542909492209678307 8273996314364238314517461)
                ·
                  refine ⟨193921788617911835496503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8273996314364238314517461 193921788617911835496503)
                  ·
                    rfl

theorem cell21_849738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_849738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_849738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_849738 prefixEnd_849738 := by exact prefixLift 849738
  have htrace : WordTrace (prefixWord ++ tailWord_849738) baseStart_849738 baseEnd_849738 := by
    simpa [prefixWord, tailWord_849738, baseEnd_849738] using wordTrace_append hprefix tailTrace_849738
  have hstable : (prefixWord ++ tailWord_849738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849738).length < 2 ^ (prefixWord ++ tailWord_849738).sum := by decide
  have hdescent : baseEnd_849738 < baseStart_849738 := by decide
  rcases family_descends (prefixWord ++ tailWord_849738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849741 : List Nat := [1, 6, 1, 2, 1, 1, 2, 7]
def baseStart_849741 : Nat := 118140960795 + 849741 * 2 ^ 59
def prefixEnd_849741 : Nat := 4983230072969 + 3 ^ 40 * 849741 * 2
def baseEnd_849741 : Nat := 64640824419594832315499

theorem tailTrace_849741 : CollatzResearch.WordTrace tailWord_849741 prefixEnd_849741 64640824419594832315499 := by
  unfold tailWord_849741
  simp only [CollatzResearch.WordTrace]
  refine ⟨30992600414540956053981077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20661733609693970702654051 30992600414540956053981077)
  ·
    refine ⟨1452778144431607315030363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30992600414540956053981077 1452778144431607315030363)
    ·
      refine ⟨2179167216647410972545545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1452778144431607315030363 2179167216647410972545545)
      ·
        refine ⟨1634375412485558229409159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2179167216647410972545545 1634375412485558229409159)
        ·
          refine ⟨2451563118728337344113739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1634375412485558229409159 2451563118728337344113739)
          ·
            refine ⟨3677344678092506016170609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2451563118728337344113739 3677344678092506016170609)
            ·
              refine ⟨2758008508569379512127957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3677344678092506016170609 2758008508569379512127957)
              ·
                refine ⟨64640824419594832315499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2758008508569379512127957 64640824419594832315499)
                ·
                  rfl

theorem cell21_849741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 7].length) (baseStart_849741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_849741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_849741 prefixEnd_849741 := by exact prefixLift 849741
  have htrace : WordTrace (prefixWord ++ tailWord_849741) baseStart_849741 baseEnd_849741 := by
    simpa [prefixWord, tailWord_849741, baseEnd_849741] using wordTrace_append hprefix tailTrace_849741
  have hstable : (prefixWord ++ tailWord_849741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849741).length < 2 ^ (prefixWord ++ tailWord_849741).sum := by decide
  have hdescent : baseEnd_849741 < baseStart_849741 := by decide
  rcases family_descends (prefixWord ++ tailWord_849741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849772 : List Nat := [2, 2, 1, 1, 4, 3, 1, 4, 3]
def baseStart_849772 : Nat := 118140960795 + 849772 * 2 ^ 59
def prefixEnd_849772 : Nat := 4983230072969 + 3 ^ 40 * 849772 * 2
def baseEnd_849772 : Nat := 193929547881135331929767

theorem tailTrace_849772 : CollatzResearch.WordTrace tailWord_849772 prefixEnd_849772 193929547881135331929767 := by
  unfold tailWord_849772
  simp only [CollatzResearch.WordTrace]
  refine ⟨15496865538714324174179785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20662487384952432232239713 15496865538714324174179785)
  ·
    refine ⟨11622649154035743130634839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15496865538714324174179785 11622649154035743130634839)
    ·
      refine ⟨17433973731053614695952259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11622649154035743130634839 17433973731053614695952259)
      ·
        refine ⟨26150960596580422043928389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17433973731053614695952259 26150960596580422043928389)
        ·
          refine ⟨4903305111858829133236573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26150960596580422043928389 4903305111858829133236573)
          ·
            refine ⟨1838739416947060924963715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4903305111858829133236573 1838739416947060924963715)
            ·
              refine ⟨2758109125420591387445573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1838739416947060924963715 2758109125420591387445573)
              ·
                refine ⟨517145461016360885146045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2758109125420591387445573 517145461016360885146045)
                ·
                  refine ⟨193929547881135331929767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 517145461016360885146045 193929547881135331929767)
                  ·
                    rfl

theorem cell21_849772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 4, 3].length) (baseStart_849772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_849772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_849772 prefixEnd_849772 := by exact prefixLift 849772
  have htrace : WordTrace (prefixWord ++ tailWord_849772) baseStart_849772 baseEnd_849772 := by
    simpa [prefixWord, tailWord_849772, baseEnd_849772] using wordTrace_append hprefix tailTrace_849772
  have hstable : (prefixWord ++ tailWord_849772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849772).length < 2 ^ (prefixWord ++ tailWord_849772).sum := by decide
  have hdescent : baseEnd_849772 < baseStart_849772 := by decide
  rcases family_descends (prefixWord ++ tailWord_849772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849806 : List Nat := [4, 1, 1, 5, 1, 1, 2, 3, 3]
def baseStart_849806 : Nat := 118140960795 + 849806 * 2 ^ 59
def prefixEnd_849806 : Nat := 4983230072969 + 3 ^ 40 * 849806 * 2
def baseEnd_849806 : Nat := 193937307144358828363031

theorem tailTrace_849806 : CollatzResearch.WordTrace tailWord_849806 prefixEnd_849806 193937307144358828363031 := by
  unfold tailWord_849806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3874371394913184019387159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20663314106203648103398181 3874371394913184019387159)
  ·
    refine ⟨5811557092369776029080739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3874371394913184019387159 5811557092369776029080739)
    ·
      refine ⟨8717335638554664043621109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5811557092369776029080739 8717335638554664043621109)
      ·
        refine ⟨817250216114499754089479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8717335638554664043621109 817250216114499754089479)
        ·
          refine ⟨1225875324171749631134219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 817250216114499754089479 1225875324171749631134219)
          ·
            refine ⟨1838812986257624446701329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1225875324171749631134219 1838812986257624446701329)
            ·
              refine ⟨1379109739693218335025997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1838812986257624446701329 1379109739693218335025997)
              ·
                refine ⟨517166152384956875634749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1379109739693218335025997 517166152384956875634749)
                ·
                  refine ⟨193937307144358828363031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 517166152384956875634749 193937307144358828363031)
                  ·
                    rfl

theorem cell21_849806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_849806 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_849806 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_849806 prefixEnd_849806 := by exact prefixLift 849806
  have htrace : WordTrace (prefixWord ++ tailWord_849806) baseStart_849806 baseEnd_849806 := by
    simpa [prefixWord, tailWord_849806, baseEnd_849806] using wordTrace_append hprefix tailTrace_849806
  have hstable : (prefixWord ++ tailWord_849806).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849806).length < 2 ^ (prefixWord ++ tailWord_849806).sum := by decide
  have hdescent : baseEnd_849806 < baseStart_849806 := by decide
  rcases family_descends (prefixWord ++ tailWord_849806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849831 : List Nat := [1, 1, 6, 1, 2, 1, 1, 3, 5]
def baseStart_849831 : Nat := 118140960795 + 849831 * 2 ^ 59
def prefixEnd_849831 : Nat := 4983230072969 + 3 ^ 40 * 849831 * 2
def baseEnd_849831 : Nat := 193943012484964340446313

theorem tailTrace_849831 : CollatzResearch.WordTrace tailWord_849831 prefixEnd_849831 193943012484964340446313 := by
  unfold tailWord_849831
  simp only [CollatzResearch.WordTrace]
  refine ⟨30995882984214901424757347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20663921989476600949838231 30995882984214901424757347)
  ·
    refine ⟨46493824476322352137136021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30995882984214901424757347 46493824476322352137136021)
    ·
      refine ⟨2179398022327610256428251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 46493824476322352137136021 2179398022327610256428251)
      ·
        refine ⟨3269097033491415384642377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2179398022327610256428251 3269097033491415384642377)
        ·
          refine ⟨2451822775118561538481783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3269097033491415384642377 2451822775118561538481783)
          ·
            refine ⟨3677734162677842307722675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2451822775118561538481783 3677734162677842307722675)
            ·
              refine ⟨5516601244016763461584013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3677734162677842307722675 5516601244016763461584013)
              ·
                refine ⟨2068725466506286298094005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5516601244016763461584013 2068725466506286298094005)
                ·
                  refine ⟨193943012484964340446313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2068725466506286298094005 193943012484964340446313)
                  ·
                    rfl

theorem cell21_849831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 5].length) (baseStart_849831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_849831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_849831 prefixEnd_849831 := by exact prefixLift 849831
  have htrace : WordTrace (prefixWord ++ tailWord_849831) baseStart_849831 baseEnd_849831 := by
    simpa [prefixWord, tailWord_849831, baseEnd_849831] using wordTrace_append hprefix tailTrace_849831
  have hstable : (prefixWord ++ tailWord_849831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849831).length < 2 ^ (prefixWord ++ tailWord_849831).sum := by decide
  have hdescent : baseEnd_849831 < baseStart_849831 := by decide
  rcases family_descends (prefixWord ++ tailWord_849831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849933 : List Nat := [1, 7, 1, 2, 2, 1, 2, 2, 3]
def baseStart_849933 : Nat := 118140960795 + 849933 * 2 ^ 59
def prefixEnd_849933 : Nat := 4983230072969 + 3 ^ 40 * 849933 * 2
def baseEnd_849933 : Nat := 193966290274634829746105

theorem tailTrace_849933 : CollatzResearch.WordTrace tailWord_849933 prefixEnd_849933 193966290274634829746105 := by
  unfold tailWord_849933
  simp only [CollatzResearch.WordTrace]
  refine ⟨30999603229845372844970453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20666402153230248563313635 30999603229845372844970453)
  ·
    refine ⟨726553200699500926053995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 30999603229845372844970453 726553200699500926053995)
    ·
      refine ⟨1089829801049251389080993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 726553200699500926053995 1089829801049251389080993)
      ·
        refine ⟨817372350786938541810745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1089829801049251389080993 817372350786938541810745)
        ·
          refine ⟨613029263090203906358059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 817372350786938541810745 613029263090203906358059)
          ·
            refine ⟨919543894635305859537089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 613029263090203906358059 919543894635305859537089)
            ·
              refine ⟨689657920976479394652817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 919543894635305859537089 689657920976479394652817)
              ·
                refine ⟨517243440732359545989613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 689657920976479394652817 517243440732359545989613)
                ·
                  refine ⟨193966290274634829746105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 517243440732359545989613 193966290274634829746105)
                  ·
                    rfl

theorem cell21_849933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_849933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_849933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_849933 prefixEnd_849933 := by exact prefixLift 849933
  have htrace : WordTrace (prefixWord ++ tailWord_849933) baseStart_849933 baseEnd_849933 := by
    simpa [prefixWord, tailWord_849933, baseEnd_849933] using wordTrace_append hprefix tailTrace_849933
  have hstable : (prefixWord ++ tailWord_849933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849933).length < 2 ^ (prefixWord ++ tailWord_849933).sum := by decide
  have hdescent : baseEnd_849933 < baseStart_849933 := by decide
  rcases family_descends (prefixWord ++ tailWord_849933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849983 : List Nat := [1, 1, 2, 2, 3, 1, 3, 5, 3]
def baseStart_849983 : Nat := 118140960795 + 849983 * 2 ^ 59
def prefixEnd_849983 : Nat := 4983230072969 + 3 ^ 40 * 849983 * 2
def baseEnd_849983 : Nat := 193977700955845853912669

theorem tailTrace_849983 : CollatzResearch.WordTrace tailWord_849983 prefixEnd_849983 193977700955845853912669 := by
  unfold tailWord_849983
  simp only [CollatzResearch.WordTrace]
  refine ⟨31001426879664231384290603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20667617919776154256193735 31001426879664231384290603)
  ·
    refine ⟨46502140319496347076435905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31001426879664231384290603 46502140319496347076435905)
    ·
      refine ⟨34876605239622260307326929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46502140319496347076435905 34876605239622260307326929)
      ·
        refine ⟨26157453929716695230495197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34876605239622260307326929 26157453929716695230495197)
        ·
          refine ⟨9809045223643760711435699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26157453929716695230495197 9809045223643760711435699)
          ·
            refine ⟨14713567835465641067153549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9809045223643760711435699 14713567835465641067153549)
            ·
              refine ⟨5517587938299615400182581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14713567835465641067153549 5517587938299615400182581)
              ·
                refine ⟨517273869215588943767117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5517587938299615400182581 517273869215588943767117)
                ·
                  refine ⟨193977700955845853912669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 517273869215588943767117 193977700955845853912669)
                  ·
                    rfl

theorem cell21_849983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 5, 3].length) (baseStart_849983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_849983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_849983 prefixEnd_849983 := by exact prefixLift 849983
  have htrace : WordTrace (prefixWord ++ tailWord_849983) baseStart_849983 baseEnd_849983 := by
    simpa [prefixWord, tailWord_849983, baseEnd_849983] using wordTrace_append hprefix tailTrace_849983
  have hstable : (prefixWord ++ tailWord_849983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849983).length < 2 ^ (prefixWord ++ tailWord_849983).sum := by decide
  have hdescent : baseEnd_849983 < baseStart_849983 := by decide
  rcases family_descends (prefixWord ++ tailWord_849983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850028 : List Nat := [2, 2, 1, 1, 3, 3, 4, 5]
def baseStart_850028 : Nat := 118140960795 + 850028 * 2 ^ 59
def prefixEnd_850028 : Nat := 4983230072969 + 3 ^ 40 * 850028 * 2
def baseEnd_850028 : Nat := 64662656856311925220859

theorem tailTrace_850028 : CollatzResearch.WordTrace tailWord_850028 prefixEnd_850028 64662656856311925220859 := by
  unfold tailWord_850028
  simp only [CollatzResearch.WordTrace]
  refine ⟨15501534082250602034839369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20668712109667469379785825 15501534082250602034839369)
  ·
    refine ⟨11626150561687951526129527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15501534082250602034839369 11626150561687951526129527)
    ·
      refine ⟨17439225842531927289194291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11626150561687951526129527 17439225842531927289194291)
      ·
        refine ⟨26158838763797890933791437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17439225842531927289194291 26158838763797890933791437)
        ·
          refine ⟨9809564536424209100171789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26158838763797890933791437 9809564536424209100171789)
          ·
            refine ⟨3678586701159078412564421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9809564536424209100171789 3678586701159078412564421)
            ·
              refine ⟨689735006467327202355829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3678586701159078412564421 689735006467327202355829)
              ·
                refine ⟨64662656856311925220859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 689735006467327202355829 64662656856311925220859)
                ·
                  rfl

theorem cell21_850028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 5].length) (baseStart_850028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_850028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_850028 prefixEnd_850028 := by exact prefixLift 850028
  have htrace : WordTrace (prefixWord ++ tailWord_850028) baseStart_850028 baseEnd_850028 := by
    simpa [prefixWord, tailWord_850028, baseEnd_850028] using wordTrace_append hprefix tailTrace_850028
  have hstable : (prefixWord ++ tailWord_850028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850028).length < 2 ^ (prefixWord ++ tailWord_850028).sum := by decide
  have hdescent : baseEnd_850028 < baseStart_850028 := by decide
  rcases family_descends (prefixWord ++ tailWord_850028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850110 : List Nat := [4, 2, 1, 1, 4, 2, 2, 2, 3]
def baseStart_850110 : Nat := 118140960795 + 850110 * 2 ^ 59
def prefixEnd_850110 : Nat := 4983230072969 + 3 ^ 40 * 850110 * 2
def baseEnd_850110 : Nat := 194006684086121855295743

theorem tailTrace_850110 : CollatzResearch.WordTrace tailWord_850110 prefixEnd_850110 194006684086121855295743 := by
  unfold tailWord_850110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3875757368775516509270473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20670705966802754716109189 3875757368775516509270473)
  ·
    refine ⟨2906818026581637381952855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3875757368775516509270473 2906818026581637381952855)
    ·
      refine ⟨4360227039872456072929283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2906818026581637381952855 4360227039872456072929283)
      ·
        refine ⟨6540340559808684109393925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4360227039872456072929283 6540340559808684109393925)
        ·
          refine ⟨1226313854964128270511361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6540340559808684109393925 1226313854964128270511361)
          ·
            refine ⟨919735391223096202883521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1226313854964128270511361 919735391223096202883521)
            ·
              refine ⟨689801543417322152162641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 919735391223096202883521 689801543417322152162641)
              ·
                refine ⟨517351157562991614121981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 689801543417322152162641 517351157562991614121981)
                ·
                  refine ⟨194006684086121855295743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 517351157562991614121981 194006684086121855295743)
                  ·
                    rfl

theorem cell21_850110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_850110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_850110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_850110 prefixEnd_850110 := by exact prefixLift 850110
  have htrace : WordTrace (prefixWord ++ tailWord_850110) baseStart_850110 baseEnd_850110 := by
    simpa [prefixWord, tailWord_850110, baseEnd_850110] using wordTrace_append hprefix tailTrace_850110
  have hstable : (prefixWord ++ tailWord_850110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850110).length < 2 ^ (prefixWord ++ tailWord_850110).sum := by decide
  have hdescent : baseEnd_850110 < baseStart_850110 := by decide
  rcases family_descends (prefixWord ++ tailWord_850110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850152 : List Nat := [2, 1, 4, 1, 2, 3, 2, 3, 3]
def baseStart_850152 : Nat := 118140960795 + 850152 * 2 ^ 59
def prefixEnd_850152 : Nat := 4983230072969 + 3 ^ 40 * 850152 * 2
def baseEnd_850152 : Nat := 194016269058339115595657

theorem tailTrace_850152 : CollatzResearch.WordTrace tailWord_850152 prefixEnd_850152 194016269058339115595657 := by
  unfold tailWord_850152
  simp only [CollatzResearch.WordTrace]
  refine ⟨15503795408025986623596355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20671727210701315498128473 15503795408025986623596355)
  ·
    refine ⟨23255693112038979935394533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15503795408025986623596355 23255693112038979935394533)
    ·
      refine ⟨4360442458507308737886475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23255693112038979935394533 4360442458507308737886475)
      ·
        refine ⟨6540663687760963106829713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4360442458507308737886475 6540663687760963106829713)
        ·
          refine ⟨4905497765820722330122285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6540663687760963106829713 4905497765820722330122285)
          ·
            refine ⟨1839561662182770873795857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4905497765820722330122285 1839561662182770873795857)
            ·
              refine ⟨1379671246637078155346893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1839561662182770873795857 1379671246637078155346893)
              ·
                refine ⟨517376717488904308255085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1379671246637078155346893 517376717488904308255085)
                ·
                  refine ⟨194016269058339115595657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 517376717488904308255085 194016269058339115595657)
                  ·
                    rfl

theorem cell21_850152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 3, 3].length) (baseStart_850152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_850152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_850152 prefixEnd_850152 := by exact prefixLift 850152
  have htrace : WordTrace (prefixWord ++ tailWord_850152) baseStart_850152 baseEnd_850152 := by
    simpa [prefixWord, tailWord_850152, baseEnd_850152] using wordTrace_append hprefix tailTrace_850152
  have hstable : (prefixWord ++ tailWord_850152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850152).length < 2 ^ (prefixWord ++ tailWord_850152).sum := by decide
  have hdescent : baseEnd_850152 < baseStart_850152 := by decide
  rcases family_descends (prefixWord ++ tailWord_850152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850166 : List Nat := [5, 1, 1, 1, 1, 1, 5, 2, 4]
def baseStart_850166 : Nat := 118140960795 + 850166 * 2 ^ 59
def prefixEnd_850166 : Nat := 4983230072969 + 3 ^ 40 * 850166 * 2
def baseEnd_850166 : Nat := 194019464049078202362295

theorem tailTrace_850166 : CollatzResearch.WordTrace tailWord_850166 prefixEnd_850166 194019464049078202362295 := by
  unfold tailWord_850166
  simp only [CollatzResearch.WordTrace]
  refine ⟨1938006339875078352387647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20672067625334169092134901 1938006339875078352387647)
  ·
    refine ⟨2907009509812617528581471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1938006339875078352387647 2907009509812617528581471)
    ·
      refine ⟨4360514264718926292872207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2907009509812617528581471 4360514264718926292872207)
      ·
        refine ⟨6540771397078389439308311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4360514264718926292872207 6540771397078389439308311)
        ·
          refine ⟨9811157095617584158962467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6540771397078389439308311 9811157095617584158962467)
          ·
            refine ⟨14716735643426376238443701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9811157095617584158962467 14716735643426376238443701)
            ·
              refine ⟨1379693966571222772354097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14716735643426376238443701 1379693966571222772354097)
              ·
                refine ⟨1034770474928417079265573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1379693966571222772354097 1034770474928417079265573)
                ·
                  refine ⟨194019464049078202362295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1034770474928417079265573 194019464049078202362295)
                  ·
                    rfl

theorem cell21_850166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_850166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_850166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_850166 prefixEnd_850166 := by exact prefixLift 850166
  have htrace : WordTrace (prefixWord ++ tailWord_850166) baseStart_850166 baseEnd_850166 := by
    simpa [prefixWord, tailWord_850166, baseEnd_850166] using wordTrace_append hprefix tailTrace_850166
  have hstable : (prefixWord ++ tailWord_850166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850166).length < 2 ^ (prefixWord ++ tailWord_850166).sum := by decide
  have hdescent : baseEnd_850166 < baseStart_850166 := by decide
  rcases family_descends (prefixWord ++ tailWord_850166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850228 : List Nat := [2, 5, 1, 1, 1, 4, 1, 1, 5]
def baseStart_850228 : Nat := 118140960795 + 850228 * 2 ^ 59
def prefixEnd_850228 : Nat := 4983230072969 + 3 ^ 40 * 850228 * 2
def baseEnd_850228 : Nat := 194033613293779872328835

theorem tailTrace_850228 : CollatzResearch.WordTrace tailWord_850228 prefixEnd_850228 194033613293779872328835 := by
  unfold tailWord_850228
  simp only [CollatzResearch.WordTrace]
  refine ⟨15505181381888319113479669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20673575175851092151306225 15505181381888319113479669)
  ·
    refine ⟨1453610754552029916888719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15505181381888319113479669 1453610754552029916888719)
    ·
      refine ⟨2180416131828044875333079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1453610754552029916888719 2180416131828044875333079)
      ·
        refine ⟨3270624197742067312999619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2180416131828044875333079 3270624197742067312999619)
        ·
          refine ⟨4905936296613100969499429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3270624197742067312999619 4905936296613100969499429)
          ·
            refine ⟨919863055614956431781143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4905936296613100969499429 919863055614956431781143)
            ·
              refine ⟨1379794583422434647671715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 919863055614956431781143 1379794583422434647671715)
              ·
                refine ⟨2069691875133651971507573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1379794583422434647671715 2069691875133651971507573)
                ·
                  refine ⟨194033613293779872328835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2069691875133651971507573 194033613293779872328835)
                  ·
                    rfl

theorem cell21_850228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_850228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_850228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_850228 prefixEnd_850228 := by exact prefixLift 850228
  have htrace : WordTrace (prefixWord ++ tailWord_850228) baseStart_850228 baseEnd_850228 := by
    simpa [prefixWord, tailWord_850228, baseEnd_850228] using wordTrace_append hprefix tailTrace_850228
  have hstable : (prefixWord ++ tailWord_850228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850228).length < 2 ^ (prefixWord ++ tailWord_850228).sum := by decide
  have hdescent : baseEnd_850228 < baseStart_850228 := by decide
  rcases family_descends (prefixWord ++ tailWord_850228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850239 : List Nat := [1, 1, 2, 2, 4, 1, 4, 6]
def baseStart_850239 : Nat := 118140960795 + 850239 * 2 ^ 59
def prefixEnd_850239 : Nat := 4983230072969 + 3 ^ 40 * 850239 * 2
def baseEnd_850239 : Nat := 64678707881215432548493

theorem tailTrace_850239 : CollatzResearch.WordTrace tailWord_850239 prefixEnd_850239 64678707881215432548493 := by
  unfold tailWord_850239
  simp only [CollatzResearch.WordTrace]
  refine ⟨31010763966736787105609771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20673842644491191403739847 31010763966736787105609771)
  ·
    refine ⟨46516145950105180658414657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31010763966736787105609771 46516145950105180658414657)
    ·
      refine ⟨34887109462578885493810993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46516145950105180658414657 34887109462578885493810993)
      ·
        refine ⟨26165332096934164120358245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34887109462578885493810993 26165332096934164120358245)
        ·
          refine ⟨4905999768175155772567171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26165332096934164120358245 4905999768175155772567171)
          ·
            refine ⟨7358999652262733658850757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4905999768175155772567171 7358999652262733658850757)
            ·
              refine ⟨1379812434799262561034517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7358999652262733658850757 1379812434799262561034517)
              ·
                refine ⟨64678707881215432548493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1379812434799262561034517 64678707881215432548493)
                ·
                  rfl

theorem cell21_850239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 6].length) (baseStart_850239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_850239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_850239 prefixEnd_850239 := by exact prefixLift 850239
  have htrace : WordTrace (prefixWord ++ tailWord_850239) baseStart_850239 baseEnd_850239 := by
    simpa [prefixWord, tailWord_850239, baseEnd_850239] using wordTrace_append hprefix tailTrace_850239
  have hstable : (prefixWord ++ tailWord_850239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850239).length < 2 ^ (prefixWord ++ tailWord_850239).sum := by decide
  have hdescent : baseEnd_850239 < baseStart_850239 := by decide
  rcases family_descends (prefixWord ++ tailWord_850239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850301 : List Nat := [1, 4, 1, 1, 2, 3, 2, 3, 4]
def baseStart_850301 : Nat := 118140960795 + 850301 * 2 ^ 59
def prefixEnd_850301 : Nat := 4983230072969 + 3 ^ 40 * 850301 * 2
def baseEnd_850301 : Nat := 194050272888347967612019

theorem tailTrace_850301 : CollatzResearch.WordTrace tailWord_850301 prefixEnd_850301 194050272888347967612019 := by
  unfold tailWord_850301
  simp only [CollatzResearch.WordTrace]
  refine ⟨31013025292512171694366757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20675350195008114462911171 31013025292512171694366757)
  ·
    refine ⟨5814942242346032192693767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31013025292512171694366757 5814942242346032192693767)
    ·
      refine ⟨8722413363519048289040651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5814942242346032192693767 8722413363519048289040651)
      ·
        refine ⟨13083620045278572433560977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8722413363519048289040651 13083620045278572433560977)
        ·
          refine ⟨9812715033958929325170733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13083620045278572433560977 9812715033958929325170733)
          ·
            refine ⟨3679768137734598496939025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9812715033958929325170733 3679768137734598496939025)
            ·
              refine ⟨2759826103300948872704269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3679768137734598496939025 2759826103300948872704269)
              ·
                refine ⟨1034934788737855827264101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2759826103300948872704269 1034934788737855827264101)
                ·
                  refine ⟨194050272888347967612019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1034934788737855827264101 194050272888347967612019)
                  ·
                    rfl

theorem cell21_850301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_850301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_850301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_850301 prefixEnd_850301 := by exact prefixLift 850301
  have htrace : WordTrace (prefixWord ++ tailWord_850301) baseStart_850301 baseEnd_850301 := by
    simpa [prefixWord, tailWord_850301, baseEnd_850301] using wordTrace_append hprefix tailTrace_850301
  have hstable : (prefixWord ++ tailWord_850301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850301).length < 2 ^ (prefixWord ++ tailWord_850301).sum := by decide
  have hdescent : baseEnd_850301 < baseStart_850301 := by decide
  rcases family_descends (prefixWord ++ tailWord_850301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850329 : List Nat := [1, 2, 1, 2, 1, 4, 1, 2, 7]
def baseStart_850329 : Nat := 118140960795 + 850329 * 2 ^ 59
def prefixEnd_850329 : Nat := 4983230072969 + 3 ^ 40 * 850329 * 2
def baseEnd_850329 : Nat := 194056662869826141145295

theorem tailTrace_850329 : CollatzResearch.WordTrace tailWord_850329 prefixEnd_850329 194056662869826141145295 := by
  unfold tailWord_850329
  simp only [CollatzResearch.WordTrace]
  refine ⟨31014046536410732476386041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20676031024273821650924027 31014046536410732476386041)
  ·
    refine ⟨23260534902308049357289531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31014046536410732476386041 23260534902308049357289531)
    ·
      refine ⟨34890802353462074035934297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23260534902308049357289531 34890802353462074035934297)
      ·
        refine ⟨26168101765096555526950723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34890802353462074035934297 26168101765096555526950723)
        ·
          refine ⟨39252152647644833290426085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26168101765096555526950723 39252152647644833290426085)
          ·
            refine ⟨7359778621433406241954891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39252152647644833290426085 7359778621433406241954891)
            ·
              refine ⟨11039667932150109362932337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7359778621433406241954891 11039667932150109362932337)
              ·
                refine ⟨8279750949112582022199253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11039667932150109362932337 8279750949112582022199253)
                ·
                  refine ⟨194056662869826141145295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8279750949112582022199253 194056662869826141145295)
                  ·
                    rfl

theorem cell21_850329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 7].length) (baseStart_850329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_850329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_850329 prefixEnd_850329 := by exact prefixLift 850329
  have htrace : WordTrace (prefixWord ++ tailWord_850329) baseStart_850329 baseEnd_850329 := by
    simpa [prefixWord, tailWord_850329, baseEnd_850329] using wordTrace_append hprefix tailTrace_850329
  have hstable : (prefixWord ++ tailWord_850329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850329).length < 2 ^ (prefixWord ++ tailWord_850329).sum := by decide
  have hdescent : baseEnd_850329 < baseStart_850329 := by decide
  rcases family_descends (prefixWord ++ tailWord_850329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850422 : List Nat := [5, 1, 1, 1, 2, 1, 2, 1, 7]
def baseStart_850422 : Nat := 118140960795 + 850422 * 2 ^ 59
def prefixEnd_850422 : Nat := 4983230072969 + 3 ^ 40 * 850422 * 2
def baseEnd_850422 : Nat := 194077886736878646095105

theorem tailTrace_850422 : CollatzResearch.WordTrace tailWord_850422 prefixEnd_850422 194077886736878646095105 := by
  unfold tailWord_850422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1938589907817113084970095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20678292350049206239681013 1938589907817113084970095)
  ·
    refine ⟨2907884861725669627455143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1938589907817113084970095 2907884861725669627455143)
    ·
      refine ⟨4361827292588504441182715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2907884861725669627455143 4361827292588504441182715)
      ·
        refine ⟨6542740938882756661774073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4361827292588504441182715 6542740938882756661774073)
        ·
          refine ⟨4907055704162067496330555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6542740938882756661774073 4907055704162067496330555)
          ·
            refine ⟨7360583556243101244495833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4907055704162067496330555 7360583556243101244495833)
            ·
              refine ⟨5520437667182325933371875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7360583556243101244495833 5520437667182325933371875)
              ·
                refine ⟨8280656500773488900057813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5520437667182325933371875 8280656500773488900057813)
                ·
                  refine ⟨194077886736878646095105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8280656500773488900057813 194077886736878646095105)
                  ·
                    rfl

theorem cell21_850422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_850422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_850422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_850422 prefixEnd_850422 := by exact prefixLift 850422
  have htrace : WordTrace (prefixWord ++ tailWord_850422) baseStart_850422 baseEnd_850422 := by
    simpa [prefixWord, tailWord_850422, baseEnd_850422] using wordTrace_append hprefix tailTrace_850422
  have hstable : (prefixWord ++ tailWord_850422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850422).length < 2 ^ (prefixWord ++ tailWord_850422).sum := by decide
  have hdescent : baseEnd_850422 < baseStart_850422 := by decide
  rcases family_descends (prefixWord ++ tailWord_850422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850450 : List Nat := [3, 2, 16]
def baseStart_850450 : Nat := 118140960795 + 850450 * 2 ^ 59
def prefixEnd_850450 : Nat := 4983230072969 + 3 ^ 40 * 850450 * 2
def baseEnd_850450 : Nat := 266233575745345431589

theorem tailTrace_850450 : CollatzResearch.WordTrace tailWord_850450 prefixEnd_850450 266233575745345431589 := by
  unfold tailWord_850450
  simp only [CollatzResearch.WordTrace]
  refine ⟨7754614942243092535385201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20678973179314913427693869 7754614942243092535385201)
  ·
    refine ⟨5815961206682319401538901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7754614942243092535385201 5815961206682319401538901)
    ·
      refine ⟨266233575745345431589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 16 5815961206682319401538901 266233575745345431589)
      ·
        rfl

theorem cell21_850450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 16].length) (baseStart_850450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_850450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_850450 prefixEnd_850450 := by exact prefixLift 850450
  have htrace : WordTrace (prefixWord ++ tailWord_850450) baseStart_850450 baseEnd_850450 := by
    simpa [prefixWord, tailWord_850450, baseEnd_850450] using wordTrace_append hprefix tailTrace_850450
  have hstable : (prefixWord ++ tailWord_850450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850450).length < 2 ^ (prefixWord ++ tailWord_850450).sum := by decide
  have hdescent : baseEnd_850450 < baseStart_850450 := by decide
  rcases family_descends (prefixWord ++ tailWord_850450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850453 : List Nat := [1, 3, 2, 1, 3, 1, 4, 2, 4]
def baseStart_850453 : Nat := 118140960795 + 850453 * 2 ^ 59
def prefixEnd_850453 : Nat := 4983230072969 + 3 ^ 40 * 850453 * 2
def baseEnd_850453 : Nat := 194084961359229481078375

theorem tailTrace_850453 : CollatzResearch.WordTrace tailWord_850453 prefixEnd_850453 194084961359229481078375 := by
  unfold tailWord_850453
  simp only [CollatzResearch.WordTrace]
  refine ⟨31018569187961501653900013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20679046125307667769266675 31018569187961501653900013)
  ·
    refine ⟨11631963445485563120212505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31018569187961501653900013 11631963445485563120212505)
    ·
      refine ⟨8723972584114172340159379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11631963445485563120212505 8723972584114172340159379)
      ·
        refine ⟨13085958876171258510239069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8723972584114172340159379 13085958876171258510239069)
        ·
          refine ⟨4907234578564221941339651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13085958876171258510239069 4907234578564221941339651)
          ·
            refine ⟨7360851867846332912009477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4907234578564221941339651 7360851867846332912009477)
            ·
              refine ⟨1380159725221187421001777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7360851867846332912009477 1380159725221187421001777)
              ·
                refine ⟨1035119793915890565751333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1380159725221187421001777 1035119793915890565751333)
                ·
                  refine ⟨194084961359229481078375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1035119793915890565751333 194084961359229481078375)
                  ·
                    rfl

theorem cell21_850453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_850453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_850453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_850453 prefixEnd_850453 := by exact prefixLift 850453
  have htrace : WordTrace (prefixWord ++ tailWord_850453) baseStart_850453 baseEnd_850453 := by
    simpa [prefixWord, tailWord_850453, baseEnd_850453] using wordTrace_append hprefix tailTrace_850453
  have hstable : (prefixWord ++ tailWord_850453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850453).length < 2 ^ (prefixWord ++ tailWord_850453).sum := by decide
  have hdescent : baseEnd_850453 < baseStart_850453 := by decide
  rcases family_descends (prefixWord ++ tailWord_850453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850456 : List Nat := [2, 1, 2, 3, 3, 1, 4, 2, 3]
def baseStart_850456 : Nat := 118140960795 + 850456 * 2 ^ 59
def prefixEnd_850456 : Nat := 4983230072969 + 3 ^ 40 * 850456 * 2
def baseEnd_850456 : Nat := 194085646000102142528369

theorem tailTrace_850456 : CollatzResearch.WordTrace tailWord_850456 prefixEnd_850456 194085646000102142528369 := by
  unfold tailWord_850456
  simp only [CollatzResearch.WordTrace]
  refine ⟨15509339303475316583129611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20679119071300422110839481 15509339303475316583129611)
  ·
    refine ⟨23264008955212974874694417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15509339303475316583129611 23264008955212974874694417)
    ·
      refine ⟨17448006716409731156020813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23264008955212974874694417 17448006716409731156020813)
      ·
        refine ⟨6543002518653649183507805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17448006716409731156020813 6543002518653649183507805)
        ·
          refine ⟨2453625944495118443815427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6543002518653649183507805 2453625944495118443815427)
          ·
            refine ⟨3680438916742677665723141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2453625944495118443815427 3680438916742677665723141)
            ·
              refine ⟨690082296889252062323089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3680438916742677665723141 690082296889252062323089)
              ·
                refine ⟨517561722666939046742317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 690082296889252062323089 517561722666939046742317)
                ·
                  refine ⟨194085646000102142528369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 517561722666939046742317 194085646000102142528369)
                  ·
                    rfl

theorem cell21_850456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 2, 3].length) (baseStart_850456 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_850456 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_850456 prefixEnd_850456 := by exact prefixLift 850456
  have htrace : WordTrace (prefixWord ++ tailWord_850456) baseStart_850456 baseEnd_850456 := by
    simpa [prefixWord, tailWord_850456, baseEnd_850456] using wordTrace_append hprefix tailTrace_850456
  have hstable : (prefixWord ++ tailWord_850456).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850456).length < 2 ^ (prefixWord ++ tailWord_850456).sum := by decide
  have hdescent : baseEnd_850456 < baseStart_850456 := by decide
  rcases family_descends (prefixWord ++ tailWord_850456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850467 : List Nat := [1, 1, 1, 4, 4, 1, 3, 6]
def baseStart_850467 : Nat := 118140960795 + 850467 * 2 ^ 59
def prefixEnd_850467 : Nat := 4983230072969 + 3 ^ 40 * 850467 * 2
def baseEnd_850467 : Nat := 64696052116656189281671

theorem tailTrace_850467 : CollatzResearch.WordTrace tailWord_850467 prefixEnd_850467 64696052116656189281671 := by
  unfold tailWord_850467
  simp only [CollatzResearch.WordTrace]
  refine ⟨31019079809910782044909655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20679386539940521363273103 31019079809910782044909655)
  ·
    refine ⟨46528619714866173067364483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31019079809910782044909655 46528619714866173067364483)
    ·
      refine ⟨69792929572299259601046725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46528619714866173067364483 69792929572299259601046725)
      ·
        refine ⟨13086174294806111175196261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69792929572299259601046725 13086174294806111175196261)
        ·
          refine ⟨2453657680276145845349299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13086174294806111175196261 2453657680276145845349299)
          ·
            refine ⟨3680486520414218768023949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2453657680276145845349299 3680486520414218768023949)
            ·
              refine ⟨1380182445155332038008981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3680486520414218768023949 1380182445155332038008981)
              ·
                refine ⟨64696052116656189281671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1380182445155332038008981 64696052116656189281671)
                ·
                  rfl

theorem cell21_850467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 6].length) (baseStart_850467 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_850467 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_850467 prefixEnd_850467 := by exact prefixLift 850467
  have htrace : WordTrace (prefixWord ++ tailWord_850467) baseStart_850467 baseEnd_850467 := by
    simpa [prefixWord, tailWord_850467, baseEnd_850467] using wordTrace_append hprefix tailTrace_850467
  have hstable : (prefixWord ++ tailWord_850467).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850467).length < 2 ^ (prefixWord ++ tailWord_850467).sum := by decide
  have hdescent : baseEnd_850467 < baseStart_850467 := by decide
  rcases family_descends (prefixWord ++ tailWord_850467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850481 : List Nat := [1, 2, 2, 3, 1, 1, 3, 1, 7]
def baseStart_850481 : Nat := 118140960795 + 850481 * 2 ^ 59
def prefixEnd_850481 : Nat := 4983230072969 + 3 ^ 40 * 850481 * 2
def baseEnd_850481 : Nat := 194091351340707654611651

theorem tailTrace_850481 : CollatzResearch.WordTrace tailWord_850481 prefixEnd_850481 194091351340707654611651 := by
  unfold tailWord_850481
  simp only [CollatzResearch.WordTrace]
  refine ⟨31019590431860062435919297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20679726954573374957279531 31019590431860062435919297)
  ·
    refine ⟨23264692823895046826939473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31019590431860062435919297 23264692823895046826939473)
    ·
      refine ⟨17448519617921285120204605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23264692823895046826939473 17448519617921285120204605)
      ·
        refine ⟨6543194856720481920076727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17448519617921285120204605 6543194856720481920076727)
        ·
          refine ⟨9814792285080722880115091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6543194856720481920076727 9814792285080722880115091)
          ·
            refine ⟨14722188427621084320172637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9814792285080722880115091 14722188427621084320172637)
            ·
              refine ⟨5520820660357906620064739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14722188427621084320172637 5520820660357906620064739)
              ·
                refine ⟨8281230990536859930097109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5520820660357906620064739 8281230990536859930097109)
                ·
                  refine ⟨194091351340707654611651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8281230990536859930097109 194091351340707654611651)
                  ·
                    rfl

theorem cell21_850481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 7].length) (baseStart_850481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_850481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_850481 prefixEnd_850481 := by exact prefixLift 850481
  have htrace : WordTrace (prefixWord ++ tailWord_850481) baseStart_850481 baseEnd_850481 := by
    simpa [prefixWord, tailWord_850481, baseEnd_850481] using wordTrace_append hprefix tailTrace_850481
  have hstable : (prefixWord ++ tailWord_850481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850481).length < 2 ^ (prefixWord ++ tailWord_850481).sum := by decide
  have hdescent : baseEnd_850481 < baseStart_850481 := by decide
  rcases family_descends (prefixWord ++ tailWord_850481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850512 : List Nat := [2, 1, 1, 1, 1, 3, 2, 6, 4]
def baseStart_850512 : Nat := 118140960795 + 850512 * 2 ^ 59
def prefixEnd_850512 : Nat := 4983230072969 + 3 ^ 40 * 850512 * 2
def baseEnd_850512 : Nat := 194098425963058489594921

theorem tailTrace_850512 : CollatzResearch.WordTrace tailWord_850512 prefixEnd_850512 194098425963058489594921 := by
  unfold tailWord_850512
  simp only [CollatzResearch.WordTrace]
  refine ⟨15510360547373877365148895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20680480729831836486865193 15510360547373877365148895)
  ·
    refine ⟨23265540821060816047723343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15510360547373877365148895 23265540821060816047723343)
    ·
      refine ⟨34898311231591224071585015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23265540821060816047723343 34898311231591224071585015)
      ·
        refine ⟨52347466847386836107377523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34898311231591224071585015 52347466847386836107377523)
        ·
          refine ⟨78521200271080254161066285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52347466847386836107377523 78521200271080254161066285)
          ·
            refine ⟨29445450101655095310399857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78521200271080254161066285 29445450101655095310399857)
            ·
              refine ⟨22084087576241321482799893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29445450101655095310399857 22084087576241321482799893)
              ·
                refine ⟨1035191605136311944506245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22084087576241321482799893 1035191605136311944506245)
                ·
                  refine ⟨194098425963058489594921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1035191605136311944506245 194098425963058489594921)
                  ·
                    rfl

theorem cell21_850512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 4].length) (baseStart_850512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_850512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_850512 prefixEnd_850512 := by exact prefixLift 850512
  have htrace : WordTrace (prefixWord ++ tailWord_850512) baseStart_850512 baseEnd_850512 := by
    simpa [prefixWord, tailWord_850512, baseEnd_850512] using wordTrace_append hprefix tailTrace_850512
  have hstable : (prefixWord ++ tailWord_850512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850512).length < 2 ^ (prefixWord ++ tailWord_850512).sum := by decide
  have hdescent : baseEnd_850512 < baseStart_850512 := by decide
  rcases family_descends (prefixWord ++ tailWord_850512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850543 : List Nat := [1, 1, 2, 1, 3, 2, 6, 5]
def baseStart_850543 : Nat := 118140960795 + 850543 * 2 ^ 59
def prefixEnd_850543 : Nat := 4983230072969 + 3 ^ 40 * 850543 * 2
def baseEnd_850543 : Nat := 64701833528469774859397

theorem tailTrace_850543 : CollatzResearch.WordTrace tailWord_850543 prefixEnd_850543 64701833528469774859397 := by
  unfold tailWord_850543
  simp only [CollatzResearch.WordTrace]
  refine ⟨31021851757635447024676283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20681234505090298016450855 31021851757635447024676283)
  ·
    refine ⟨46532777636453170537014425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31021851757635447024676283 46532777636453170537014425)
    ·
      refine ⟨34899583227339877902760819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46532777636453170537014425 34899583227339877902760819)
      ·
        refine ⟨52349374841009816854141229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34899583227339877902760819 52349374841009816854141229)
        ·
          refine ⟨19631015565378681320302961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52349374841009816854141229 19631015565378681320302961)
          ·
            refine ⟨14723261674034010990227221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19631015565378681320302961 14723261674034010990227221)
            ·
              refine ⟨690152890970344265166901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14723261674034010990227221 690152890970344265166901)
              ·
                refine ⟨64701833528469774859397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 690152890970344265166901 64701833528469774859397)
                ·
                  rfl

theorem cell21_850543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 5].length) (baseStart_850543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_850543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_850543 prefixEnd_850543 := by exact prefixLift 850543
  have htrace : WordTrace (prefixWord ++ tailWord_850543) baseStart_850543 baseEnd_850543 := by
    simpa [prefixWord, tailWord_850543, baseEnd_850543] using wordTrace_append hprefix tailTrace_850543
  have hstable : (prefixWord ++ tailWord_850543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850543).length < 2 ^ (prefixWord ++ tailWord_850543).sum := by decide
  have hdescent : baseEnd_850543 < baseStart_850543 := by decide
  rcases family_descends (prefixWord ++ tailWord_850543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850549 : List Nat := [1, 3, 4, 2, 2, 2, 1, 3, 3]
def baseStart_850549 : Nat := 118140960795 + 850549 * 2 ^ 59
def prefixEnd_850549 : Nat := 4983230072969 + 3 ^ 40 * 850549 * 2
def baseEnd_850549 : Nat := 194106869867154647478179

theorem tailTrace_850549 : CollatzResearch.WordTrace tailWord_850549 prefixEnd_850549 194106869867154647478179 := by
  unfold tailWord_850549
  simp only [CollatzResearch.WordTrace]
  refine ⟨31022070595613710049394701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20681380397075806699596467 31022070595613710049394701)
  ·
    refine ⟨11633276473355141268523013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31022070595613710049394701 11633276473355141268523013)
    ·
      refine ⟨2181239338754088987848065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11633276473355141268523013 2181239338754088987848065)
      ·
        refine ⟨1635929504065566740886049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2181239338754088987848065 1635929504065566740886049)
        ·
          refine ⟨1226947128049175055664537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1635929504065566740886049 1226947128049175055664537)
          ·
            refine ⟨920210346036881291748403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1226947128049175055664537 920210346036881291748403)
            ·
              refine ⟨1380315519055321937622605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 920210346036881291748403 1380315519055321937622605)
              ·
                refine ⟨517618319645745726608477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1380315519055321937622605 517618319645745726608477)
                ·
                  refine ⟨194106869867154647478179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 517618319645745726608477 194106869867154647478179)
                  ·
                    rfl

theorem cell21_850549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 3, 3].length) (baseStart_850549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_850549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_850549 prefixEnd_850549 := by exact prefixLift 850549
  have htrace : WordTrace (prefixWord ++ tailWord_850549) baseStart_850549 baseEnd_850549 := by
    simpa [prefixWord, tailWord_850549, baseEnd_850549] using wordTrace_append hprefix tailTrace_850549
  have hstable : (prefixWord ++ tailWord_850549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850549).length < 2 ^ (prefixWord ++ tailWord_850549).sum := by decide
  have hdescent : baseEnd_850549 < baseStart_850549 := by decide
  rcases family_descends (prefixWord ++ tailWord_850549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850625 : List Nat := [1, 2, 6, 2, 1, 1, 1, 4, 3]
def baseStart_850625 : Nat := 118140960795 + 850625 * 2 ^ 59
def prefixEnd_850625 : Nat := 4983230072969 + 3 ^ 40 * 850625 * 2
def baseEnd_850625 : Nat := 194124214102595404211357

theorem tailTrace_850625 : CollatzResearch.WordTrace tailWord_850625 prefixEnd_850625 194124214102595404211357 := by
  unfold tailWord_850625
  simp only [CollatzResearch.WordTrace]
  refine ⟨31024842543338375029161329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20683228362225583352774219 31024842543338375029161329)
  ·
    refine ⟨23268631907503781271870997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31024842543338375029161329 23268631907503781271870997)
    ·
      refine ⟨1090717120664239747118953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23268631907503781271870997 1090717120664239747118953)
      ·
        refine ⟨818037840498179810339215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1090717120664239747118953 818037840498179810339215)
        ·
          refine ⟨1227056760747269715508823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 818037840498179810339215 1227056760747269715508823)
          ·
            refine ⟨1840585141120904573263235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1227056760747269715508823 1840585141120904573263235)
            ·
              refine ⟨2760877711681356859894853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1840585141120904573263235 2760877711681356859894853)
              ·
                refine ⟨517664570940254411230285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2760877711681356859894853 517664570940254411230285)
                ·
                  refine ⟨194124214102595404211357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 517664570940254411230285 194124214102595404211357)
                  ·
                    rfl

theorem cell21_850625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 4, 3].length) (baseStart_850625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_850625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_850625 prefixEnd_850625 := by exact prefixLift 850625
  have htrace : WordTrace (prefixWord ++ tailWord_850625) baseStart_850625 baseEnd_850625 := by
    simpa [prefixWord, tailWord_850625, baseEnd_850625] using wordTrace_append hprefix tailTrace_850625
  have hstable : (prefixWord ++ tailWord_850625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850625).length < 2 ^ (prefixWord ++ tailWord_850625).sum := by decide
  have hdescent : baseEnd_850625 < baseStart_850625 := by decide
  rcases family_descends (prefixWord ++ tailWord_850625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850636 : List Nat := [2, 2, 1, 5, 1, 3, 1, 6]
def baseStart_850636 : Nat := 118140960795 + 850636 * 2 ^ 59
def prefixEnd_850636 : Nat := 4983230072969 + 3 ^ 40 * 850636 * 2
def baseEnd_850636 : Nat := 64708908150820609842667

theorem tailTrace_850636 : CollatzResearch.WordTrace tailWord_850636 prefixEnd_850636 64708908150820609842667 := by
  unfold tailWord_850636
  simp only [CollatzResearch.WordTrace]
  refine ⟨15512621873149261953905881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20683495830865682605207841 15512621873149261953905881)
  ·
    refine ⟨11634466404861946465429411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15512621873149261953905881 11634466404861946465429411)
    ·
      refine ⟨17451699607292919698144117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11634466404861946465429411 17451699607292919698144117)
      ·
        refine ⟨1636096838183711221701011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17451699607292919698144117 1636096838183711221701011)
        ·
          refine ⟨2454145257275566832551517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1636096838183711221701011 2454145257275566832551517)
          ·
            refine ⟨920304471478337562206819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2454145257275566832551517 920304471478337562206819)
            ·
              refine ⟨1380456707217506343310229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 920304471478337562206819 1380456707217506343310229)
              ·
                refine ⟨64708908150820609842667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1380456707217506343310229 64708908150820609842667)
                ·
                  rfl

theorem cell21_850636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 6].length) (baseStart_850636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_850636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_850636 prefixEnd_850636 := by exact prefixLift 850636
  have htrace : WordTrace (prefixWord ++ tailWord_850636) baseStart_850636 baseEnd_850636 := by
    simpa [prefixWord, tailWord_850636, baseEnd_850636] using wordTrace_append hprefix tailTrace_850636
  have hstable : (prefixWord ++ tailWord_850636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850636).length < 2 ^ (prefixWord ++ tailWord_850636).sum := by decide
  have hdescent : baseEnd_850636 < baseStart_850636 := by decide
  rcases family_descends (prefixWord ++ tailWord_850636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850709 : List Nat := [1, 3, 2, 1, 2, 2, 1, 4, 5]
def baseStart_850709 : Nat := 118140960795 + 850709 * 2 ^ 59
def prefixEnd_850709 : Nat := 4983230072969 + 3 ^ 40 * 850709 * 2
def baseEnd_850709 : Nat := 194143384047029924811185

theorem tailTrace_850709 : CollatzResearch.WordTrace tailWord_850709 prefixEnd_850709 194143384047029924811185 := by
  unfold tailWord_850709
  simp only [CollatzResearch.WordTrace]
  refine ⟨31027906275034057375219181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20685270850022704916812787 31027906275034057375219181)
  ·
    refine ⟨11635464853137771515707193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31027906275034057375219181 11635464853137771515707193)
    ·
      refine ⟨8726598639853328636780395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11635464853137771515707193 8726598639853328636780395)
      ·
        refine ⟨13089897959779992955170593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8726598639853328636780395 13089897959779992955170593)
        ·
          refine ⟨9817423469834994716377945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13089897959779992955170593 9817423469834994716377945)
          ·
            refine ⟨7363067602376246037283459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9817423469834994716377945 7363067602376246037283459)
            ·
              refine ⟨11044601403564369055925189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7363067602376246037283459 11044601403564369055925189)
              ·
                refine ⟨2070862763168319197985973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11044601403564369055925189 2070862763168319197985973)
                ·
                  refine ⟨194143384047029924811185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2070862763168319197985973 194143384047029924811185)
                  ·
                    rfl

theorem cell21_850709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_850709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_850709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_850709 prefixEnd_850709 := by exact prefixLift 850709
  have htrace : WordTrace (prefixWord ++ tailWord_850709) baseStart_850709 baseEnd_850709 := by
    simpa [prefixWord, tailWord_850709, baseEnd_850709] using wordTrace_append hprefix tailTrace_850709
  have hstable : (prefixWord ++ tailWord_850709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850709).length < 2 ^ (prefixWord ++ tailWord_850709).sum := by decide
  have hdescent : baseEnd_850709 < baseStart_850709 := by decide
  rcases family_descends (prefixWord ++ tailWord_850709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850743 : List Nat := [1, 1, 3, 1, 2, 1, 7, 2, 3]
def baseStart_850743 : Nat := 118140960795 + 850743 * 2 ^ 59
def prefixEnd_850743 : Nat := 4983230072969 + 3 ^ 40 * 850743 * 2
def baseEnd_850743 : Nat := 194151143310253421244449

theorem tailTrace_850743 : CollatzResearch.WordTrace tailWord_850743 prefixEnd_850743 194151143310253421244449 := by
  unfold tailWord_850743
  simp only [CollatzResearch.WordTrace]
  refine ⟨31029146356910881181956883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20686097571273920787971255 31029146356910881181956883)
  ·
    refine ⟨46543719535366321772935325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31029146356910881181956883 46543719535366321772935325)
    ·
      refine ⟨17453894825762370664850747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46543719535366321772935325 17453894825762370664850747)
      ·
        refine ⟨26180842238643555997276121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17453894825762370664850747 26180842238643555997276121)
        ·
          refine ⟨19635631678982666997957091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26180842238643555997276121 19635631678982666997957091)
          ·
            refine ⟨29453447518474000496935637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19635631678982666997957091 29453447518474000496935637)
            ·
              refine ⟨690315176214234386646929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 29453447518474000496935637 690315176214234386646929)
              ·
                refine ⟨517736382160675789985197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 690315176214234386646929 517736382160675789985197)
                ·
                  refine ⟨194151143310253421244449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 517736382160675789985197 194151143310253421244449)
                  ·
                    rfl

theorem cell21_850743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 2, 3].length) (baseStart_850743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_850743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_850743 prefixEnd_850743 := by exact prefixLift 850743
  have htrace : WordTrace (prefixWord ++ tailWord_850743) baseStart_850743 baseEnd_850743 := by
    simpa [prefixWord, tailWord_850743, baseEnd_850743] using wordTrace_append hprefix tailTrace_850743
  have hstable : (prefixWord ++ tailWord_850743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850743).length < 2 ^ (prefixWord ++ tailWord_850743).sum := by decide
  have hdescent : baseEnd_850743 < baseStart_850743 := by decide
  rcases family_descends (prefixWord ++ tailWord_850743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850799 : List Nat := [1, 1, 2, 1, 3, 1, 1, 5, 6]
def baseStart_850799 : Nat := 118140960795 + 850799 * 2 ^ 59
def prefixEnd_850799 : Nat := 4983230072969 + 3 ^ 40 * 850799 * 2
def baseEnd_850799 : Nat := 194163923273209768311001

theorem tailTrace_850799 : CollatzResearch.WordTrace tailWord_850799 prefixEnd_850799 194163923273209768311001 := by
  unfold tailWord_850799
  simp only [CollatzResearch.WordTrace]
  refine ⟨31031188844708002745995451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20687459229805335163996967 31031188844708002745995451)
  ·
    refine ⟨46546783267062004118993177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31031188844708002745995451 46546783267062004118993177)
    ·
      refine ⟨34910087450296503089244883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46546783267062004118993177 34910087450296503089244883)
      ·
        refine ⟨52365131175444754633867325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34910087450296503089244883 52365131175444754633867325)
        ·
          refine ⟨19636924190791782987700247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52365131175444754633867325 19636924190791782987700247)
          ·
            refine ⟨29455386286187674481550371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19636924190791782987700247 29455386286187674481550371)
            ·
              refine ⟨44183079429281511722325557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29455386286187674481550371 44183079429281511722325557)
              ·
                refine ⟨4142163696495141723968021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44183079429281511722325557 4142163696495141723968021)
                ·
                  refine ⟨194163923273209768311001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4142163696495141723968021 194163923273209768311001)
                  ·
                    rfl

theorem cell21_850799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 6].length) (baseStart_850799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_850799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_850799 prefixEnd_850799 := by exact prefixLift 850799
  have htrace : WordTrace (prefixWord ++ tailWord_850799) baseStart_850799 baseEnd_850799 := by
    simpa [prefixWord, tailWord_850799, baseEnd_850799] using wordTrace_append hprefix tailTrace_850799
  have hstable : (prefixWord ++ tailWord_850799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850799).length < 2 ^ (prefixWord ++ tailWord_850799).sum := by decide
  have hdescent : baseEnd_850799 < baseStart_850799 := by decide
  rcases family_descends (prefixWord ++ tailWord_850799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850850 : List Nat := [3, 3, 1, 2, 2, 3, 1, 2, 4]
def baseStart_850850 : Nat := 118140960795 + 850850 * 2 ^ 59
def prefixEnd_850850 : Nat := 4983230072969 + 3 ^ 40 * 850850 * 2
def baseEnd_850850 : Nat := 194175562168045012960897

theorem tailTrace_850850 : CollatzResearch.WordTrace tailWord_850850 prefixEnd_850850 194175562168045012960897 := by
  unfold tailWord_850850
  simp only [CollatzResearch.WordTrace]
  refine ⟨7758262241880809614025501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20688699311682158970734669 7758262241880809614025501)
  ·
    refine ⟨2909348340705303605259563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7758262241880809614025501 2909348340705303605259563)
    ·
      refine ⟨4364022511057955407889345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2909348340705303605259563 4364022511057955407889345)
      ·
        refine ⟨3273016883293466555917009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4364022511057955407889345 3273016883293466555917009)
        ·
          refine ⟨2454762662470099916937757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3273016883293466555917009 2454762662470099916937757)
          ·
            refine ⟨920535998426287468851659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2454762662470099916937757 920535998426287468851659)
            ·
              refine ⟨1380803997639431203277489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 920535998426287468851659 1380803997639431203277489)
              ·
                refine ⟨1035602998229573402458117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1380803997639431203277489 1035602998229573402458117)
                ·
                  refine ⟨194175562168045012960897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1035602998229573402458117 194175562168045012960897)
                  ·
                    rfl

theorem cell21_850850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_850850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_850850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_850850 prefixEnd_850850 := by exact prefixLift 850850
  have htrace : WordTrace (prefixWord ++ tailWord_850850) baseStart_850850 baseEnd_850850 := by
    simpa [prefixWord, tailWord_850850, baseEnd_850850] using wordTrace_append hprefix tailTrace_850850
  have hstable : (prefixWord ++ tailWord_850850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850850).length < 2 ^ (prefixWord ++ tailWord_850850).sum := by decide
  have hdescent : baseEnd_850850 < baseStart_850850 := by decide
  rcases family_descends (prefixWord ++ tailWord_850850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850895 : List Nat := [1, 1, 2, 1, 1, 8, 1, 3, 3]
def baseStart_850895 : Nat := 118140960795 + 850895 * 2 ^ 59
def prefixEnd_850895 : Nat := 4983230072969 + 3 ^ 40 * 850895 * 2
def baseEnd_850895 : Nat := 194185831781134934710805

theorem tailTrace_850895 : CollatzResearch.WordTrace tailWord_850895 prefixEnd_850895 194185831781134934710805 := by
  unfold tailWord_850895
  simp only [CollatzResearch.WordTrace]
  refine ⟨31034690252360211141490139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20689793501573474094326759 31034690252360211141490139)
  ·
    refine ⟨46552035378540316712235209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31034690252360211141490139 46552035378540316712235209)
    ·
      refine ⟨34914026533905237534176407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46552035378540316712235209 34914026533905237534176407)
      ·
        refine ⟨52371039800857856301264611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34914026533905237534176407 52371039800857856301264611)
        ·
          refine ⟨78556559701286784451896917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52371039800857856301264611 78556559701286784451896917)
          ·
            refine ⟨920584683999454505295667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 78556559701286784451896917 920584683999454505295667)
            ·
              refine ⟨1380877025999181757943501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 920584683999454505295667 1380877025999181757943501)
              ·
                refine ⟨517828884749693159228813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1380877025999181757943501 517828884749693159228813)
                ·
                  refine ⟨194185831781134934710805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 517828884749693159228813 194185831781134934710805)
                  ·
                    rfl

theorem cell21_850895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 3, 3].length) (baseStart_850895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_850895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_850895 prefixEnd_850895 := by exact prefixLift 850895
  have htrace : WordTrace (prefixWord ++ tailWord_850895) baseStart_850895 baseEnd_850895 := by
    simpa [prefixWord, tailWord_850895, baseEnd_850895] using wordTrace_append hprefix tailTrace_850895
  have hstable : (prefixWord ++ tailWord_850895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850895).length < 2 ^ (prefixWord ++ tailWord_850895).sum := by decide
  have hdescent : baseEnd_850895 < baseStart_850895 := by decide
  rcases family_descends (prefixWord ++ tailWord_850895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850906 : List Nat := [3, 1, 1, 2, 4, 1, 9]
def baseStart_850906 : Nat := 118140960795 + 850906 * 2 ^ 59
def prefixEnd_850906 : Nat := 4983230072969 + 3 ^ 40 * 850906 * 2
def baseEnd_850906 : Nat := 21576482459000151114161

theorem tailTrace_850906 : CollatzResearch.WordTrace tailWord_850906 prefixEnd_850906 21576482459000151114161 := by
  unfold tailWord_850906
  simp only [CollatzResearch.WordTrace]
  refine ⟨7758772863830090005035143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20690060970213573346760381 7758772863830090005035143)
  ·
    refine ⟨11638159295745135007552715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7758772863830090005035143 11638159295745135007552715)
    ·
      refine ⟨17457238943617702511329073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11638159295745135007552715 17457238943617702511329073)
      ·
        refine ⟨13092929207713276883496805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17457238943617702511329073 13092929207713276883496805)
        ·
          refine ⟨2454924226446239415655651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13092929207713276883496805 2454924226446239415655651)
          ·
            refine ⟨3682386339669359123483477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2454924226446239415655651 3682386339669359123483477)
            ·
              refine ⟨21576482459000151114161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3682386339669359123483477 21576482459000151114161)
              ·
                rfl

theorem cell21_850906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 9].length) (baseStart_850906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_850906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_850906 prefixEnd_850906 := by exact prefixLift 850906
  have htrace : WordTrace (prefixWord ++ tailWord_850906) baseStart_850906 baseEnd_850906 := by
    simpa [prefixWord, tailWord_850906, baseEnd_850906] using wordTrace_append hprefix tailTrace_850906
  have hstable : (prefixWord ++ tailWord_850906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850906).length < 2 ^ (prefixWord ++ tailWord_850906).sum := by decide
  have hdescent : baseEnd_850906 < baseStart_850906 := by decide
  rcases family_descends (prefixWord ++ tailWord_850906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850968 : List Nat := [2, 1, 2, 3, 2, 2, 1, 4, 4]
def baseStart_850968 : Nat := 118140960795 + 850968 * 2 ^ 59
def prefixEnd_850968 : Nat := 4983230072969 + 3 ^ 40 * 850968 * 2
def baseEnd_850968 : Nat := 194202491375703029993989

theorem tailTrace_850968 : CollatzResearch.WordTrace tailWord_850968 prefixEnd_850968 194202491375703029993989 := by
  unfold tailWord_850968
  simp only [CollatzResearch.WordTrace]
  refine ⟨15518676390547872304448779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20691568520730496405931705 15518676390547872304448779)
  ·
    refine ⟨23278014585821808456673169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15518676390547872304448779 23278014585821808456673169)
    ·
      refine ⟨17458510939366356342504877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23278014585821808456673169 17458510939366356342504877)
      ·
        refine ⟨6546941602262383628439329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17458510939366356342504877 6546941602262383628439329)
        ·
          refine ⟨4910206201696787721329497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6546941602262383628439329 4910206201696787721329497)
          ·
            refine ⟨3682654651272590790997123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4910206201696787721329497 3682654651272590790997123)
            ·
              refine ⟨5523981976908886186495685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3682654651272590790997123 5523981976908886186495685)
              ·
                refine ⟨1035746620670416159967941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5523981976908886186495685 1035746620670416159967941)
                ·
                  refine ⟨194202491375703029993989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1035746620670416159967941 194202491375703029993989)
                  ·
                    rfl

theorem cell21_850968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 4].length) (baseStart_850968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_850968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_850968 prefixEnd_850968 := by exact prefixLift 850968
  have htrace : WordTrace (prefixWord ++ tailWord_850968) baseStart_850968 baseEnd_850968 := by
    simpa [prefixWord, tailWord_850968, baseEnd_850968] using wordTrace_append hprefix tailTrace_850968
  have hstable : (prefixWord ++ tailWord_850968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850968).length < 2 ^ (prefixWord ++ tailWord_850968).sum := by decide
  have hdescent : baseEnd_850968 < baseStart_850968 := by decide
  rcases family_descends (prefixWord ++ tailWord_850968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851058 : List Nat := [3, 2, 1, 2, 2, 1, 3, 7]
def baseStart_851058 : Nat := 118140960795 + 851058 * 2 ^ 59
def prefixEnd_851058 : Nat := 4983230072969 + 3 ^ 40 * 851058 * 2
def baseEnd_851058 : Nat := 64741010200627624497935

theorem tailTrace_851058 : CollatzResearch.WordTrace tailWord_851058 prefixEnd_851058 64741010200627624497935 := by
  unfold tailWord_851058
  simp only [CollatzResearch.WordTrace]
  refine ⟨7760158837692422494918457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20693756900513126653115885 7760158837692422494918457)
  ·
    refine ⟨5820119128269316871188843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7760158837692422494918457 5820119128269316871188843)
    ·
      refine ⟨8730178692403975306783265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5820119128269316871188843 8730178692403975306783265)
      ·
        refine ⟨6547634019302981480087449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8730178692403975306783265 6547634019302981480087449)
        ·
          refine ⟨4910725514477236110065587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6547634019302981480087449 4910725514477236110065587)
          ·
            refine ⟨7366088271715854165098381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4910725514477236110065587 7366088271715854165098381)
            ·
              refine ⟨2762283101893445311911893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7366088271715854165098381 2762283101893445311911893)
              ·
                refine ⟨64741010200627624497935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2762283101893445311911893 64741010200627624497935)
                ·
                  rfl

theorem cell21_851058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 7].length) (baseStart_851058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_851058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_851058 prefixEnd_851058 := by exact prefixLift 851058
  have htrace : WordTrace (prefixWord ++ tailWord_851058) baseStart_851058 baseEnd_851058 := by
    simpa [prefixWord, tailWord_851058, baseEnd_851058] using wordTrace_append hprefix tailTrace_851058
  have hstable : (prefixWord ++ tailWord_851058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851058).length < 2 ^ (prefixWord ++ tailWord_851058).sum := by decide
  have hdescent : baseEnd_851058 < baseStart_851058 := by decide
  rcases family_descends (prefixWord ++ tailWord_851058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851072 : List Nat := [2, 1, 1, 2, 1, 3, 2, 2, 7]
def baseStart_851072 : Nat := 118140960795 + 851072 * 2 ^ 59
def prefixEnd_851072 : Nat := 4983230072969 + 3 ^ 40 * 851072 * 2
def baseEnd_851072 : Nat := 194226225592621960260443

theorem tailTrace_851072 : CollatzResearch.WordTrace tailWord_851072 prefixEnd_851072 194226225592621960260443 := by
  unfold tailWord_851072
  simp only [CollatzResearch.WordTrace]
  refine ⟨15520572986359485185341735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20694097315145980247122313 15520572986359485185341735)
  ·
    refine ⟨23280859479539227778012603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15520572986359485185341735 23280859479539227778012603)
    ·
      refine ⟨34921289219308841667018905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23280859479539227778012603 34921289219308841667018905)
      ·
        refine ⟨26190966914481631250264179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34921289219308841667018905 26190966914481631250264179)
        ·
          refine ⟨39286450371722446875396269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26190966914481631250264179 39286450371722446875396269)
          ·
            refine ⟨14732418889395917578273601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39286450371722446875396269 14732418889395917578273601)
            ·
              refine ⟨11049314167046938183705201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14732418889395917578273601 11049314167046938183705201)
              ·
                refine ⟨8286985625285203637778901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11049314167046938183705201 8286985625285203637778901)
                ·
                  refine ⟨194226225592621960260443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8286985625285203637778901 194226225592621960260443)
                  ·
                    rfl

theorem cell21_851072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 7].length) (baseStart_851072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_851072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_851072 prefixEnd_851072 := by exact prefixLift 851072
  have htrace : WordTrace (prefixWord ++ tailWord_851072) baseStart_851072 baseEnd_851072 := by
    simpa [prefixWord, tailWord_851072, baseEnd_851072] using wordTrace_append hprefix tailTrace_851072
  have hstable : (prefixWord ++ tailWord_851072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851072).length < 2 ^ (prefixWord ++ tailWord_851072).sum := by decide
  have hdescent : baseEnd_851072 < baseStart_851072 := by decide
  rcases family_descends (prefixWord ++ tailWord_851072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851134 : List Nat := [4, 2, 1, 1, 3, 10]
def baseStart_851134 : Nat := 118140960795 + 851134 * 2 ^ 59
def prefixEnd_851134 : Nat := 4983230072969 + 3 ^ 40 * 851134 * 2
def baseEnd_851134 : Nat := 7194087956937912230629

theorem tailTrace_851134 : CollatzResearch.WordTrace tailWord_851134 prefixEnd_851134 7194087956937912230629 := by
  unfold tailWord_851134
  simp only [CollatzResearch.WordTrace]
  refine ⟨3880425912311794369930057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20695604865662903306293637 3880425912311794369930057)
  ·
    refine ⟨2910319434233845777447543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3880425912311794369930057 2910319434233845777447543)
    ·
      refine ⟨4365479151350768666171315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2910319434233845777447543 4365479151350768666171315)
      ·
        refine ⟨6548218727026152999256973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4365479151350768666171315 6548218727026152999256973)
        ·
          refine ⟨2455582022634807374721365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6548218727026152999256973 2455582022634807374721365)
          ·
            refine ⟨7194087956937912230629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2455582022634807374721365 7194087956937912230629)
            ·
              rfl

theorem cell21_851134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 10].length) (baseStart_851134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_851134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_851134 prefixEnd_851134 := by exact prefixLift 851134
  have htrace : WordTrace (prefixWord ++ tailWord_851134) baseStart_851134 baseEnd_851134 := by
    simpa [prefixWord, tailWord_851134, baseEnd_851134] using wordTrace_append hprefix tailTrace_851134
  have hstable : (prefixWord ++ tailWord_851134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851134).length < 2 ^ (prefixWord ++ tailWord_851134).sum := by decide
  have hdescent : baseEnd_851134 < baseStart_851134 := by decide
  rcases family_descends (prefixWord ++ tailWord_851134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851137 : List Nat := [1, 2, 6, 1, 1, 1, 1, 4, 4]
def baseStart_851137 : Nat := 118140960795 + 851137 * 2 ^ 59
def prefixEnd_851137 : Nat := 4983230072969 + 3 ^ 40 * 851137 * 2
def baseEnd_851137 : Nat := 194241059478196291676977

theorem tailTrace_851137 : CollatzResearch.WordTrace tailWord_851137 prefixEnd_851137 194241059478196291676977 := by
  unfold tailWord_851137
  simp only [CollatzResearch.WordTrace]
  refine ⟨31043516717483486471799665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20695677811655657647866443 31043516717483486471799665)
  ·
    refine ⟨23282637538112614853849749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31043516717483486471799665 23282637538112614853849749)
    ·
      refine ⟨1091373634599028821274207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23282637538112614853849749 1091373634599028821274207)
      ·
        refine ⟨1637060451898543231911311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1091373634599028821274207 1637060451898543231911311)
        ·
          refine ⟨2455590677847814847866967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1637060451898543231911311 2455590677847814847866967)
          ·
            refine ⟨3683386016771722271800451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2455590677847814847866967 3683386016771722271800451)
            ·
              refine ⟨5525079025157583407700677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3683386016771722271800451 5525079025157583407700677)
              ·
                refine ⟨1035952317217046888943877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5525079025157583407700677 1035952317217046888943877)
                ·
                  refine ⟨194241059478196291676977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1035952317217046888943877 194241059478196291676977)
                  ·
                    rfl

theorem cell21_851137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 4].length) (baseStart_851137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_851137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_851137 prefixEnd_851137 := by exact prefixLift 851137
  have htrace : WordTrace (prefixWord ++ tailWord_851137) baseStart_851137 baseEnd_851137 := by
    simpa [prefixWord, tailWord_851137, baseEnd_851137] using wordTrace_append hprefix tailTrace_851137
  have hstable : (prefixWord ++ tailWord_851137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851137).length < 2 ^ (prefixWord ++ tailWord_851137).sum := by decide
  have hdescent : baseEnd_851137 < baseStart_851137 := by decide
  rcases family_descends (prefixWord ++ tailWord_851137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851182 : List Nat := [4, 1, 2, 1, 1, 1, 3, 5, 3]
def baseStart_851182 : Nat := 118140960795 + 851182 * 2 ^ 59
def prefixEnd_851182 : Nat := 4983230072969 + 3 ^ 40 * 851182 * 2
def baseEnd_851182 : Nat := 194251329091286213426885

theorem tailTrace_851182 : CollatzResearch.WordTrace tailWord_851182 prefixEnd_851182 194251329091286213426885 := by
  unfold tailWord_851182
  simp only [CollatzResearch.WordTrace]
  refine ⟨3880644750290057394648475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20696772001546972771458533 3880644750290057394648475)
  ·
    refine ⟨5820967125435086091972713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3880644750290057394648475 5820967125435086091972713)
    ·
      refine ⟨4365725344076314568979535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5820967125435086091972713 4365725344076314568979535)
      ·
        refine ⟨6548588016114471853469303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4365725344076314568979535 6548588016114471853469303)
        ·
          refine ⟨9822882024171707780203955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6548588016114471853469303 9822882024171707780203955)
          ·
            refine ⟨14734323036257561670305933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9822882024171707780203955 14734323036257561670305933)
            ·
              refine ⟨5525371138596585626364725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14734323036257561670305933 5525371138596585626364725)
              ·
                refine ⟨518003544243429902471693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5525371138596585626364725 518003544243429902471693)
                ·
                  refine ⟨194251329091286213426885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 518003544243429902471693 194251329091286213426885)
                  ·
                    rfl

theorem cell21_851182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_851182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_851182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_851182 prefixEnd_851182 := by exact prefixLift 851182
  have htrace : WordTrace (prefixWord ++ tailWord_851182) baseStart_851182 baseEnd_851182 := by
    simpa [prefixWord, tailWord_851182, baseEnd_851182] using wordTrace_append hprefix tailTrace_851182
  have hstable : (prefixWord ++ tailWord_851182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851182).length < 2 ^ (prefixWord ++ tailWord_851182).sum := by decide
  have hdescent : baseEnd_851182 < baseStart_851182 := by decide
  rcases family_descends (prefixWord ++ tailWord_851182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851188 : List Nat := [2, 6, 1, 2, 1, 2, 1, 2, 4]
def baseStart_851188 : Nat := 118140960795 + 851188 * 2 ^ 59
def prefixEnd_851188 : Nat := 4983230072969 + 3 ^ 40 * 851188 * 2
def baseEnd_851188 : Nat := 194252698373031536326873

theorem tailTrace_851188 : CollatzResearch.WordTrace tailWord_851188 prefixEnd_851188 194252698373031536326873 := by
  unfold tailWord_851188
  simp only [CollatzResearch.WordTrace]
  refine ⟨15522688420149361090953109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20696917893532481454604145 15522688420149361090953109)
  ·
    refine ⟨727626019694501301138427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15522688420149361090953109 727626019694501301138427)
    ·
      refine ⟨1091439029541751951707641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 727626019694501301138427 1091439029541751951707641)
      ·
        refine ⟨818579272156313963780731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1091439029541751951707641 818579272156313963780731)
        ·
          refine ⟨1227868908234470945671097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 818579272156313963780731 1227868908234470945671097)
          ·
            refine ⟨920901681175853209253323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1227868908234470945671097 920901681175853209253323)
            ·
              refine ⟨1381352521763779813879985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 920901681175853209253323 1381352521763779813879985)
              ·
                refine ⟨1036014391322834860409989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1381352521763779813879985 1036014391322834860409989)
                ·
                  refine ⟨194252698373031536326873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1036014391322834860409989 194252698373031536326873)
                  ·
                    rfl

theorem cell21_851188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_851188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_851188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_851188 prefixEnd_851188 := by exact prefixLift 851188
  have htrace : WordTrace (prefixWord ++ tailWord_851188) baseStart_851188 baseEnd_851188 := by
    simpa [prefixWord, tailWord_851188, baseEnd_851188] using wordTrace_append hprefix tailTrace_851188
  have hstable : (prefixWord ++ tailWord_851188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851188).length < 2 ^ (prefixWord ++ tailWord_851188).sum := by decide
  have hdescent : baseEnd_851188 < baseStart_851188 := by decide
  rcases family_descends (prefixWord ++ tailWord_851188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851193 : List Nat := [1, 2, 1, 3, 1, 1, 12]
def baseStart_851193 : Nat := 118140960795 + 851193 * 2 ^ 59
def prefixEnd_851193 : Nat := 4983230072969 + 3 ^ 40 * 851193 * 2
def baseEnd_851193 : Nat := 21583759937905848749281

theorem tailTrace_851193 : CollatzResearch.WordTrace tailWord_851193 prefixEnd_851193 21583759937905848749281 := by
  unfold tailWord_851193
  simp only [CollatzResearch.WordTrace]
  refine ⟨31045559205280608035838233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20697039470187072023892155 31045559205280608035838233)
  ·
    refine ⟨23284169403960456026878675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31045559205280608035838233 23284169403960456026878675)
    ·
      refine ⟨34926254105940684040318013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23284169403960456026878675 34926254105940684040318013)
      ·
        refine ⟨13097345289727756515119255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34926254105940684040318013 13097345289727756515119255)
        ·
          refine ⟨19646017934591634772678883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13097345289727756515119255 19646017934591634772678883)
          ·
            refine ⟨29469026901887452159018325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19646017934591634772678883 29469026901887452159018325)
            ·
              refine ⟨21583759937905848749281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 29469026901887452159018325 21583759937905848749281)
              ·
                rfl

theorem cell21_851193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 12].length) (baseStart_851193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_851193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_851193 prefixEnd_851193 := by exact prefixLift 851193
  have htrace : WordTrace (prefixWord ++ tailWord_851193) baseStart_851193 baseEnd_851193 := by
    simpa [prefixWord, tailWord_851193, baseEnd_851193] using wordTrace_append hprefix tailTrace_851193
  have hstable : (prefixWord ++ tailWord_851193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851193).length < 2 ^ (prefixWord ++ tailWord_851193).sum := by decide
  have hdescent : baseEnd_851193 < baseStart_851193 := by decide
  rcases family_descends (prefixWord ++ tailWord_851193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851196 : List Nat := [2, 2, 2, 1, 5, 1, 1, 1, 6]
def baseStart_851196 : Nat := 118140960795 + 851196 * 2 ^ 59
def prefixEnd_851196 : Nat := 4983230072969 + 3 ^ 40 * 851196 * 2
def baseEnd_851196 : Nat := 194254524082025300193523

theorem tailTrace_851196 : CollatzResearch.WordTrace tailWord_851196 prefixEnd_851196 194254524082025300193523 := by
  unfold tailWord_851196
  simp only [CollatzResearch.WordTrace]
  refine ⟨15522834312134869774098721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20697112416179826365464961 15522834312134869774098721)
  ·
    refine ⟨11642125734101152330574041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15522834312134869774098721 11642125734101152330574041)
    ·
      refine ⟨8731594300575864247930531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11642125734101152330574041 8731594300575864247930531)
      ·
        refine ⟨13097391450863796371895797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8731594300575864247930531 13097391450863796371895797)
        ·
          refine ⟨1227880448518480909865231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13097391450863796371895797 1227880448518480909865231)
          ·
            refine ⟨1841820672777721364797847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1227880448518480909865231 1841820672777721364797847)
            ·
              refine ⟨2762731009166582047196771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1841820672777721364797847 2762731009166582047196771)
              ·
                refine ⟨4144096513749873070795157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2762731009166582047196771 4144096513749873070795157)
                ·
                  refine ⟨194254524082025300193523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4144096513749873070795157 194254524082025300193523)
                  ·
                    rfl

theorem cell21_851196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_851196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_851196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_851196 prefixEnd_851196 := by exact prefixLift 851196
  have htrace : WordTrace (prefixWord ++ tailWord_851196) baseStart_851196 baseEnd_851196 := by
    simpa [prefixWord, tailWord_851196, baseEnd_851196] using wordTrace_append hprefix tailTrace_851196
  have hstable : (prefixWord ++ tailWord_851196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851196).length < 2 ^ (prefixWord ++ tailWord_851196).sum := by decide
  have hdescent : baseEnd_851196 < baseStart_851196 := by decide
  rcases family_descends (prefixWord ++ tailWord_851196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851362 : List Nat := [3, 3, 1, 2, 1, 3, 8]
def baseStart_851362 : Nat := 118140960795 + 851362 * 2 ^ 59
def prefixEnd_851362 : Nat := 4983230072969 + 3 ^ 40 * 851362 * 2
def baseEnd_851362 : Nat := 21588045282627322269613

theorem tailTrace_851362 : CollatzResearch.WordTrace tailWord_851362 prefixEnd_851362 21588045282627322269613 := by
  unfold tailWord_851362
  simp only [CollatzResearch.WordTrace]
  refine ⟨7762930785417087474685085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20701148761112233265826893 7762930785417087474685085)
  ·
    refine ⟨2911099044531407803006907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7762930785417087474685085 2911099044531407803006907)
    ·
      refine ⟨4366648566797111704510361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2911099044531407803006907 4366648566797111704510361)
      ·
        refine ⟨3274986425097833778382771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4366648566797111704510361 3274986425097833778382771)
        ·
          refine ⟨4912479637646750667574157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3274986425097833778382771 4912479637646750667574157)
          ·
            refine ⟨1842179864117531500340309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4912479637646750667574157 1842179864117531500340309)
            ·
              refine ⟨21588045282627322269613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1842179864117531500340309 21588045282627322269613)
              ·
                rfl

theorem cell21_851362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 8].length) (baseStart_851362 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_851362 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_851362 prefixEnd_851362 := by exact prefixLift 851362
  have htrace : WordTrace (prefixWord ++ tailWord_851362) baseStart_851362 baseEnd_851362 := by
    simpa [prefixWord, tailWord_851362, baseEnd_851362] using wordTrace_append hprefix tailTrace_851362
  have hstable : (prefixWord ++ tailWord_851362).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851362).length < 2 ^ (prefixWord ++ tailWord_851362).sum := by decide
  have hdescent : baseEnd_851362 < baseStart_851362 := by decide
  rcases family_descends (prefixWord ++ tailWord_851362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851396 : List Nat := [2, 3, 3, 2, 1, 3, 2, 5]
def baseStart_851396 : Nat := 118140960795 + 851396 * 2 ^ 59
def prefixEnd_851396 : Nat := 4983230072969 + 3 ^ 40 * 851396 * 2
def baseEnd_851396 : Nat := 64766722268956465619927

theorem tailTrace_851396 : CollatzResearch.WordTrace tailWord_851396 prefixEnd_851396 64766722268956465619927 := by
  unfold tailWord_851396
  simp only [CollatzResearch.WordTrace]
  refine ⟨15526481611772586852739021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20701975482363449136985361 15526481611772586852739021)
  ·
    refine ⟨5822430604414720069777133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15526481611772586852739021 5822430604414720069777133)
    ·
      refine ⟨2183411476655520026166425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5822430604414720069777133 2183411476655520026166425)
      ·
        refine ⟨1637558607491640019624819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2183411476655520026166425 1637558607491640019624819)
        ·
          refine ⟨2456337911237460029437229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1637558607491640019624819 2456337911237460029437229)
          ·
            refine ⟨921126716714047511038961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2456337911237460029437229 921126716714047511038961)
            ·
              refine ⟨690845037535535633279221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 921126716714047511038961 690845037535535633279221)
              ·
                refine ⟨64766722268956465619927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 690845037535535633279221 64766722268956465619927)
                ·
                  rfl

theorem cell21_851396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 5].length) (baseStart_851396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_851396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_851396 prefixEnd_851396 := by exact prefixLift 851396
  have htrace : WordTrace (prefixWord ++ tailWord_851396) baseStart_851396 baseEnd_851396 := by
    simpa [prefixWord, tailWord_851396, baseEnd_851396] using wordTrace_append hprefix tailTrace_851396
  have hstable : (prefixWord ++ tailWord_851396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851396).length < 2 ^ (prefixWord ++ tailWord_851396).sum := by decide
  have hdescent : baseEnd_851396 < baseStart_851396 := by decide
  rcases family_descends (prefixWord ++ tailWord_851396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851427 : List Nat := [1, 1, 1, 6, 2, 2, 3, 2, 3]
def baseStart_851427 : Nat := 118140960795 + 851427 * 2 ^ 59
def prefixEnd_851427 : Nat := 4983230072969 + 3 ^ 40 * 851427 * 2
def baseEnd_851427 : Nat := 194307241429220231843051

theorem tailTrace_851427 : CollatzResearch.WordTrace tailWord_851427 prefixEnd_851427 194307241429220231843051 := by
  unfold tailWord_851427
  simp only [CollatzResearch.WordTrace]
  refine ⟨31054093886432865999856535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20702729257621910666571023 31054093886432865999856535)
  ·
    refine ⟨46581140829649298999784803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31054093886432865999856535 46581140829649298999784803)
    ·
      refine ⟨69871711244473948499677205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46581140829649298999784803 69871711244473948499677205)
      ·
        refine ⟨3275236464584716335922369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 69871711244473948499677205 3275236464584716335922369)
        ·
          refine ⟨2456427348438537251941777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3275236464584716335922369 2456427348438537251941777)
          ·
            refine ⟨1842320511328902938956333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2456427348438537251941777 1842320511328902938956333)
            ·
              refine ⟨690870191748338602108625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1842320511328902938956333 690870191748338602108625)
              ·
                refine ⟨518152643811253951581469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 690870191748338602108625 518152643811253951581469)
                ·
                  refine ⟨194307241429220231843051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 518152643811253951581469 194307241429220231843051)
                  ·
                    rfl

theorem cell21_851427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 2, 3].length) (baseStart_851427 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_851427 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_851427 prefixEnd_851427 := by exact prefixLift 851427
  have htrace : WordTrace (prefixWord ++ tailWord_851427) baseStart_851427 baseEnd_851427 := by
    simpa [prefixWord, tailWord_851427, baseEnd_851427] using wordTrace_append hprefix tailTrace_851427
  have hstable : (prefixWord ++ tailWord_851427).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851427).length < 2 ^ (prefixWord ++ tailWord_851427).sum := by decide
  have hdescent : baseEnd_851427 < baseStart_851427 := by decide
  rcases family_descends (prefixWord ++ tailWord_851427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851438 : List Nat := [4, 1, 2, 1, 2, 1, 4, 6]
def baseStart_851438 : Nat := 118140960795 + 851438 * 2 ^ 59
def prefixEnd_851438 : Nat := 4983230072969 + 3 ^ 40 * 851438 * 2
def baseEnd_851438 : Nat := 64769917259695552386565

theorem tailTrace_851438 : CollatzResearch.WordTrace tailWord_851438 prefixEnd_851438 64769917259695552386565 := by
  unfold tailWord_851438
  simp only [CollatzResearch.WordTrace]
  refine ⟨3881811886174126859813371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20702996726262009919004645 3881811886174126859813371)
  ·
    refine ⟨5822717829261190289720057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3881811886174126859813371 5822717829261190289720057)
    ·
      refine ⟨4367038371945892717290043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5822717829261190289720057 4367038371945892717290043)
      ·
        refine ⟨6550557557918839075935065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4367038371945892717290043 6550557557918839075935065)
        ·
          refine ⟨4912918168439129306951299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6550557557918839075935065 4912918168439129306951299)
          ·
            refine ⟨7369377252658693960426949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4912918168439129306951299 7369377252658693960426949)
            ·
              refine ⟨1381758234873505117580053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7369377252658693960426949 1381758234873505117580053)
              ·
                refine ⟨64769917259695552386565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1381758234873505117580053 64769917259695552386565)
                ·
                  rfl

theorem cell21_851438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_851438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_851438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_851438 prefixEnd_851438 := by exact prefixLift 851438
  have htrace : WordTrace (prefixWord ++ tailWord_851438) baseStart_851438 baseEnd_851438 := by
    simpa [prefixWord, tailWord_851438, baseEnd_851438] using wordTrace_append hprefix tailTrace_851438
  have hstable : (prefixWord ++ tailWord_851438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851438).length < 2 ^ (prefixWord ++ tailWord_851438).sum := by decide
  have hdescent : baseEnd_851438 < baseStart_851438 := by decide
  rcases family_descends (prefixWord ++ tailWord_851438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851441 : List Nat := [1, 2, 2, 2, 3, 4, 2, 1, 4]
def baseStart_851441 : Nat := 118140960795 + 851441 * 2 ^ 59
def prefixEnd_851441 : Nat := 4983230072969 + 3 ^ 40 * 851441 * 2
def baseEnd_851441 : Nat := 194310436419959318609689

theorem tailTrace_851441 : CollatzResearch.WordTrace tailWord_851441 prefixEnd_851441 194310436419959318609689 := by
  unfold tailWord_851441
  simp only [CollatzResearch.WordTrace]
  refine ⟨31054604508382146390866177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20703069672254764260577451 31054604508382146390866177)
  ·
    refine ⟨23290953381286609793149633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31054604508382146390866177 23290953381286609793149633)
    ·
      refine ⟨17468215035964957344862225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23290953381286609793149633 17468215035964957344862225)
      ·
        refine ⟨13101161276973718008646669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17468215035964957344862225 13101161276973718008646669)
        ·
          refine ⟨4912935478865144253242501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13101161276973718008646669 4912935478865144253242501)
          ·
            refine ⟨921175402287214547482969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4912935478865144253242501 921175402287214547482969)
            ·
              refine ⟨690881551715410910612227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 921175402287214547482969 690881551715410910612227)
              ·
                refine ⟨1036322327573116365918341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 690881551715410910612227 1036322327573116365918341)
                ·
                  refine ⟨194310436419959318609689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1036322327573116365918341 194310436419959318609689)
                  ·
                    rfl

theorem cell21_851441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 4].length) (baseStart_851441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_851441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_851441 prefixEnd_851441 := by exact prefixLift 851441
  have htrace : WordTrace (prefixWord ++ tailWord_851441) baseStart_851441 baseEnd_851441 := by
    simpa [prefixWord, tailWord_851441, baseEnd_851441] using wordTrace_append hprefix tailTrace_851441
  have hstable : (prefixWord ++ tailWord_851441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851441).length < 2 ^ (prefixWord ++ tailWord_851441).sum := by decide
  have hdescent : baseEnd_851441 < baseStart_851441 := by decide
  rcases family_descends (prefixWord ++ tailWord_851441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851452 : List Nat := [2, 2, 2, 1, 2, 1, 2, 4, 5]
def baseStart_851452 : Nat := 118140960795 + 851452 * 2 ^ 59
def prefixEnd_851452 : Nat := 4983230072969 + 3 ^ 40 * 851452 * 2
def baseEnd_851452 : Nat := 194312946769825743926333

theorem tailTrace_851452 : CollatzResearch.WordTrace tailWord_851452 prefixEnd_851452 194312946769825743926333 := by
  unfold tailWord_851452
  simp only [CollatzResearch.WordTrace]
  refine ⟨15527502855671147634758305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20703337140894863513011073 15527502855671147634758305)
  ·
    refine ⟨11645627141753360726068729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15527502855671147634758305 11645627141753360726068729)
    ·
      refine ⟨8734220356315020544551547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11645627141753360726068729 8734220356315020544551547)
      ·
        refine ⟨13101330534472530816827321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8734220356315020544551547 13101330534472530816827321)
        ·
          refine ⟨9825997900854398112620491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13101330534472530816827321 9825997900854398112620491)
          ·
            refine ⟨14738996851281597168930737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9825997900854398112620491 14738996851281597168930737)
            ·
              refine ⟨11054247638461197876698053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14738996851281597168930737 11054247638461197876698053)
              ·
                refine ⟨2072671432211474601880885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11054247638461197876698053 2072671432211474601880885)
                ·
                  refine ⟨194312946769825743926333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2072671432211474601880885 194312946769825743926333)
                  ·
                    rfl

theorem cell21_851452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_851452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_851452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_851452 prefixEnd_851452 := by exact prefixLift 851452
  have htrace : WordTrace (prefixWord ++ tailWord_851452) baseStart_851452 baseEnd_851452 := by
    simpa [prefixWord, tailWord_851452, baseEnd_851452] using wordTrace_append hprefix tailTrace_851452
  have hstable : (prefixWord ++ tailWord_851452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851452).length < 2 ^ (prefixWord ++ tailWord_851452).sum := by decide
  have hdescent : baseEnd_851452 < baseStart_851452 := by decide
  rcases family_descends (prefixWord ++ tailWord_851452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851514 : List Nat := [3, 1, 1, 1, 3, 2, 5, 5]
def baseStart_851514 : Nat := 118140960795 + 851514 * 2 ^ 59
def prefixEnd_851514 : Nat := 4983230072969 + 3 ^ 40 * 851514 * 2
def baseEnd_851514 : Nat := 64775698671509137964291

theorem tailTrace_851514 : CollatzResearch.WordTrace tailWord_851514 prefixEnd_851514 64775698671509137964291 := by
  unfold tailWord_851514
  simp only [CollatzResearch.WordTrace]
  refine ⟨7764316759279419964568399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20704844691411786572182397 7764316759279419964568399)
  ·
    refine ⟨11646475138919129946852599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7764316759279419964568399 11646475138919129946852599)
    ·
      refine ⟨17469712708378694920278899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11646475138919129946852599 17469712708378694920278899)
      ·
        refine ⟨26204569062568042380418349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17469712708378694920278899 26204569062568042380418349)
        ·
          refine ⟨9826713398463015892656881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26204569062568042380418349 9826713398463015892656881)
          ·
            refine ⟨7370035048847261919492661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9826713398463015892656881 7370035048847261919492661)
            ·
              refine ⟨690940785829430804952437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7370035048847261919492661 690940785829430804952437)
              ·
                refine ⟨64775698671509137964291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 690940785829430804952437 64775698671509137964291)
                ·
                  rfl

theorem cell21_851514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 5].length) (baseStart_851514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_851514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_851514 prefixEnd_851514 := by exact prefixLift 851514
  have htrace : WordTrace (prefixWord ++ tailWord_851514) baseStart_851514 baseEnd_851514 := by
    simpa [prefixWord, tailWord_851514, baseEnd_851514] using wordTrace_append hprefix tailTrace_851514
  have hstable : (prefixWord ++ tailWord_851514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851514).length < 2 ^ (prefixWord ++ tailWord_851514).sum := by decide
  have hdescent : baseEnd_851514 < baseStart_851514 := by decide
  rcases family_descends (prefixWord ++ tailWord_851514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851559 : List Nat := [1, 1, 5, 1, 1, 1, 2, 5, 4]
def baseStart_851559 : Nat := 118140960795 + 851559 * 2 ^ 59
def prefixEnd_851559 : Nat := 4983230072969 + 3 ^ 40 * 851559 * 2
def baseEnd_851559 : Nat := 194337365627617335642781

theorem tailTrace_851559 : CollatzResearch.WordTrace tailWord_851559 prefixEnd_851559 194337365627617335642781 := by
  unfold tailWord_851559
  simp only [CollatzResearch.WordTrace]
  refine ⟨31058908321954652543661731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20705938881303101695774487 31058908321954652543661731)
  ·
    refine ⟨46588362482931978815492597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31058908321954652543661731 46588362482931978815492597)
    ·
      refine ⟨4367658982774873013952431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46588362482931978815492597 4367658982774873013952431)
      ·
        refine ⟨6551488474162309520928647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4367658982774873013952431 6551488474162309520928647)
        ·
          refine ⟨9827232711243464281392971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6551488474162309520928647 9827232711243464281392971)
          ·
            refine ⟨14740849066865196422089457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9827232711243464281392971 14740849066865196422089457)
            ·
              refine ⟨11055636800148897316567093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14740849066865196422089457 11055636800148897316567093)
              ·
                refine ⟨1036465950013959123428165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11055636800148897316567093 1036465950013959123428165)
                ·
                  refine ⟨194337365627617335642781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1036465950013959123428165 194337365627617335642781)
                  ·
                    rfl

theorem cell21_851559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 4].length) (baseStart_851559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_851559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_851559 prefixEnd_851559 := by exact prefixLift 851559
  have htrace : WordTrace (prefixWord ++ tailWord_851559) baseStart_851559 baseEnd_851559 := by
    simpa [prefixWord, tailWord_851559, baseEnd_851559] using wordTrace_append hprefix tailTrace_851559
  have hstable : (prefixWord ++ tailWord_851559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851559).length < 2 ^ (prefixWord ++ tailWord_851559).sum := by decide
  have hdescent : baseEnd_851559 < baseStart_851559 := by decide
  rcases family_descends (prefixWord ++ tailWord_851559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851649 : List Nat := [1, 2, 6, 12]
def baseStart_851649 : Nat := 118140960795 + 851649 * 2 ^ 59
def prefixEnd_851649 : Nat := 4983230072969 + 3 ^ 40 * 851649 * 2
def baseEnd_851649 : Nat := 799826768945667403879

theorem tailTrace_851649 : CollatzResearch.WordTrace tailWord_851649 prefixEnd_851649 799826768945667403879 := by
  unfold tailWord_851649
  simp only [CollatzResearch.WordTrace]
  refine ⟨31062190891628597914438001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20708127261085731942958667 31062190891628597914438001)
  ·
    refine ⟨23296643168721448435828501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31062190891628597914438001 23296643168721448435828501)
    ·
      refine ⟨1092030148533817895429461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23296643168721448435828501 1092030148533817895429461)
      ·
        refine ⟨799826768945667403879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1092030148533817895429461 799826768945667403879)
        ·
          rfl

theorem cell21_851649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 12].length) (baseStart_851649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_851649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_851649 prefixEnd_851649 := by exact prefixLift 851649
  have htrace : WordTrace (prefixWord ++ tailWord_851649) baseStart_851649 baseEnd_851649 := by
    simpa [prefixWord, tailWord_851649, baseEnd_851649] using wordTrace_append hprefix tailTrace_851649
  have hstable : (prefixWord ++ tailWord_851649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851649).length < 2 ^ (prefixWord ++ tailWord_851649).sum := by decide
  have hdescent : baseEnd_851649 < baseStart_851649 := by decide
  rcases family_descends (prefixWord ++ tailWord_851649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851652 : List Nat := [2, 3, 3, 1, 1, 1, 4, 2, 4]
def baseStart_851652 : Nat := 118140960795 + 851652 * 2 ^ 59
def prefixEnd_851652 : Nat := 4983230072969 + 3 ^ 40 * 851652 * 2
def baseEnd_851652 : Nat := 194358589494669840592591

theorem tailTrace_851652 : CollatzResearch.WordTrace tailWord_851652 prefixEnd_851652 194358589494669840592591 := by
  unfold tailWord_851652
  simp only [CollatzResearch.WordTrace]
  refine ⟨15531150155308864713398605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20708200207078486284531473 15531150155308864713398605)
  ·
    refine ⟨5824181308240824267524477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15531150155308864713398605 5824181308240824267524477)
    ·
      refine ⟨2184067990590309100321679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5824181308240824267524477 2184067990590309100321679)
      ·
        refine ⟨3276101985885463650482519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2184067990590309100321679 3276101985885463650482519)
        ·
          refine ⟨4914152978828195475723779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3276101985885463650482519 4914152978828195475723779)
          ·
            refine ⟨7371229468242293213585669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4914152978828195475723779 7371229468242293213585669)
            ·
              refine ⟨1382105525295429977547313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7371229468242293213585669 1382105525295429977547313)
              ·
                refine ⟨1036579143971572483160485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1382105525295429977547313 1036579143971572483160485)
                ·
                  refine ⟨194358589494669840592591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1036579143971572483160485 194358589494669840592591)
                  ·
                    rfl

theorem cell21_851652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_851652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_851652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_851652 prefixEnd_851652 := by exact prefixLift 851652
  have htrace : WordTrace (prefixWord ++ tailWord_851652) baseStart_851652 baseEnd_851652 := by
    simpa [prefixWord, tailWord_851652, baseEnd_851652] using wordTrace_append hprefix tailTrace_851652
  have hstable : (prefixWord ++ tailWord_851652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851652).length < 2 ^ (prefixWord ++ tailWord_851652).sum := by decide
  have hdescent : baseEnd_851652 < baseStart_851652 := by decide
  rcases family_descends (prefixWord ++ tailWord_851652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851663 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 9]
def baseStart_851663 : Nat := 118140960795 + 851663 * 2 ^ 59
def prefixEnd_851663 : Nat := 4983230072969 + 3 ^ 40 * 851663 * 2
def baseEnd_851663 : Nat := 194361099844536265909235

theorem tailTrace_851663 : CollatzResearch.WordTrace tailWord_851663 prefixEnd_851663 194361099844536265909235 := by
  unfold tailWord_851663
  simp only [CollatzResearch.WordTrace]
  refine ⟨31062701513577878305447643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20708467675718585536965095 31062701513577878305447643)
  ·
    refine ⟨46594052270366817458171465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31062701513577878305447643 46594052270366817458171465)
    ·
      refine ⟨34945539202775113093628599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46594052270366817458171465 34945539202775113093628599)
      ·
        refine ⟨52418308804162669640442899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34945539202775113093628599 52418308804162669640442899)
        ·
          refine ⟨78627463206244004460664349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52418308804162669640442899 78627463206244004460664349)
          ·
            refine ⟨29485298702341501672749131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78627463206244004460664349 29485298702341501672749131)
            ·
              refine ⟨44227948053512252509123697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29485298702341501672749131 44227948053512252509123697)
              ·
                refine ⟨33170961040134189381842773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44227948053512252509123697 33170961040134189381842773)
                ·
                  refine ⟨194361099844536265909235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 33170961040134189381842773 194361099844536265909235)
                  ·
                    rfl

theorem cell21_851663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 9].length) (baseStart_851663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_851663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_851663 prefixEnd_851663 := by exact prefixLift 851663
  have htrace : WordTrace (prefixWord ++ tailWord_851663) baseStart_851663 baseEnd_851663 := by
    simpa [prefixWord, tailWord_851663, baseEnd_851663] using wordTrace_append hprefix tailTrace_851663
  have hstable : (prefixWord ++ tailWord_851663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851663).length < 2 ^ (prefixWord ++ tailWord_851663).sum := by decide
  have hdescent : baseEnd_851663 < baseStart_851663 := by decide
  rcases family_descends (prefixWord ++ tailWord_851663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851666 : List Nat := [3, 2, 2, 2, 2, 1, 3, 6]
def baseStart_851666 : Nat := 118140960795 + 851666 * 2 ^ 59
def prefixEnd_851666 : Nat := 4983230072969 + 3 ^ 40 * 851666 * 2
def baseEnd_851666 : Nat := 64787261495136309119743

theorem tailTrace_851666 : CollatzResearch.WordTrace tailWord_851666 prefixEnd_851666 64787261495136309119743 := by
  unfold tailWord_851666
  simp only [CollatzResearch.WordTrace]
  refine ⟨7765702733141752454451713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20708540621711339878537901 7765702733141752454451713)
  ·
    refine ⟨5824277049856314340838785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7765702733141752454451713 5824277049856314340838785)
    ·
      refine ⟨4368207787392235755629089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5824277049856314340838785 4368207787392235755629089)
      ·
        refine ⟨3276155840544176816721817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4368207787392235755629089 3276155840544176816721817)
        ·
          refine ⟨2457116880408132612541363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3276155840544176816721817 2457116880408132612541363)
          ·
            refine ⟨3685675320612198918812045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2457116880408132612541363 3685675320612198918812045)
            ·
              refine ⟨1382128245229574594554517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3685675320612198918812045 1382128245229574594554517)
              ·
                refine ⟨64787261495136309119743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1382128245229574594554517 64787261495136309119743)
                ·
                  rfl

theorem cell21_851666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 6].length) (baseStart_851666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_851666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_851666 prefixEnd_851666 := by exact prefixLift 851666
  have htrace : WordTrace (prefixWord ++ tailWord_851666) baseStart_851666 baseEnd_851666 := by
    simpa [prefixWord, tailWord_851666, baseEnd_851666] using wordTrace_append hprefix tailTrace_851666
  have hstable : (prefixWord ++ tailWord_851666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851666).length < 2 ^ (prefixWord ++ tailWord_851666).sum := by decide
  have hdescent : baseEnd_851666 < baseStart_851666 := by decide
  rcases family_descends (prefixWord ++ tailWord_851666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851683 : List Nat := [1, 1, 1, 7, 2, 1, 3, 5]
def baseStart_851683 : Nat := 118140960795 + 851683 * 2 ^ 59
def prefixEnd_851683 : Nat := 4983230072969 + 3 ^ 40 * 851683 * 2
def baseEnd_851683 : Nat := 64788554705673558525287

theorem tailTrace_851683 : CollatzResearch.WordTrace tailWord_851683 prefixEnd_851683 64788554705673558525287 := by
  unfold tailWord_851683
  simp only [CollatzResearch.WordTrace]
  refine ⟨31063430973505421721175703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20708953982336947814117135 31063430973505421721175703)
  ·
    refine ⟨46595146460258132581763555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31063430973505421721175703 46595146460258132581763555)
    ·
      refine ⟨69892719690387198872645333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46595146460258132581763555 69892719690387198872645333)
      ·
        refine ⟨1638110617743449973577625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 69892719690387198872645333 1638110617743449973577625)
        ·
          refine ⟨1228582963307587480183219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1638110617743449973577625 1228582963307587480183219)
          ·
            refine ⟨1842874444961381220274829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1228582963307587480183219 1842874444961381220274829)
            ·
              refine ⟨691077916860517957603061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1842874444961381220274829 691077916860517957603061)
              ·
                refine ⟨64788554705673558525287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 691077916860517957603061 64788554705673558525287)
                ·
                  rfl

theorem cell21_851683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 5].length) (baseStart_851683 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_851683 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_851683 prefixEnd_851683 := by exact prefixLift 851683
  have htrace : WordTrace (prefixWord ++ tailWord_851683) baseStart_851683 baseEnd_851683 := by
    simpa [prefixWord, tailWord_851683, baseEnd_851683] using wordTrace_append hprefix tailTrace_851683
  have hstable : (prefixWord ++ tailWord_851683).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851683).length < 2 ^ (prefixWord ++ tailWord_851683).sum := by decide
  have hdescent : baseEnd_851683 < baseStart_851683 := by decide
  rcases family_descends (prefixWord ++ tailWord_851683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851697 : List Nat := [1, 2, 2, 2, 2, 3, 1, 5, 3]
def baseStart_851697 : Nat := 118140960795 + 851697 * 2 ^ 59
def prefixEnd_851697 : Nat := 4983230072969 + 3 ^ 40 * 851697 * 2
def baseEnd_851697 : Nat := 194368859107759762342499

theorem tailTrace_851697 : CollatzResearch.WordTrace tailWord_851697 prefixEnd_851697 194368859107759762342499 := by
  unfold tailWord_851697
  simp only [CollatzResearch.WordTrace]
  refine ⟨31063941595454702112185345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20709294396969801408123563 31063941595454702112185345)
  ·
    refine ⟨23297956196591026584139009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31063941595454702112185345 23297956196591026584139009)
    ·
      refine ⟨17473467147443269938104257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23297956196591026584139009 17473467147443269938104257)
      ·
        refine ⟨13105100360582452453578193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17473467147443269938104257 13105100360582452453578193)
        ·
          refine ⟨9828825270436839340183645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13105100360582452453578193 9828825270436839340183645)
          ·
            refine ⟨3685809476413814752568867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9828825270436839340183645 3685809476413814752568867)
            ·
              refine ⟨5528714214620722128853301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3685809476413814752568867 5528714214620722128853301)
              ·
                refine ⟨518316957620692699579997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5528714214620722128853301 518316957620692699579997)
                ·
                  refine ⟨194368859107759762342499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 518316957620692699579997 194368859107759762342499)
                  ·
                    rfl

theorem cell21_851697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 5, 3].length) (baseStart_851697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_851697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_851697 prefixEnd_851697 := by exact prefixLift 851697
  have htrace : WordTrace (prefixWord ++ tailWord_851697) baseStart_851697 baseEnd_851697 := by
    simpa [prefixWord, tailWord_851697, baseEnd_851697] using wordTrace_append hprefix tailTrace_851697
  have hstable : (prefixWord ++ tailWord_851697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851697).length < 2 ^ (prefixWord ++ tailWord_851697).sum := by decide
  have hdescent : baseEnd_851697 < baseStart_851697 := by decide
  rcases family_descends (prefixWord ++ tailWord_851697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851711 : List Nat := [1, 1, 2, 2, 1, 3, 5, 2, 4]
def baseStart_851711 : Nat := 118140960795 + 851711 * 2 ^ 59
def prefixEnd_851711 : Nat := 4983230072969 + 3 ^ 40 * 851711 * 2
def baseEnd_851711 : Nat := 194372054098498849109137

theorem tailTrace_851711 : CollatzResearch.WordTrace tailWord_851711 prefixEnd_851711 194372054098498849109137 := by
  unfold tailWord_851711
  simp only [CollatzResearch.WordTrace]
  refine ⟨31064452217403982503194987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20709634811602655002129991 31064452217403982503194987)
  ·
    refine ⟨46596678326105973754792481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31064452217403982503194987 46596678326105973754792481)
    ·
      refine ⟨34947508744579480316094361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46596678326105973754792481 34947508744579480316094361)
      ·
        refine ⟨26210631558434610237070771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34947508744579480316094361 26210631558434610237070771)
        ·
          refine ⟨39315947337651915355606157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26210631558434610237070771 39315947337651915355606157)
          ·
            refine ⟨14743480251619468258352309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39315947337651915355606157 14743480251619468258352309)
            ·
              refine ⟨1382201273589325149220529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14743480251619468258352309 1382201273589325149220529)
              ·
                refine ⟨1036650955191993861915397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1382201273589325149220529 1036650955191993861915397)
                ·
                  refine ⟨194372054098498849109137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1036650955191993861915397 194372054098498849109137)
                  ·
                    rfl

theorem cell21_851711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 4].length) (baseStart_851711 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_851711 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_851711 prefixEnd_851711 := by exact prefixLift 851711
  have htrace : WordTrace (prefixWord ++ tailWord_851711) baseStart_851711 baseEnd_851711 := by
    simpa [prefixWord, tailWord_851711, baseEnd_851711] using wordTrace_append hprefix tailTrace_851711
  have hstable : (prefixWord ++ tailWord_851711).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851711).length < 2 ^ (prefixWord ++ tailWord_851711).sum := by decide
  have hdescent : baseEnd_851711 < baseStart_851711 := by decide
  rcases family_descends (prefixWord ++ tailWord_851711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851714 : List Nat := [3, 4, 1, 1, 1, 1, 1, 6, 3]
def baseStart_851714 : Nat := 118140960795 + 851714 * 2 ^ 59
def prefixEnd_851714 : Nat := 4983230072969 + 3 ^ 40 * 851714 * 2
def baseEnd_851714 : Nat := 194372738739371510559131

theorem tailTrace_851714 : CollatzResearch.WordTrace tailWord_851714 prefixEnd_851714 194372738739371510559131 := by
  unfold tailWord_851714
  simp only [CollatzResearch.WordTrace]
  refine ⟨7766140409098278503888549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20709707757595409343702797 7766140409098278503888549)
  ·
    refine ⟨1456151326705927219479103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7766140409098278503888549 1456151326705927219479103)
    ·
      refine ⟨2184226990058890829218655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1456151326705927219479103 2184226990058890829218655)
      ·
        refine ⟨3276340485088336243827983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2184226990058890829218655 3276340485088336243827983)
        ·
          refine ⟨4914510727632504365741975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3276340485088336243827983 4914510727632504365741975)
          ·
            refine ⟨7371766091448756548612963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4914510727632504365741975 7371766091448756548612963)
            ·
              refine ⟨11057649137173134822919445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7371766091448756548612963 11057649137173134822919445)
              ·
                refine ⟨518327303304990694824349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11057649137173134822919445 518327303304990694824349)
                ·
                  refine ⟨194372738739371510559131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 518327303304990694824349 194372738739371510559131)
                  ·
                    rfl

theorem cell21_851714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_851714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_851714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_851714 prefixEnd_851714 := by exact prefixLift 851714
  have htrace : WordTrace (prefixWord ++ tailWord_851714) baseStart_851714 baseEnd_851714 := by
    simpa [prefixWord, tailWord_851714, baseEnd_851714] using wordTrace_append hprefix tailTrace_851714
  have hstable : (prefixWord ++ tailWord_851714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851714).length < 2 ^ (prefixWord ++ tailWord_851714).sum := by decide
  have hdescent : baseEnd_851714 < baseStart_851714 := by decide
  rcases family_descends (prefixWord ++ tailWord_851714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851773 : List Nat := [1, 4, 1, 4, 1, 1, 3, 1, 5]
def baseStart_851773 : Nat := 118140960795 + 851773 * 2 ^ 59
def prefixEnd_851773 : Nat := 4983230072969 + 3 ^ 40 * 851773 * 2
def baseEnd_851773 : Nat := 194386203343200519075677

theorem tailTrace_851773 : CollatzResearch.WordTrace tailWord_851773 prefixEnd_851773 194386203343200519075677 := by
  unfold tailWord_851773
  simp only [CollatzResearch.WordTrace]
  refine ⟨31066713543179367091951973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20711142362119578061301315 31066713543179367091951973)
  ·
    refine ⟨5825008789346131329740995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31066713543179367091951973 5825008789346131329740995)
    ·
      refine ⟨8737513184019196994611493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5825008789346131329740995 8737513184019196994611493)
      ·
        refine ⟨1638283722003599436489655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8737513184019196994611493 1638283722003599436489655)
        ·
          refine ⟨2457425583005399154734483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1638283722003599436489655 2457425583005399154734483)
          ·
            refine ⟨3686138374508098732101725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2457425583005399154734483 3686138374508098732101725)
            ·
              refine ⟨1382301890440537024538147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3686138374508098732101725 1382301890440537024538147)
              ·
                refine ⟨2073452835660805536807221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1382301890440537024538147 2073452835660805536807221)
                ·
                  refine ⟨194386203343200519075677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2073452835660805536807221 194386203343200519075677)
                  ·
                    rfl

theorem cell21_851773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_851773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_851773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_851773 prefixEnd_851773 := by exact prefixLift 851773
  have htrace : WordTrace (prefixWord ++ tailWord_851773) baseStart_851773 baseEnd_851773 := by
    simpa [prefixWord, tailWord_851773, baseEnd_851773] using wordTrace_append hprefix tailTrace_851773
  have hstable : (prefixWord ++ tailWord_851773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851773).length < 2 ^ (prefixWord ++ tailWord_851773).sum := by decide
  have hdescent : baseEnd_851773 < baseStart_851773 := by decide
  rcases family_descends (prefixWord ++ tailWord_851773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851818 : List Nat := [3, 1, 3, 4, 1, 9]
def baseStart_851818 : Nat := 118140960795 + 851818 * 2 ^ 59
def prefixEnd_851818 : Nat := 4983230072969 + 3 ^ 40 * 851818 * 2
def baseEnd_851818 : Nat := 7199869368751497808355

theorem tailTrace_851818 : CollatzResearch.WordTrace tailWord_851818 prefixEnd_851818 7199869368751497808355 := by
  unfold tailWord_851818
  simp only [CollatzResearch.WordTrace]
  refine ⟨7767088707004084944335027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20712236552010893184893405 7767088707004084944335027)
  ·
    refine ⟨11650633060506127416502541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7767088707004084944335027 11650633060506127416502541)
    ·
      refine ⟨4368987397689797781188453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11650633060506127416502541 4368987397689797781188453)
      ·
        refine ⟨819185137066837083972835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4368987397689797781188453 819185137066837083972835)
        ·
          refine ⟨1228777705600255625959253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 819185137066837083972835 1228777705600255625959253)
          ·
            refine ⟨7199869368751497808355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1228777705600255625959253 7199869368751497808355)
            ·
              rfl

theorem cell21_851818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 9].length) (baseStart_851818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_851818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_851818 prefixEnd_851818 := by exact prefixLift 851818
  have htrace : WordTrace (prefixWord ++ tailWord_851818) baseStart_851818 baseEnd_851818 := by
    simpa [prefixWord, tailWord_851818, baseEnd_851818] using wordTrace_append hprefix tailTrace_851818
  have hstable : (prefixWord ++ tailWord_851818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851818).length < 2 ^ (prefixWord ++ tailWord_851818).sum := by decide
  have hdescent : baseEnd_851818 < baseStart_851818 := by decide
  rcases family_descends (prefixWord ++ tailWord_851818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851866 : List Nat := [3, 1, 1, 4, 2, 2, 2, 3, 3]
def baseStart_851866 : Nat := 118140960795 + 851866 * 2 ^ 59
def prefixEnd_851866 : Nat := 4983230072969 + 3 ^ 40 * 851866 * 2
def baseEnd_851866 : Nat := 194407427210253024025487

theorem tailTrace_851866 : CollatzResearch.WordTrace tailWord_851866 prefixEnd_851866 194407427210253024025487 := by
  unfold tailWord_851866
  simp only [CollatzResearch.WordTrace]
  refine ⟨7767526382960610993771863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20713403687894962650058301 7767526382960610993771863)
  ·
    refine ⟨11651289574440916490657795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7767526382960610993771863 11651289574440916490657795)
    ·
      refine ⟨17476934361661374735986693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11651289574440916490657795 17476934361661374735986693)
      ·
        refine ⟨3276925192811507762997505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17476934361661374735986693 3276925192811507762997505)
        ·
          refine ⟨2457693894608630822248129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3276925192811507762997505 2457693894608630822248129)
          ·
            refine ⟨1843270420956473116686097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2457693894608630822248129 1843270420956473116686097)
            ·
              refine ⟨1382452815717354837514573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1843270420956473116686097 1382452815717354837514573)
              ·
                refine ⟨518419805894008064067965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1382452815717354837514573 518419805894008064067965)
                ·
                  refine ⟨194407427210253024025487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 518419805894008064067965 194407427210253024025487)
                  ·
                    rfl

theorem cell21_851866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 3, 3].length) (baseStart_851866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_851866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_851866 prefixEnd_851866 := by exact prefixLift 851866
  have htrace : WordTrace (prefixWord ++ tailWord_851866) baseStart_851866 baseEnd_851866 := by
    simpa [prefixWord, tailWord_851866, baseEnd_851866] using wordTrace_append hprefix tailTrace_851866
  have hstable : (prefixWord ++ tailWord_851866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851866).length < 2 ^ (prefixWord ++ tailWord_851866).sum := by decide
  have hdescent : baseEnd_851866 < baseStart_851866 := by decide
  rcases family_descends (prefixWord ++ tailWord_851866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851967 : List Nat := [1, 1, 2, 2, 1, 2, 1, 6, 5]
def baseStart_851967 : Nat := 118140960795 + 851967 * 2 ^ 59
def prefixEnd_851967 : Nat := 4983230072969 + 3 ^ 40 * 851967 * 2
def baseEnd_851967 : Nat := 194430476786299292841947

theorem tailTrace_851967 : CollatzResearch.WordTrace tailWord_851967 prefixEnd_851967 194430476786299292841947 := by
  unfold tailWord_851967
  simp only [CollatzResearch.WordTrace]
  refine ⟨31073789304476538224514155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20715859536317692149676103 31073789304476538224514155)
  ·
    refine ⟨46610683956714807336771233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31073789304476538224514155 46610683956714807336771233)
    ·
      refine ⟨34958012967536105502578425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46610683956714807336771233 34958012967536105502578425)
      ·
        refine ⟨26218509725652079126933819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34958012967536105502578425 26218509725652079126933819)
        ·
          refine ⟨39327764588478118690400729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26218509725652079126933819 39327764588478118690400729)
          ·
            refine ⟨29495823441358589017800547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39327764588478118690400729 29495823441358589017800547)
            ·
              refine ⟨44243735162037883526700821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29495823441358589017800547 44243735162037883526700821)
              ·
                refine ⟨2073925085720525790314101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44243735162037883526700821 2073925085720525790314101)
                ·
                  refine ⟨194430476786299292841947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2073925085720525790314101 194430476786299292841947)
                  ·
                    rfl

theorem cell21_851967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 5].length) (baseStart_851967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_851967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_851967 prefixEnd_851967 := by exact prefixLift 851967
  have htrace : WordTrace (prefixWord ++ tailWord_851967) baseStart_851967 baseEnd_851967 := by
    simpa [prefixWord, tailWord_851967, baseEnd_851967] using wordTrace_append hprefix tailTrace_851967
  have hstable : (prefixWord ++ tailWord_851967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851967).length < 2 ^ (prefixWord ++ tailWord_851967).sum := by decide
  have hdescent : baseEnd_851967 < baseStart_851967 := by decide
  rcases family_descends (prefixWord ++ tailWord_851967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852012 : List Nat := [2, 2, 1, 1, 1, 2, 2, 10]
def baseStart_852012 : Nat := 118140960795 + 852012 * 2 ^ 59
def prefixEnd_852012 : Nat := 4983230072969 + 3 ^ 40 * 852012 * 2
def baseEnd_852012 : Nat := 64813582133129738197285

theorem tailTrace_852012 : CollatzResearch.WordTrace tailWord_852012 prefixEnd_852012 64813582133129738197285 := by
  unfold tailWord_852012
  simp only [CollatzResearch.WordTrace]
  refine ⟨15537715294656755454951145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20716953726209007273268193 15537715294656755454951145)
  ·
    refine ⟨11653286470992566591213359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15537715294656755454951145 11653286470992566591213359)
    ·
      refine ⟨17479929706488849886820039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11653286470992566591213359 17479929706488849886820039)
      ·
        refine ⟨26219894559733274830230059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17479929706488849886820039 26219894559733274830230059)
        ·
          refine ⟨39329841839599912245345089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26219894559733274830230059 39329841839599912245345089)
          ·
            refine ⟨29497381379699934184008817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39329841839599912245345089 29497381379699934184008817)
            ·
              refine ⟨22123036034774950638006613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29497381379699934184008817 22123036034774950638006613)
              ·
                refine ⟨64813582133129738197285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 22123036034774950638006613 64813582133129738197285)
                ·
                  rfl

theorem cell21_852012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 10].length) (baseStart_852012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_852012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_852012 prefixEnd_852012 := by exact prefixLift 852012
  have htrace : WordTrace (prefixWord ++ tailWord_852012) baseStart_852012 baseEnd_852012 := by
    simpa [prefixWord, tailWord_852012, baseEnd_852012] using wordTrace_append hprefix tailTrace_852012
  have hstable : (prefixWord ++ tailWord_852012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852012).length < 2 ^ (prefixWord ++ tailWord_852012).sum := by decide
  have hdescent : baseEnd_852012 < baseStart_852012 := by decide
  rcases family_descends (prefixWord ++ tailWord_852012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852060 : List Nat := [2, 2, 4, 1, 1, 2, 1, 3, 5]
def baseStart_852060 : Nat := 118140960795 + 852060 * 2 ^ 59
def prefixEnd_852060 : Nat := 4983230072969 + 3 ^ 40 * 852060 * 2
def baseEnd_852060 : Nat := 194451700653351797791757

theorem tailTrace_852060 : CollatzResearch.WordTrace tailWord_852060 prefixEnd_852060 194451700653351797791757 := by
  unfold tailWord_852060
  simp only [CollatzResearch.WordTrace]
  refine ⟨15538590646569807553824817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20718120862093076738433089 15538590646569807553824817)
  ·
    refine ⟨11653942984927355665368613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15538590646569807553824817 11653942984927355665368613)
    ·
      refine ⟨2185114309673879187256615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11653942984927355665368613 2185114309673879187256615)
      ·
        refine ⟨3277671464510818780884923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2185114309673879187256615 3277671464510818780884923)
        ·
          refine ⟨4916507196766228171327385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3277671464510818780884923 4916507196766228171327385)
          ·
            refine ⟨3687380397574671128495539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4916507196766228171327385 3687380397574671128495539)
            ·
              refine ⟨5531070596362006692743309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3687380397574671128495539 5531070596362006692743309)
              ·
                refine ⟨2074151473635752509778741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5531070596362006692743309 2074151473635752509778741)
                ·
                  refine ⟨194451700653351797791757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2074151473635752509778741 194451700653351797791757)
                  ·
                    rfl

theorem cell21_852060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_852060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_852060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_852060 prefixEnd_852060 := by exact prefixLift 852060
  have htrace : WordTrace (prefixWord ++ tailWord_852060) baseStart_852060 baseEnd_852060 := by
    simpa [prefixWord, tailWord_852060, baseEnd_852060] using wordTrace_append hprefix tailTrace_852060
  have hstable : (prefixWord ++ tailWord_852060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852060).length < 2 ^ (prefixWord ++ tailWord_852060).sum := by decide
  have hdescent : baseEnd_852060 < baseStart_852060 := by decide
  rcases family_descends (prefixWord ++ tailWord_852060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852122 : List Nat := [3, 1, 1, 5, 2, 1, 2, 6]
def baseStart_852122 : Nat := 118140960795 + 852122 * 2 ^ 59
def prefixEnd_852122 : Nat := 4983230072969 + 3 ^ 40 * 852122 * 2
def baseEnd_852122 : Nat := 64821949966017822586099

theorem tailTrace_852122 : CollatzResearch.WordTrace tailWord_852122 prefixEnd_852122 64821949966017822586099 := by
  unfold tailWord_852122
  simp only [CollatzResearch.WordTrace]
  refine ⟨7769860654728749924101655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20719628412609999797604413 7769860654728749924101655)
  ·
    refine ⟨11654790982093124886152483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7769860654728749924101655 11654790982093124886152483)
    ·
      refine ⟨17482186473139687329228725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11654790982093124886152483 17482186473139687329228725)
      ·
        refine ⟨1638954981856845687115193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17482186473139687329228725 1638954981856845687115193)
        ·
          refine ⟨1229216236392634265336395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1638954981856845687115193 1229216236392634265336395)
          ·
            refine ⟨1843824354588951398004593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1229216236392634265336395 1843824354588951398004593)
            ·
              refine ⟨1382868265941713548503445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1843824354588951398004593 1382868265941713548503445)
              ·
                refine ⟨64821949966017822586099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1382868265941713548503445 64821949966017822586099)
                ·
                  rfl

theorem cell21_852122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 6].length) (baseStart_852122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_852122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_852122 prefixEnd_852122 := by exact prefixLift 852122
  have htrace : WordTrace (prefixWord ++ tailWord_852122) baseStart_852122 baseEnd_852122 := by
    simpa [prefixWord, tailWord_852122, baseEnd_852122] using wordTrace_append hprefix tailTrace_852122
  have hstable : (prefixWord ++ tailWord_852122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852122).length < 2 ^ (prefixWord ++ tailWord_852122).sum := by decide
  have hdescent : baseEnd_852122 < baseStart_852122 := by decide
  rcases family_descends (prefixWord ++ tailWord_852122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852257 : List Nat := [1, 2, 3, 2, 1, 1, 6, 5]
def baseStart_852257 : Nat := 118140960795 + 852257 * 2 ^ 59
def prefixEnd_852257 : Nat := 4983230072969 + 3 ^ 40 * 852257 * 2
def baseEnd_852257 : Nat := 64832219579107744336007

theorem tailTrace_852257 : CollatzResearch.WordTrace tailWord_852257 prefixEnd_852257 64832219579107744336007 := by
  unfold tailWord_852257
  simp only [CollatzResearch.WordTrace]
  refine ⟨31084366473425917752571025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20722910982283945168380683 31084366473425917752571025)
  ·
    refine ⟨23313274855069438314428269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31084366473425917752571025 23313274855069438314428269)
    ·
      refine ⟨8742478070651039367910601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23313274855069438314428269 8742478070651039367910601)
      ·
        refine ⟨6556858552988279525932951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8742478070651039367910601 6556858552988279525932951)
        ·
          refine ⟨9835287829482419288899427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6556858552988279525932951 9835287829482419288899427)
          ·
            refine ⟨14752931744223628933349141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9835287829482419288899427 14752931744223628933349141)
            ·
              refine ⟨691543675510482606250741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14752931744223628933349141 691543675510482606250741)
              ·
                refine ⟨64832219579107744336007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 691543675510482606250741 64832219579107744336007)
                ·
                  rfl

theorem cell21_852257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 5].length) (baseStart_852257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_852257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_852257 prefixEnd_852257 := by exact prefixLift 852257
  have htrace : WordTrace (prefixWord ++ tailWord_852257) baseStart_852257 baseEnd_852257 := by
    simpa [prefixWord, tailWord_852257, baseEnd_852257] using wordTrace_append hprefix tailTrace_852257
  have hstable : (prefixWord ++ tailWord_852257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852257).length < 2 ^ (prefixWord ++ tailWord_852257).sum := by decide
  have hdescent : baseEnd_852257 < baseStart_852257 := by decide
  rcases family_descends (prefixWord ++ tailWord_852257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852274 : List Nat := [3, 2, 1, 1, 6, 1, 7]
def baseStart_852274 : Nat := 118140960795 + 852274 * 2 ^ 59
def prefixEnd_852274 : Nat := 4983230072969 + 3 ^ 40 * 852274 * 2
def baseEnd_852274 : Nat := 21611170929881664580517

theorem tailTrace_852274 : CollatzResearch.WordTrace tailWord_852274 prefixEnd_852274 21611170929881664580517 := by
  unfold tailWord_852274
  simp only [CollatzResearch.WordTrace]
  refine ⟨7771246628591082413984969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20723324342909553103959917 7771246628591082413984969)
  ·
    refine ⟨5828434971443311810488727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7771246628591082413984969 5828434971443311810488727)
    ·
      refine ⟨8742652457164967715733091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5828434971443311810488727 8742652457164967715733091)
      ·
        refine ⟨13113978685747451573599637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8742652457164967715733091 13113978685747451573599637)
        ·
          refine ⟨614717750894411792512483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13113978685747451573599637 614717750894411792512483)
          ·
            refine ⟨922076626341617688768725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 614717750894411792512483 922076626341617688768725)
            ·
              refine ⟨21611170929881664580517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 922076626341617688768725 21611170929881664580517)
              ·
                rfl

theorem cell21_852274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 7].length) (baseStart_852274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_852274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_852274 prefixEnd_852274 := by exact prefixLift 852274
  have htrace : WordTrace (prefixWord ++ tailWord_852274) baseStart_852274 baseEnd_852274 := by
    simpa [prefixWord, tailWord_852274, baseEnd_852274] using wordTrace_append hprefix tailTrace_852274
  have hstable : (prefixWord ++ tailWord_852274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852274).length < 2 ^ (prefixWord ++ tailWord_852274).sum := by decide
  have hdescent : baseEnd_852274 < baseStart_852274 := by decide
  rcases family_descends (prefixWord ++ tailWord_852274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852412 : List Nat := [2, 2, 2, 4, 1, 2, 3, 1, 4]
def baseStart_852412 : Nat := 118140960795 + 852412 * 2 ^ 59
def prefixEnd_852412 : Nat := 4983230072969 + 3 ^ 40 * 852412 * 2
def baseEnd_852412 : Nat := 194532031849077407924371

theorem tailTrace_852412 : CollatzResearch.WordTrace tailWord_852412 prefixEnd_852412 194532031849077407924371 := by
  unfold tailWord_852412
  simp only [CollatzResearch.WordTrace]
  refine ⟨15545009893932189612231745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20726679858576252816308993 15545009893932189612231745)
  ·
    refine ⟨11658757420449142209173809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15545009893932189612231745 11658757420449142209173809)
    ·
      refine ⟨8744068065336856656880357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11658757420449142209173809 8744068065336856656880357)
      ·
        refine ⟨1639512762250660623165067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8744068065336856656880357 1639512762250660623165067)
        ·
          refine ⟨2459269143375990934747601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1639512762250660623165067 2459269143375990934747601)
          ·
            refine ⟨1844451857531993201060701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2459269143375990934747601 1844451857531993201060701)
            ·
              refine ⟨691669446574497450397763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1844451857531993201060701 691669446574497450397763)
              ·
                refine ⟨1037504169861746175596645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 691669446574497450397763 1037504169861746175596645)
                ·
                  refine ⟨194532031849077407924371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1037504169861746175596645 194532031849077407924371)
                  ·
                    rfl

theorem cell21_852412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 4].length) (baseStart_852412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_852412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_852412 prefixEnd_852412 := by exact prefixLift 852412
  have htrace : WordTrace (prefixWord ++ tailWord_852412) baseStart_852412 baseEnd_852412 := by
    simpa [prefixWord, tailWord_852412, baseEnd_852412] using wordTrace_append hprefix tailTrace_852412
  have hstable : (prefixWord ++ tailWord_852412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852412).length < 2 ^ (prefixWord ++ tailWord_852412).sum := by decide
  have hdescent : baseEnd_852412 < baseStart_852412 := by decide
  rcases family_descends (prefixWord ++ tailWord_852412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852423 : List Nat := [1, 1, 4, 1, 1, 4, 2, 2, 5]
def baseStart_852423 : Nat := 118140960795 + 852423 * 2 ^ 59
def prefixEnd_852423 : Nat := 4983230072969 + 3 ^ 40 * 852423 * 2
def baseEnd_852423 : Nat := 194534542198943833241015

theorem tailTrace_852423 : CollatzResearch.WordTrace tailWord_852423 prefixEnd_852423 194534542198943833241015 := by
  unfold tailWord_852423
  simp only [CollatzResearch.WordTrace]
  refine ⟨31090420990824528103113923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20726947327216352068742615 31090420990824528103113923)
  ·
    refine ⟨46635631486236792154670885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31090420990824528103113923 46635631486236792154670885)
    ·
      refine ⟨8744180903669398529000791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46635631486236792154670885 8744180903669398529000791)
      ·
        refine ⟨13116271355504097793501187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8744180903669398529000791 13116271355504097793501187)
        ·
          refine ⟨19674407033256146690251781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13116271355504097793501187 19674407033256146690251781)
          ·
            refine ⟨3688951318735527504422209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19674407033256146690251781 3688951318735527504422209)
            ·
              refine ⟨2766713489051645628316657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3688951318735527504422209 2766713489051645628316657)
              ·
                refine ⟨2075035116788734221237493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2766713489051645628316657 2075035116788734221237493)
                ·
                  refine ⟨194534542198943833241015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2075035116788734221237493 194534542198943833241015)
                  ·
                    rfl

theorem cell21_852423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 5].length) (baseStart_852423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_852423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_852423 prefixEnd_852423 := by exact prefixLift 852423
  have htrace : WordTrace (prefixWord ++ tailWord_852423) baseStart_852423 baseEnd_852423 := by
    simpa [prefixWord, tailWord_852423, baseEnd_852423] using wordTrace_append hprefix tailTrace_852423
  have hstable : (prefixWord ++ tailWord_852423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852423).length < 2 ^ (prefixWord ++ tailWord_852423).sum := by decide
  have hdescent : baseEnd_852423 < baseStart_852423 := by decide
  rcases family_descends (prefixWord ++ tailWord_852423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852519 : List Nat := [1, 1, 7, 2, 1, 2, 1, 6]
def baseStart_852519 : Nat := 118140960795 + 852519 * 2 ^ 59
def prefixEnd_852519 : Nat := 4983230072969 + 3 ^ 40 * 852519 * 2
def baseEnd_852519 : Nat := 64852150235622999880273

theorem tailTrace_852519 : CollatzResearch.WordTrace tailWord_852519 prefixEnd_852519 64852150235622999880273 := by
  unfold tailWord_852519
  simp only [CollatzResearch.WordTrace]
  refine ⟨31093922398476736498608611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20729281598984490999072407 31093922398476736498608611)
  ·
    refine ⟨46640883597715104747912917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31093922398476736498608611 46640883597715104747912917)
    ·
      refine ⟨1093145709321447767529209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 46640883597715104747912917 1093145709321447767529209)
      ·
        refine ⟨819859281991085825646907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1093145709321447767529209 819859281991085825646907)
        ·
          refine ⟨1229788922986628738470361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 819859281991085825646907 1229788922986628738470361)
          ·
            refine ⟨922341692239971553852771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1229788922986628738470361 922341692239971553852771)
            ·
              refine ⟨1383512538359957330779157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 922341692239971553852771 1383512538359957330779157)
              ·
                refine ⟨64852150235622999880273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1383512538359957330779157 64852150235622999880273)
                ·
                  rfl

theorem cell21_852519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 6].length) (baseStart_852519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_852519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_852519 prefixEnd_852519 := by exact prefixLift 852519
  have htrace : WordTrace (prefixWord ++ tailWord_852519) baseStart_852519 baseEnd_852519 := by
    simpa [prefixWord, tailWord_852519, baseEnd_852519] using wordTrace_append hprefix tailTrace_852519
  have hstable : (prefixWord ++ tailWord_852519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852519).length < 2 ^ (prefixWord ++ tailWord_852519).sum := by decide
  have hdescent : baseEnd_852519 < baseStart_852519 := by decide
  rcases family_descends (prefixWord ++ tailWord_852519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852530 : List Nat := [3, 2, 1, 1, 2, 1, 4, 3, 4]
def baseStart_852530 : Nat := 118140960795 + 852530 * 2 ^ 59
def prefixEnd_852530 : Nat := 4983230072969 + 3 ^ 40 * 852530 * 2
def baseEnd_852530 : Nat := 194558961056735424957463

theorem tailTrace_852530 : CollatzResearch.WordTrace tailWord_852530 prefixEnd_852530 194558961056735424957463 := by
  unfold tailWord_852530
  simp only [CollatzResearch.WordTrace]
  refine ⟨7773580900359221344314761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20729549067624590251506029 7773580900359221344314761)
  ·
    refine ⟨5830185675269416008236071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7773580900359221344314761 5830185675269416008236071)
    ·
      refine ⟨8745278512904124012354107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5830185675269416008236071 8745278512904124012354107)
      ·
        refine ⟨13117917769356186018531161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8745278512904124012354107 13117917769356186018531161)
        ·
          refine ⟨9838438327017139513898371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13117917769356186018531161 9838438327017139513898371)
          ·
            refine ⟨14757657490525709270847557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9838438327017139513898371 14757657490525709270847557)
            ·
              refine ⟨2767060779473570488283917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14757657490525709270847557 2767060779473570488283917)
              ·
                refine ⟨1037647792302588933106469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2767060779473570488283917 1037647792302588933106469)
                ·
                  refine ⟨194558961056735424957463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1037647792302588933106469 194558961056735424957463)
                  ·
                    rfl

theorem cell21_852530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_852530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_852530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_852530 prefixEnd_852530 := by exact prefixLift 852530
  have htrace : WordTrace (prefixWord ++ tailWord_852530) baseStart_852530 baseEnd_852530 := by
    simpa [prefixWord, tailWord_852530, baseEnd_852530] using wordTrace_append hprefix tailTrace_852530
  have hstable : (prefixWord ++ tailWord_852530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852530).length < 2 ^ (prefixWord ++ tailWord_852530).sum := by decide
  have hdescent : baseEnd_852530 < baseStart_852530 := by decide
  rcases family_descends (prefixWord ++ tailWord_852530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852550 : List Nat := [6, 1, 1, 1, 2, 1, 1, 5, 3]
def baseStart_852550 : Nat := 118140960795 + 852550 * 2 ^ 59
def prefixEnd_852550 : Nat := 4983230072969 + 3 ^ 40 * 852550 * 2
def baseEnd_852550 : Nat := 194563525329219834624089

theorem tailTrace_852550 : CollatzResearch.WordTrace tailWord_852550 prefixEnd_852550 194563525329219834624089 := by
  unfold tailWord_852550
  simp only [CollatzResearch.WordTrace]
  refine ⟨971720408167638399780847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20730035374242952528658069 971720408167638399780847)
  ·
    refine ⟨1457580612251457599671271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 971720408167638399780847 1457580612251457599671271)
    ·
      refine ⟨2186370918377186399506907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1457580612251457599671271 2186370918377186399506907)
      ·
        refine ⟨3279556377565779599260361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2186370918377186399506907 3279556377565779599260361)
        ·
          refine ⟨2459667283174334699445271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3279556377565779599260361 2459667283174334699445271)
          ·
            refine ⟨3689500924761502049167907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2459667283174334699445271 3689500924761502049167907)
            ·
              refine ⟨5534251387142253073751861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3689500924761502049167907 5534251387142253073751861)
              ·
                refine ⟨518836067544586225664237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5534251387142253073751861 518836067544586225664237)
                ·
                  refine ⟨194563525329219834624089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 518836067544586225664237 194563525329219834624089)
                  ·
                    rfl

theorem cell21_852550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_852550 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_852550 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_852550 prefixEnd_852550 := by exact prefixLift 852550
  have htrace : WordTrace (prefixWord ++ tailWord_852550) baseStart_852550 baseEnd_852550 := by
    simpa [prefixWord, tailWord_852550, baseEnd_852550] using wordTrace_append hprefix tailTrace_852550
  have hstable : (prefixWord ++ tailWord_852550).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852550).length < 2 ^ (prefixWord ++ tailWord_852550).sum := by decide
  have hdescent : baseEnd_852550 < baseStart_852550 := by decide
  rcases family_descends (prefixWord ++ tailWord_852550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852626 : List Nat := [3, 2, 3, 1, 2, 2, 3, 2, 3]
def baseStart_852626 : Nat := 118140960795 + 852626 * 2 ^ 59
def prefixEnd_852626 : Nat := 4983230072969 + 3 ^ 40 * 852626 * 2
def baseEnd_852626 : Nat := 194580869564660591357267

theorem tailTrace_852626 : CollatzResearch.WordTrace tailWord_852626 prefixEnd_852626 194580869564660591357267 := by
  unfold tailWord_852626
  simp only [CollatzResearch.WordTrace]
  refine ⟨7774456252272273443188433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20731883339392729181835821 7774456252272273443188433)
  ·
    refine ⟨5830842189204205082391325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7774456252272273443188433 5830842189204205082391325)
    ·
      refine ⟨2186565820951576905896747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5830842189204205082391325 2186565820951576905896747)
      ·
        refine ⟨3279848731427365358845121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2186565820951576905896747 3279848731427365358845121)
        ·
          refine ⟨2459886548570524019133841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3279848731427365358845121 2459886548570524019133841)
          ·
            refine ⟨1844914911427893014350381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2459886548570524019133841 1844914911427893014350381)
            ·
              refine ⟨691843091785459880381393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1844914911427893014350381 691843091785459880381393)
              ·
                refine ⟨518882318839094910286045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 691843091785459880381393 518882318839094910286045)
                ·
                  refine ⟨194580869564660591357267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 518882318839094910286045 194580869564660591357267)
                  ·
                    rfl

theorem cell21_852626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_852626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_852626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_852626 prefixEnd_852626 := by exact prefixLift 852626
  have htrace : WordTrace (prefixWord ++ tailWord_852626) baseStart_852626 baseEnd_852626 := by
    simpa [prefixWord, tailWord_852626, baseEnd_852626] using wordTrace_append hprefix tailTrace_852626
  have hstable : (prefixWord ++ tailWord_852626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852626).length < 2 ^ (prefixWord ++ tailWord_852626).sum := by decide
  have hdescent : baseEnd_852626 < baseStart_852626 := by decide
  rcases family_descends (prefixWord ++ tailWord_852626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852640 : List Nat := [2, 1, 1, 4, 4, 2, 2, 1, 4]
def baseStart_852640 : Nat := 118140960795 + 852640 * 2 ^ 59
def prefixEnd_852640 : Nat := 4983230072969 + 3 ^ 40 * 852640 * 2
def baseEnd_852640 : Nat := 194584064555399678123905

theorem tailTrace_852640 : CollatzResearch.WordTrace tailWord_852640 prefixEnd_852640 194584064555399678123905 := by
  unfold tailWord_852640
  simp only [CollatzResearch.WordTrace]
  refine ⟨15549167815519187081881687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20732223754025582775842249 15549167815519187081881687)
  ·
    refine ⟨23323751723278780622822531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15549167815519187081881687 23323751723278780622822531)
    ·
      refine ⟨34985627584918170934233797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23323751723278780622822531 34985627584918170934233797)
      ·
        refine ⟨6559805172172157050168837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34985627584918170934233797 6559805172172157050168837)
        ·
          refine ⟨1229963469782279446906657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6559805172172157050168837 1229963469782279446906657)
          ·
            refine ⟨922472602336709585179993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1229963469782279446906657 922472602336709585179993)
            ·
              refine ⟨691854451752532188884995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 922472602336709585179993 691854451752532188884995)
              ·
                refine ⟨1037781677628798283327493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 691854451752532188884995 1037781677628798283327493)
                ·
                  refine ⟨194584064555399678123905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1037781677628798283327493 194584064555399678123905)
                  ·
                    rfl

theorem cell21_852640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 4].length) (baseStart_852640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_852640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_852640 prefixEnd_852640 := by exact prefixLift 852640
  have htrace : WordTrace (prefixWord ++ tailWord_852640) baseStart_852640 baseEnd_852640 := by
    simpa [prefixWord, tailWord_852640, baseEnd_852640] using wordTrace_append hprefix tailTrace_852640
  have hstable : (prefixWord ++ tailWord_852640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852640).length < 2 ^ (prefixWord ++ tailWord_852640).sum := by decide
  have hdescent : baseEnd_852640 < baseStart_852640 := by decide
  rcases family_descends (prefixWord ++ tailWord_852640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852668 : List Nat := [2, 2, 2, 3, 1, 1, 2, 5, 3]
def baseStart_852668 : Nat := 118140960795 + 852668 * 2 ^ 59
def prefixEnd_852668 : Nat := 4983230072969 + 3 ^ 40 * 852668 * 2
def baseEnd_852668 : Nat := 194590454536877851657181

theorem tailTrace_852668 : CollatzResearch.WordTrace tailWord_852668 prefixEnd_852668 194590454536877851657181 := by
  unfold tailWord_852668
  simp only [CollatzResearch.WordTrace]
  refine ⟨15549678437468467472891329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20732904583291289963855105 15549678437468467472891329)
  ·
    refine ⟨11662258828101350604668497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15549678437468467472891329 11662258828101350604668497)
    ·
      refine ⟨8746694121076012953501373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11662258828101350604668497 8746694121076012953501373)
      ·
        refine ⟨3280010295403504857563015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8746694121076012953501373 3280010295403504857563015)
        ·
          refine ⟨4920015443105257286344523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3280010295403504857563015 4920015443105257286344523)
          ·
            refine ⟨7380023164657885929516785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4920015443105257286344523 7380023164657885929516785)
            ·
              refine ⟨5535017373493414447137589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7380023164657885929516785 5535017373493414447137589)
              ·
                refine ⟨518907878765007604419149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5535017373493414447137589 518907878765007604419149)
                ·
                  refine ⟨194590454536877851657181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 518907878765007604419149 194590454536877851657181)
                  ·
                    rfl

theorem cell21_852668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 5, 3].length) (baseStart_852668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_852668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_852668 prefixEnd_852668 := by exact prefixLift 852668
  have htrace : WordTrace (prefixWord ++ tailWord_852668) baseStart_852668 baseEnd_852668 := by
    simpa [prefixWord, tailWord_852668, baseEnd_852668] using wordTrace_append hprefix tailTrace_852668
  have hstable : (prefixWord ++ tailWord_852668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852668).length < 2 ^ (prefixWord ++ tailWord_852668).sum := by decide
  have hdescent : baseEnd_852668 < baseStart_852668 := by decide
  rcases family_descends (prefixWord ++ tailWord_852668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852682 : List Nat := [3, 1, 2, 1, 4, 1, 1, 4, 4]
def baseStart_852682 : Nat := 118140960795 + 852682 * 2 ^ 59
def prefixEnd_852682 : Nat := 4983230072969 + 3 ^ 40 * 852682 * 2
def baseEnd_852682 : Nat := 194593649527616938423819

theorem tailTrace_852682 : CollatzResearch.WordTrace tailWord_852682 prefixEnd_852682 194593649527616938423819 := by
  unfold tailWord_852682
  simp only [CollatzResearch.WordTrace]
  refine ⟨7774966874221553834198075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20733244997924143557861533 7774966874221553834198075)
  ·
    refine ⟨11662450311332330751297113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7774966874221553834198075 11662450311332330751297113)
    ·
      refine ⟨8746837733499248063472835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11662450311332330751297113 8746837733499248063472835)
      ·
        refine ⟨13120256600248872095209253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8746837733499248063472835 13120256600248872095209253)
        ·
          refine ⟨2460048112546663517851735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13120256600248872095209253 2460048112546663517851735)
          ·
            refine ⟨3690072168819995276777603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2460048112546663517851735 3690072168819995276777603)
            ·
              refine ⟨5535108253229992915166405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3690072168819995276777603 5535108253229992915166405)
              ·
                refine ⟨1037832797480623671593701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5535108253229992915166405 1037832797480623671593701)
                ·
                  refine ⟨194593649527616938423819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1037832797480623671593701 194593649527616938423819)
                  ·
                    rfl

theorem cell21_852682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_852682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_852682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_852682 prefixEnd_852682 := by exact prefixLift 852682
  have htrace : WordTrace (prefixWord ++ tailWord_852682) baseStart_852682 baseEnd_852682 := by
    simpa [prefixWord, tailWord_852682, baseEnd_852682] using wordTrace_append hprefix tailTrace_852682
  have hstable : (prefixWord ++ tailWord_852682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852682).length < 2 ^ (prefixWord ++ tailWord_852682).sum := by decide
  have hdescent : baseEnd_852682 < baseStart_852682 := by decide
  rcases family_descends (prefixWord ++ tailWord_852682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852696 : List Nat := [2, 1, 2, 2, 3, 2, 3, 6]
def baseStart_852696 : Nat := 118140960795 + 852696 * 2 ^ 59
def prefixEnd_852696 : Nat := 4983230072969 + 3 ^ 40 * 852696 * 2
def baseEnd_852696 : Nat := 64865614839452008396819

theorem tailTrace_852696 : CollatzResearch.WordTrace tailWord_852696 prefixEnd_852696 64865614839452008396819 := by
  unfold tailWord_852696
  simp only [CollatzResearch.WordTrace]
  refine ⟨15550189059417747863900971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20733585412556997151867961 15550189059417747863900971)
  ·
    refine ⟨23325283589126621795851457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15550189059417747863900971 23325283589126621795851457)
    ·
      refine ⟨17493962691844966346888593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23325283589126621795851457 17493962691844966346888593)
      ·
        refine ⟨13120472018883724760166445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17493962691844966346888593 13120472018883724760166445)
        ·
          refine ⟨4920177007081396785062417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13120472018883724760166445 4920177007081396785062417)
          ·
            refine ⟨3690132755311047588796813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4920177007081396785062417 3690132755311047588796813)
            ·
              refine ⟨1383799783241642845798805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3690132755311047588796813 1383799783241642845798805)
              ·
                refine ⟨64865614839452008396819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1383799783241642845798805 64865614839452008396819)
                ·
                  rfl

theorem cell21_852696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 6].length) (baseStart_852696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_852696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_852696 prefixEnd_852696 := by exact prefixLift 852696
  have htrace : WordTrace (prefixWord ++ tailWord_852696) baseStart_852696 baseEnd_852696 := by
    simpa [prefixWord, tailWord_852696, baseEnd_852696] using wordTrace_append hprefix tailTrace_852696
  have hstable : (prefixWord ++ tailWord_852696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852696).length < 2 ^ (prefixWord ++ tailWord_852696).sum := by decide
  have hdescent : baseEnd_852696 < baseStart_852696 := by decide
  rcases family_descends (prefixWord ++ tailWord_852696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852744 : List Nat := [2, 1, 3, 2, 2, 2, 2, 4, 3]
def baseStart_852744 : Nat := 118140960795 + 852744 * 2 ^ 59
def prefixEnd_852744 : Nat := 4983230072969 + 3 ^ 40 * 852744 * 2
def baseEnd_852744 : Nat := 194607798772318608390359

theorem tailTrace_852744 : CollatzResearch.WordTrace tailWord_852744 prefixEnd_852744 194607798772318608390359 := by
  unfold tailWord_852744
  simp only [CollatzResearch.WordTrace]
  refine ⟨15551064411330799962774643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20734752548441066617032857 15551064411330799962774643)
  ·
    refine ⟨23326596616996199944161965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15551064411330799962774643 23326596616996199944161965)
    ·
      refine ⟨8747473731373574979060737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23326596616996199944161965 8747473731373574979060737)
      ·
        refine ⟨6560605298530181234295553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8747473731373574979060737 6560605298530181234295553)
        ·
          refine ⟨4920453973897635925721665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6560605298530181234295553 4920453973897635925721665)
          ·
            refine ⟨3690340480423226944291249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4920453973897635925721665 3690340480423226944291249)
            ·
              refine ⟨2767755360317420208218437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3690340480423226944291249 2767755360317420208218437)
              ·
                refine ⟨518954130059516289040957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2767755360317420208218437 518954130059516289040957)
                ·
                  refine ⟨194607798772318608390359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 518954130059516289040957 194607798772318608390359)
                  ·
                    rfl

theorem cell21_852744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 4, 3].length) (baseStart_852744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_852744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_852744 prefixEnd_852744 := by exact prefixLift 852744
  have htrace : WordTrace (prefixWord ++ tailWord_852744) baseStart_852744 baseEnd_852744 := by
    simpa [prefixWord, tailWord_852744, baseEnd_852744] using wordTrace_append hprefix tailTrace_852744
  have hstable : (prefixWord ++ tailWord_852744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852744).length < 2 ^ (prefixWord ++ tailWord_852744).sum := by decide
  have hdescent : baseEnd_852744 < baseStart_852744 := by decide
  rcases family_descends (prefixWord ++ tailWord_852744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852755 : List Nat := [1, 1, 1, 2, 1, 3, 4, 8]
def baseStart_852755 : Nat := 118140960795 + 852755 * 2 ^ 59
def prefixEnd_852755 : Nat := 4983230072969 + 3 ^ 40 * 852755 * 2
def baseEnd_852755 : Nat := 64870103040728344569001

theorem tailTrace_852755 : CollatzResearch.WordTrace tailWord_852755 prefixEnd_852755 64870103040728344569001 := by
  unfold tailWord_852755
  simp only [CollatzResearch.WordTrace]
  refine ⟨31102530025621748804199719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20735020017081165869466479 31102530025621748804199719)
  ·
    refine ⟨46653795038432623206299579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31102530025621748804199719 46653795038432623206299579)
    ·
      refine ⟨69980692557648934809449369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46653795038432623206299579 69980692557648934809449369)
      ·
        refine ⟨52485519418236701107087027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69980692557648934809449369 52485519418236701107087027)
        ·
          refine ⟨78728279127355051660630541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52485519418236701107087027 78728279127355051660630541)
          ·
            refine ⟨29523104672758144372736453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78728279127355051660630541 29523104672758144372736453)
            ·
              refine ⟨5535582126142152069888085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29523104672758144372736453 5535582126142152069888085)
              ·
                refine ⟨64870103040728344569001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5535582126142152069888085 64870103040728344569001)
                ·
                  rfl

theorem cell21_852755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 8].length) (baseStart_852755 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_852755 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_852755 prefixEnd_852755 := by exact prefixLift 852755
  have htrace : WordTrace (prefixWord ++ tailWord_852755) baseStart_852755 baseEnd_852755 := by
    simpa [prefixWord, tailWord_852755, baseEnd_852755] using wordTrace_append hprefix tailTrace_852755
  have hstable : (prefixWord ++ tailWord_852755).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852755).length < 2 ^ (prefixWord ++ tailWord_852755).sum := by decide
  have hdescent : baseEnd_852755 < baseStart_852755 := by decide
  rcases family_descends (prefixWord ++ tailWord_852755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852831 : List Nat := [1, 1, 2, 3, 1, 3, 1, 9]
def baseStart_852831 : Nat := 118140960795 + 852831 * 2 ^ 59
def prefixEnd_852831 : Nat := 4983230072969 + 3 ^ 40 * 852831 * 2
def baseEnd_852831 : Nat := 64875884452541930146727

theorem tailTrace_852831 : CollatzResearch.WordTrace tailWord_852831 prefixEnd_852831 64875884452541930146727 := by
  unfold tailWord_852831
  simp only [CollatzResearch.WordTrace]
  refine ⟨31105301973346413783966347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20736867982230942522644231 31105301973346413783966347)
  ·
    refine ⟨46657952960019620675949521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31105301973346413783966347 46657952960019620675949521)
    ·
      refine ⟨34993464720014715506962141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46657952960019620675949521 34993464720014715506962141)
      ·
        refine ⟨13122549270005518315110803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34993464720014715506962141 13122549270005518315110803)
        ·
          refine ⟨19683823905008277472666205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13122549270005518315110803 19683823905008277472666205)
          ·
            refine ⟨7381433964378104052249827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19683823905008277472666205 7381433964378104052249827)
            ·
              refine ⟨11072150946567156078374741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7381433964378104052249827 11072150946567156078374741)
              ·
                refine ⟨64875884452541930146727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11072150946567156078374741 64875884452541930146727)
                ·
                  rfl

theorem cell21_852831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 9].length) (baseStart_852831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_852831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_852831 prefixEnd_852831 := by exact prefixLift 852831
  have htrace : WordTrace (prefixWord ++ tailWord_852831) baseStart_852831 baseEnd_852831 := by
    simpa [prefixWord, tailWord_852831, baseEnd_852831] using wordTrace_append hprefix tailTrace_852831
  have hstable : (prefixWord ++ tailWord_852831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852831).length < 2 ^ (prefixWord ++ tailWord_852831).sum := by decide
  have hdescent : baseEnd_852831 < baseStart_852831 := by decide
  rcases family_descends (prefixWord ++ tailWord_852831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852854 : List Nat := [5, 1, 1, 3, 1, 1, 4, 2, 3]
def baseStart_852854 : Nat := 118140960795 + 852854 * 2 ^ 59
def prefixEnd_852854 : Nat := 4983230072969 + 3 ^ 40 * 852854 * 2
def baseEnd_852854 : Nat := 194632902270982861556801

theorem tailTrace_852854 : CollatzResearch.WordTrace tailWord_852854 prefixEnd_852854 194632902270982861556801 := by
  unfold tailWord_852854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1944133803266443044503351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20737427234842059141369077 1944133803266443044503351)
  ·
    refine ⟨2916200704899664566755027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1944133803266443044503351 2916200704899664566755027)
    ·
      refine ⟨4374301057349496850132541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2916200704899664566755027 4374301057349496850132541)
      ·
        refine ⟨1640362896506061318799703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4374301057349496850132541 1640362896506061318799703)
        ·
          refine ⟨2460544344759091978199555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1640362896506061318799703 2460544344759091978199555)
          ·
            refine ⟨3690816517138637967299333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2460544344759091978199555 3690816517138637967299333)
            ·
              refine ⟨692028096963494618868625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3690816517138637967299333 692028096963494618868625)
              ·
                refine ⟨519021072722620964151469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 692028096963494618868625 519021072722620964151469)
                ·
                  refine ⟨194632902270982861556801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 519021072722620964151469 194632902270982861556801)
                  ·
                    rfl

theorem cell21_852854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_852854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_852854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_852854 prefixEnd_852854 := by exact prefixLift 852854
  have htrace : WordTrace (prefixWord ++ tailWord_852854) baseStart_852854 baseEnd_852854 := by
    simpa [prefixWord, tailWord_852854, baseEnd_852854] using wordTrace_append hprefix tailTrace_852854
  have hstable : (prefixWord ++ tailWord_852854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852854).length < 2 ^ (prefixWord ++ tailWord_852854).sum := by decide
  have hdescent : baseEnd_852854 < baseStart_852854 := by decide
  rcases family_descends (prefixWord ++ tailWord_852854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852882 : List Nat := [3, 2, 3, 2, 2, 1, 3, 5]
def baseStart_852882 : Nat := 118140960795 + 852882 * 2 ^ 59
def prefixEnd_852882 : Nat := 4983230072969 + 3 ^ 40 * 852882 * 2
def baseEnd_852882 : Nat := 64879764084153678363359

theorem tailTrace_852882 : CollatzResearch.WordTrace tailWord_852882 prefixEnd_852882 64879764084153678363359 := by
  unfold tailWord_852882
  simp only [CollatzResearch.WordTrace]
  refine ⟨7776790524040412373518225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20738108064107766329381933 7776790524040412373518225)
  ·
    refine ⟨5832592893030309280138669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7776790524040412373518225 5832592893030309280138669)
    ·
      refine ⟨2187222334886365980052001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5832592893030309280138669 2187222334886365980052001)
      ·
        refine ⟨1640416751164774485039001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2187222334886365980052001 1640416751164774485039001)
        ·
          refine ⟨1230312563373580863779251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1640416751164774485039001 1230312563373580863779251)
          ·
            refine ⟨1845468845060371295668877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1230312563373580863779251 1845468845060371295668877)
            ·
              refine ⟨692050816897639235875829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1845468845060371295668877 692050816897639235875829)
              ·
                refine ⟨64879764084153678363359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 692050816897639235875829 64879764084153678363359)
                ·
                  rfl

theorem cell21_852882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 5].length) (baseStart_852882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_852882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_852882 prefixEnd_852882 := by exact prefixLift 852882
  have htrace : WordTrace (prefixWord ++ tailWord_852882) baseStart_852882 baseEnd_852882 := by
    simpa [prefixWord, tailWord_852882, baseEnd_852882] using wordTrace_append hprefix tailTrace_852882
  have hstable : (prefixWord ++ tailWord_852882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852882).length < 2 ^ (prefixWord ++ tailWord_852882).sum := by decide
  have hdescent : baseEnd_852882 < baseStart_852882 := by decide
  rcases family_descends (prefixWord ++ tailWord_852882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852893 : List Nat := [1, 4, 2, 1, 2, 1, 2, 2, 6]
def baseStart_852893 : Nat := 118140960795 + 852893 * 2 ^ 59
def prefixEnd_852893 : Nat := 4983230072969 + 3 ^ 40 * 852893 * 2
def baseEnd_852893 : Nat := 194641802602327460406721

theorem tailTrace_852893 : CollatzResearch.WordTrace tailWord_852893 prefixEnd_852893 194641802602327460406721 := by
  unfold tailWord_852893
  simp only [CollatzResearch.WordTrace]
  refine ⟨31107563299121798372723333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20738375532747865581815555 31107563299121798372723333)
  ·
    refine ⟨5832668118585337194885625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31107563299121798372723333 5832668118585337194885625)
    ·
      refine ⟨4374501088939002896164219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5832668118585337194885625 4374501088939002896164219)
      ·
        refine ⟨6561751633408504344246329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4374501088939002896164219 6561751633408504344246329)
        ·
          refine ⟨4921313725056378258184747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6561751633408504344246329 4921313725056378258184747)
          ·
            refine ⟨7381970587584567387277121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4921313725056378258184747 7381970587584567387277121)
            ·
              refine ⟨5536477940688425540457841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7381970587584567387277121 5536477940688425540457841)
              ·
                refine ⟨4152358455516319155343381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5536477940688425540457841 4152358455516319155343381)
                ·
                  refine ⟨194641802602327460406721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4152358455516319155343381 194641802602327460406721)
                  ·
                    rfl

theorem cell21_852893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_852893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_852893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_852893 prefixEnd_852893 := by exact prefixLift 852893
  have htrace : WordTrace (prefixWord ++ tailWord_852893) baseStart_852893 baseEnd_852893 := by
    simpa [prefixWord, tailWord_852893, baseEnd_852893] using wordTrace_append hprefix tailTrace_852893
  have hstable : (prefixWord ++ tailWord_852893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852893).length < 2 ^ (prefixWord ++ tailWord_852893).sum := by decide
  have hdescent : baseEnd_852893 < baseStart_852893 := by decide
  rcases family_descends (prefixWord ++ tailWord_852893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853034 : List Nat := [3, 1, 4, 1, 4, 1, 1, 6]
def baseStart_853034 : Nat := 118140960795 + 853034 * 2 ^ 59
def prefixEnd_853034 : Nat := 4983230072969 + 3 ^ 40 * 853034 * 2
def baseEnd_853034 : Nat := 64891326907780849518811

theorem tailTrace_853034 : CollatzResearch.WordTrace tailWord_853034 prefixEnd_853034 64891326907780849518811 := by
  unfold tailWord_853034
  simp only [CollatzResearch.WordTrace]
  refine ⟨7778176497902744863401539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20741803994407319635737437 7778176497902744863401539)
  ·
    refine ⟨11667264746854117295102309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7778176497902744863401539 11667264746854117295102309)
    ·
      refine ⟨2187612140035146992831683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11667264746854117295102309 2187612140035146992831683)
      ·
        refine ⟨3281418210052720489247525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2187612140035146992831683 3281418210052720489247525)
        ·
          refine ⟨615265914384885091733911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3281418210052720489247525 615265914384885091733911)
          ·
            refine ⟨922898871577327637600867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615265914384885091733911 922898871577327637600867)
            ·
              refine ⟨1384348307365991456401301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 922898871577327637600867 1384348307365991456401301)
              ·
                refine ⟨64891326907780849518811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1384348307365991456401301 64891326907780849518811)
                ·
                  rfl

theorem cell21_853034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 6].length) (baseStart_853034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_853034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_853034 prefixEnd_853034 := by exact prefixLift 853034
  have htrace : WordTrace (prefixWord ++ tailWord_853034) baseStart_853034 baseEnd_853034 := by
    simpa [prefixWord, tailWord_853034, baseEnd_853034] using wordTrace_append hprefix tailTrace_853034
  have hstable : (prefixWord ++ tailWord_853034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853034).length < 2 ^ (prefixWord ++ tailWord_853034).sum := by decide
  have hdescent : baseEnd_853034 < baseStart_853034 := by decide
  rcases family_descends (prefixWord ++ tailWord_853034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853096 : List Nat := [2, 1, 4, 4, 1, 1, 3, 1, 4]
def baseStart_853096 : Nat := 118140960795 + 853096 * 2 ^ 59
def prefixEnd_853096 : Nat := 4983230072969 + 3 ^ 40 * 853096 * 2
def baseEnd_853096 : Nat := 194688129968044218522973

theorem tailTrace_853096 : CollatzResearch.WordTrace tailWord_853096 prefixEnd_853096 194688129968044218522973 := by
  unfold tailWord_853096
  simp only [CollatzResearch.WordTrace]
  refine ⟨15557483658693182021181571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20743311544924242694908761 15557483658693182021181571)
  ·
    refine ⟨23336225488039773031772357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15557483658693182021181571 23336225488039773031772357)
    ·
      refine ⟨4375542279007457443457317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23336225488039773031772357 4375542279007457443457317)
      ·
        refine ⟨820414177313898270648247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4375542279007457443457317 820414177313898270648247)
        ·
          refine ⟨1230621265970847405972371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 820414177313898270648247 1230621265970847405972371)
          ·
            refine ⟨1845931898956271108958557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1230621265970847405972371 1845931898956271108958557)
            ·
              refine ⟨692224462108601665859459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1845931898956271108958557 692224462108601665859459)
              ·
                refine ⟨1038336693162902498789189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 692224462108601665859459 1038336693162902498789189)
                ·
                  refine ⟨194688129968044218522973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1038336693162902498789189 194688129968044218522973)
                  ·
                    rfl

theorem cell21_853096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 4].length) (baseStart_853096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_853096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_853096 prefixEnd_853096 := by exact prefixLift 853096
  have htrace : WordTrace (prefixWord ++ tailWord_853096) baseStart_853096 baseEnd_853096 := by
    simpa [prefixWord, tailWord_853096, baseEnd_853096] using wordTrace_append hprefix tailTrace_853096
  have hstable : (prefixWord ++ tailWord_853096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853096).length < 2 ^ (prefixWord ++ tailWord_853096).sum := by decide
  have hdescent : baseEnd_853096 < baseStart_853096 := by decide
  rcases family_descends (prefixWord ++ tailWord_853096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853121 : List Nat := [1, 2, 4, 2, 2, 1, 1, 2, 6]
def baseStart_853121 : Nat := 118140960795 + 853121 * 2 ^ 59
def prefixEnd_853121 : Nat := 4983230072969 + 3 ^ 40 * 853121 * 2
def baseEnd_853121 : Nat := 194693835308649730606255

theorem tailTrace_853121 : CollatzResearch.WordTrace tailWord_853121 prefixEnd_853121 194693835308649730606255 := by
  unfold tailWord_853121
  simp only [CollatzResearch.WordTrace]
  refine ⟨31115879142295793312023217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20743919428197195541348811 31115879142295793312023217)
  ·
    refine ⟨23336909356721844984017413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31115879142295793312023217 23336909356721844984017413)
    ·
      refine ⟨4375670504385345934503265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23336909356721844984017413 4375670504385345934503265)
      ·
        refine ⟨3281752878289009450877449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4375670504385345934503265 3281752878289009450877449)
        ·
          refine ⟨2461314658716757088158087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3281752878289009450877449 2461314658716757088158087)
          ·
            refine ⟨3691971988075135632237131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2461314658716757088158087 3691971988075135632237131)
            ·
              refine ⟨5537957982112703448355697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3691971988075135632237131 5537957982112703448355697)
              ·
                refine ⟨4153468486584527586266773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5537957982112703448355697 4153468486584527586266773)
                ·
                  refine ⟨194693835308649730606255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4153468486584527586266773 194693835308649730606255)
                  ·
                    rfl

theorem cell21_853121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 6].length) (baseStart_853121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_853121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_853121 prefixEnd_853121 := by exact prefixLift 853121
  have htrace : WordTrace (prefixWord ++ tailWord_853121) baseStart_853121 baseEnd_853121 := by
    simpa [prefixWord, tailWord_853121, baseEnd_853121] using wordTrace_append hprefix tailTrace_853121
  have hstable : (prefixWord ++ tailWord_853121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853121).length < 2 ^ (prefixWord ++ tailWord_853121).sum := by decide
  have hdescent : baseEnd_853121 < baseStart_853121 := by decide
  rcases family_descends (prefixWord ++ tailWord_853121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853124 : List Nat := [2, 3, 2, 1, 2, 2, 3, 3, 3]
def baseStart_853124 : Nat := 118140960795 + 853124 * 2 ^ 59
def prefixEnd_853124 : Nat := 4983230072969 + 3 ^ 40 * 853124 * 2
def baseEnd_853124 : Nat := 194694519949522392056249

theorem tailTrace_853124 : CollatzResearch.WordTrace tailWord_853124 prefixEnd_853124 194694519949522392056249 := by
  unfold tailWord_853124
  simp only [CollatzResearch.WordTrace]
  refine ⟨15557994280642462412191213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20743992374189949882921617 15557994280642462412191213)
  ·
    refine ⟨5834247855240923404571705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15557994280642462412191213 5834247855240923404571705)
    ·
      refine ⟨4375685891430692553428779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5834247855240923404571705 4375685891430692553428779)
      ·
        refine ⟨6563528837146038830143169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4375685891430692553428779 6563528837146038830143169)
        ·
          refine ⟨4922646627859529122607377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6563528837146038830143169 4922646627859529122607377)
          ·
            refine ⟨3691984970894646841955533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4922646627859529122607377 3691984970894646841955533)
            ·
              refine ⟨1384494364085492565733325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3691984970894646841955533 1384494364085492565733325)
              ·
                refine ⟨519185386532059712149997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1384494364085492565733325 519185386532059712149997)
                ·
                  refine ⟨194694519949522392056249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 519185386532059712149997 194694519949522392056249)
                  ·
                    rfl

theorem cell21_853124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_853124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_853124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_853124 prefixEnd_853124 := by exact prefixLift 853124
  have htrace : WordTrace (prefixWord ++ tailWord_853124) baseStart_853124 baseEnd_853124 := by
    simpa [prefixWord, tailWord_853124, baseEnd_853124] using wordTrace_append hprefix tailTrace_853124
  have hstable : (prefixWord ++ tailWord_853124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853124).length < 2 ^ (prefixWord ++ tailWord_853124).sum := by decide
  have hdescent : baseEnd_853124 < baseStart_853124 := by decide
  rcases family_descends (prefixWord ++ tailWord_853124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853186 : List Nat := [3, 5, 1, 1, 3, 8]
def baseStart_853186 : Nat := 118140960795 + 853186 * 2 ^ 59
def prefixEnd_853186 : Nat := 4983230072969 + 3 ^ 40 * 853186 * 2
def baseEnd_853186 : Nat := 7211432192378668963807

theorem tailTrace_853186 : CollatzResearch.WordTrace tailWord_853186 prefixEnd_853186 7211432192378668963807 := by
  unfold tailWord_853186
  simp only [CollatzResearch.WordTrace]
  refine ⟨7779562471765077353284853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20745499924706872942092941 7779562471765077353284853)
  ·
    refine ⟨729333981727976001870455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7779562471765077353284853 729333981727976001870455)
    ·
      refine ⟨1094000972591964002805683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 729333981727976001870455 1094000972591964002805683)
      ·
        refine ⟨1641001458887946004208525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1094000972591964002805683 1641001458887946004208525)
        ·
          refine ⟨615375547082979751578197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1641001458887946004208525 615375547082979751578197)
          ·
            refine ⟨7211432192378668963807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 615375547082979751578197 7211432192378668963807)
            ·
              rfl

theorem cell21_853186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 8].length) (baseStart_853186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_853186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_853186 prefixEnd_853186 := by exact prefixLift 853186
  have htrace : WordTrace (prefixWord ++ tailWord_853186) baseStart_853186 baseEnd_853186 := by
    simpa [prefixWord, tailWord_853186, baseEnd_853186] using wordTrace_append hprefix tailTrace_853186
  have hstable : (prefixWord ++ tailWord_853186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853186).length < 2 ^ (prefixWord ++ tailWord_853186).sum := by decide
  have hdescent : baseEnd_853186 < baseStart_853186 := by decide
  rcases family_descends (prefixWord ++ tailWord_853186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853228 : List Nat := [2, 2, 1, 1, 2, 5, 3, 5]
def baseStart_853228 : Nat := 118140960795 + 853228 * 2 ^ 59
def prefixEnd_853228 : Nat := 4983230072969 + 3 ^ 40 * 853228 * 2
def baseEnd_853228 : Nat := 64906084722147107440901

theorem tailTrace_853228 : CollatzResearch.WordTrace tailWord_853228 prefixEnd_853228 64906084722147107440901 := by
  unfold tailWord_853228
  simp only [CollatzResearch.WordTrace]
  refine ⟨15559890876454075293084169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20746521168605433724112225 15559890876454075293084169)
  ·
    refine ⟨11669918157340556469813127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15559890876454075293084169 11669918157340556469813127)
    ·
      refine ⟨17504877236010834704719691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11669918157340556469813127 17504877236010834704719691)
      ·
        refine ⟨26257315854016252057079537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17504877236010834704719691 26257315854016252057079537)
        ·
          refine ⟨19692986890512189042809653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26257315854016252057079537 19692986890512189042809653)
          ·
            refine ⟨1846217520985517722763405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19692986890512189042809653 1846217520985517722763405)
            ·
              refine ⟨692331570369569146036277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1846217520985517722763405 692331570369569146036277)
              ·
                refine ⟨64906084722147107440901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 692331570369569146036277 64906084722147107440901)
                ·
                  rfl

theorem cell21_853228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 5].length) (baseStart_853228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_853228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_853228 prefixEnd_853228 := by exact prefixLift 853228
  have htrace : WordTrace (prefixWord ++ tailWord_853228) baseStart_853228 baseEnd_853228 := by
    simpa [prefixWord, tailWord_853228, baseEnd_853228] using wordTrace_append hprefix tailTrace_853228
  have hstable : (prefixWord ++ tailWord_853228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853228).length < 2 ^ (prefixWord ++ tailWord_853228).sum := by decide
  have hdescent : baseEnd_853228 < baseStart_853228 := by decide
  rcases family_descends (prefixWord ++ tailWord_853228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853259 : List Nat := [1, 1, 1, 1, 5, 3, 2, 4, 3]
def baseStart_853259 : Nat := 118140960795 + 853259 * 2 ^ 59
def prefixEnd_853259 : Nat := 4983230072969 + 3 ^ 40 * 853259 * 2
def baseEnd_853259 : Nat := 194725328788792157305973

theorem tailTrace_853259 : CollatzResearch.WordTrace tailWord_853259 prefixEnd_853259 194725328788792157305973 := by
  unfold tailWord_853259
  simp only [CollatzResearch.WordTrace]
  refine ⟨31120912415795842880546831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20747274943863895253697887 31120912415795842880546831)
  ·
    refine ⟨46681368623693764320820247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31120912415795842880546831 46681368623693764320820247)
    ·
      refine ⟨70022052935540646481230371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46681368623693764320820247 70022052935540646481230371)
      ·
        refine ⟨105033079403310969721845557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70022052935540646481230371 105033079403310969721845557)
        ·
          refine ⟨9846851194060403411423021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105033079403310969721845557 9846851194060403411423021)
          ·
            refine ⟨3692569197772651279283633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9846851194060403411423021 3692569197772651279283633)
            ·
              refine ⟨2769426898329488459462725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3692569197772651279283633 2769426898329488459462725)
              ·
                refine ⟨519267543436779086149261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2769426898329488459462725 519267543436779086149261)
                ·
                  refine ⟨194725328788792157305973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 519267543436779086149261 194725328788792157305973)
                  ·
                    rfl

theorem cell21_853259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 4, 3].length) (baseStart_853259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_853259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_853259 prefixEnd_853259 := by exact prefixLift 853259
  have htrace : WordTrace (prefixWord ++ tailWord_853259) baseStart_853259 baseEnd_853259 := by
    simpa [prefixWord, tailWord_853259, baseEnd_853259] using wordTrace_append hprefix tailTrace_853259
  have hstable : (prefixWord ++ tailWord_853259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853259).length < 2 ^ (prefixWord ++ tailWord_853259).sum := by decide
  have hdescent : baseEnd_853259 < baseStart_853259 := by decide
  rcases family_descends (prefixWord ++ tailWord_853259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853293 : List Nat := [1, 5, 3, 1, 1, 1, 3, 3, 3]
def baseStart_853293 : Nat := 118140960795 + 853293 * 2 ^ 59
def prefixEnd_853293 : Nat := 4983230072969 + 3 ^ 40 * 853293 * 2
def baseEnd_853293 : Nat := 194733088052015653739237

theorem tailTrace_853293 : CollatzResearch.WordTrace tailWord_853293 prefixEnd_853293 194733088052015653739237 := by
  unfold tailWord_853293
  simp only [CollatzResearch.WordTrace]
  refine ⟨31122152497672666687284533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20748101665115111124856355 31122152497672666687284533)
  ·
    refine ⟨2917701796656812501932925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31122152497672666687284533 2917701796656812501932925)
    ·
      refine ⟨1094138173746304688224847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2917701796656812501932925 1094138173746304688224847)
      ·
        refine ⟨1641207260619457032337271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1094138173746304688224847 1641207260619457032337271)
        ·
          refine ⟨2461810890929185548505907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1641207260619457032337271 2461810890929185548505907)
          ·
            refine ⟨3692716336393778322758861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2461810890929185548505907 3692716336393778322758861)
            ·
              refine ⟨1384768626147666871034573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3692716336393778322758861 1384768626147666871034573)
              ·
                refine ⟨519288234805375076637965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1384768626147666871034573 519288234805375076637965)
                ·
                  refine ⟨194733088052015653739237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 519288234805375076637965 194733088052015653739237)
                  ·
                    rfl

theorem cell21_853293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_853293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_853293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_853293 prefixEnd_853293 := by exact prefixLift 853293
  have htrace : WordTrace (prefixWord ++ tailWord_853293) baseStart_853293 baseEnd_853293 := by
    simpa [prefixWord, tailWord_853293, baseEnd_853293] using wordTrace_append hprefix tailTrace_853293
  have hstable : (prefixWord ++ tailWord_853293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853293).length < 2 ^ (prefixWord ++ tailWord_853293).sum := by decide
  have hdescent : baseEnd_853293 < baseStart_853293 := by decide
  rcases family_descends (prefixWord ++ tailWord_853293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853380 : List Nat := [2, 3, 2, 1, 1, 5, 1, 6]
def baseStart_853380 : Nat := 118140960795 + 853380 * 2 ^ 59
def prefixEnd_853380 : Nat := 4983230072969 + 3 ^ 40 * 853380 * 2
def baseEnd_853380 : Nat := 64917647545774278596353

theorem tailTrace_853380 : CollatzResearch.WordTrace tailWord_853380 prefixEnd_853380 64917647545774278596353 := by
  unfold tailWord_853380
  simp only [CollatzResearch.WordTrace]
  refine ⟨15562662824178740272850797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20750217098904987030467729 15562662824178740272850797)
  ·
    refine ⟨5835998559067027602319049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15562662824178740272850797 5835998559067027602319049)
    ·
      refine ⟨4376998919300270701739287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5835998559067027602319049 4376998919300270701739287)
      ·
        refine ⟨6565498378950406052608931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4376998919300270701739287 6565498378950406052608931)
        ·
          refine ⟨9848247568425609078913397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6565498378950406052608931 9848247568425609078913397)
          ·
            refine ⟨923273209539900851148131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9848247568425609078913397 923273209539900851148131)
            ·
              refine ⟨1384909814309851276722197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 923273209539900851148131 1384909814309851276722197)
              ·
                refine ⟨64917647545774278596353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1384909814309851276722197 64917647545774278596353)
                ·
                  rfl

theorem cell21_853380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 6].length) (baseStart_853380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_853380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_853380 prefixEnd_853380 := by exact prefixLift 853380
  have htrace : WordTrace (prefixWord ++ tailWord_853380) baseStart_853380 baseEnd_853380 := by
    simpa [prefixWord, tailWord_853380, baseEnd_853380] using wordTrace_append hprefix tailTrace_853380
  have hstable : (prefixWord ++ tailWord_853380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853380).length < 2 ^ (prefixWord ++ tailWord_853380).sum := by decide
  have hdescent : baseEnd_853380 < baseStart_853380 := by decide
  rcases family_descends (prefixWord ++ tailWord_853380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853408 : List Nat := [2, 1, 1, 4, 1, 2, 2, 2, 6]
def baseStart_853408 : Nat := 118140960795 + 853408 * 2 ^ 59
def prefixEnd_853408 : Nat := 4983230072969 + 3 ^ 40 * 853408 * 2
def baseEnd_853408 : Nat := 194759332618801009322335

theorem tailTrace_853408 : CollatzResearch.WordTrace tailWord_853408 prefixEnd_853408 194759332618801009322335 := by
  unfold tailWord_853408
  simp only [CollatzResearch.WordTrace]
  refine ⟨15563173446128020663860439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20750897928170694218480585 15563173446128020663860439)
  ·
    refine ⟨23344760169192030995790659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15563173446128020663860439 23344760169192030995790659)
    ·
      refine ⟨35017140253788046493685989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23344760169192030995790659 35017140253788046493685989)
      ·
        refine ⟨6565713797585258717566123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35017140253788046493685989 6565713797585258717566123)
        ·
          refine ⟨9848570696377888076349185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6565713797585258717566123 9848570696377888076349185)
          ·
            refine ⟨7386428022283416057261889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9848570696377888076349185 7386428022283416057261889)
            ·
              refine ⟨5539821016712562042946417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7386428022283416057261889 5539821016712562042946417)
              ·
                refine ⟨4154865762534421532209813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5539821016712562042946417 4154865762534421532209813)
                ·
                  refine ⟨194759332618801009322335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4154865762534421532209813 194759332618801009322335)
                  ·
                    rfl

theorem cell21_853408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 6].length) (baseStart_853408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_853408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_853408 prefixEnd_853408 := by exact prefixLift 853408
  have htrace : WordTrace (prefixWord ++ tailWord_853408) baseStart_853408 baseEnd_853408 := by
    simpa [prefixWord, tailWord_853408, baseEnd_853408] using wordTrace_append hprefix tailTrace_853408
  have hstable : (prefixWord ++ tailWord_853408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853408).length < 2 ^ (prefixWord ++ tailWord_853408).sum := by decide
  have hdescent : baseEnd_853408 < baseStart_853408 := by decide
  rcases family_descends (prefixWord ++ tailWord_853408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853411 : List Nat := [1, 1, 1, 4, 1, 3, 4, 3, 3]
def baseStart_853411 : Nat := 118140960795 + 853411 * 2 ^ 59
def prefixEnd_853411 : Nat := 4983230072969 + 3 ^ 40 * 853411 * 2
def baseEnd_853411 : Nat := 194760017259673670772329

theorem tailTrace_853411 : CollatzResearch.WordTrace tailWord_853411 prefixEnd_853411 194760017259673670772329 := by
  unfold tailWord_853411
  simp only [CollatzResearch.WordTrace]
  refine ⟨31126456311245172840080087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20750970874163448560053391 31126456311245172840080087)
  ·
    refine ⟨46689684466867759260120131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31126456311245172840080087 46689684466867759260120131)
    ·
      refine ⟨70034526700301638890180197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46689684466867759260120131 70034526700301638890180197)
      ·
        refine ⟨13131473756306557291908787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70034526700301638890180197 13131473756306557291908787)
        ·
          refine ⟨19697210634459835937863181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13131473756306557291908787 19697210634459835937863181)
          ·
            refine ⟨7386453987922438476698693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19697210634459835937863181 7386453987922438476698693)
            ·
              refine ⟨1384960122735457214381005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7386453987922438476698693 1384960122735457214381005)
              ·
                refine ⟨519360046025796455392877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1384960122735457214381005 519360046025796455392877)
                ·
                  refine ⟨194760017259673670772329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 519360046025796455392877 194760017259673670772329)
                  ·
                    rfl

theorem cell21_853411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 3, 3].length) (baseStart_853411 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_853411 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_853411 prefixEnd_853411 := by exact prefixLift 853411
  have htrace : WordTrace (prefixWord ++ tailWord_853411) baseStart_853411 baseEnd_853411 := by
    simpa [prefixWord, tailWord_853411, baseEnd_853411] using wordTrace_append hprefix tailTrace_853411
  have hstable : (prefixWord ++ tailWord_853411).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853411).length < 2 ^ (prefixWord ++ tailWord_853411).sum := by decide
  have hdescent : baseEnd_853411 < baseStart_853411 := by decide
  rcases family_descends (prefixWord ++ tailWord_853411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853501 : List Nat := [1, 4, 1, 1, 1, 5, 1, 3, 4]
def baseStart_853501 : Nat := 118140960795 + 853501 * 2 ^ 59
def prefixEnd_853501 : Nat := 4983230072969 + 3 ^ 40 * 853501 * 2
def baseEnd_853501 : Nat := 194780556485853514272145

theorem tailTrace_853501 : CollatzResearch.WordTrace tailWord_853501 prefixEnd_853501 194780556485853514272145 := by
  unfold tailWord_853501
  simp only [CollatzResearch.WordTrace]
  refine ⟨31129738880919118210856357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20753159253946078807237571 31129738880919118210856357)
  ·
    refine ⟨5836826040172334664535567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31129738880919118210856357 5836826040172334664535567)
    ·
      refine ⟨8755239060258501996803351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5836826040172334664535567 8755239060258501996803351)
      ·
        refine ⟨13132858590387752995205027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8755239060258501996803351 13132858590387752995205027)
        ·
          refine ⟨19699287885581629492807541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13132858590387752995205027 19699287885581629492807541)
          ·
            refine ⟨1846808239273277764950707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19699287885581629492807541 1846808239273277764950707)
            ·
              refine ⟨2770212358909916647426061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1846808239273277764950707 2770212358909916647426061)
              ·
                refine ⟨1038829634591218742784773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2770212358909916647426061 1038829634591218742784773)
                ·
                  refine ⟨194780556485853514272145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1038829634591218742784773 194780556485853514272145)
                  ·
                    rfl

theorem cell21_853501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_853501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_853501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_853501 prefixEnd_853501 := by exact prefixLift 853501
  have htrace : WordTrace (prefixWord ++ tailWord_853501) baseStart_853501 baseEnd_853501 := by
    simpa [prefixWord, tailWord_853501, baseEnd_853501] using wordTrace_append hprefix tailTrace_853501
  have hstable : (prefixWord ++ tailWord_853501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853501).length < 2 ^ (prefixWord ++ tailWord_853501).sum := by decide
  have hdescent : baseEnd_853501 < baseStart_853501 := by decide
  rcases family_descends (prefixWord ++ tailWord_853501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853546 : List Nat := [3, 1, 4, 1, 1, 1, 2, 3, 5]
def baseStart_853546 : Nat := 118140960795 + 853546 * 2 ^ 59
def prefixEnd_853546 : Nat := 4983230072969 + 3 ^ 40 * 853546 * 2
def baseEnd_853546 : Nat := 194790826098943436022053

theorem tailTrace_853546 : CollatzResearch.WordTrace tailWord_853546 prefixEnd_853546 194790826098943436022053 := by
  unfold tailWord_853546
  simp only [CollatzResearch.WordTrace]
  refine ⟨7782845041439022724061123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20754253443837393930829661 7782845041439022724061123)
  ·
    refine ⟨11674267562158534086091685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7782845041439022724061123 11674267562158534086091685)
    ·
      refine ⟨2188925167904725141142191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11674267562158534086091685 2188925167904725141142191)
      ·
        refine ⟨3283387751857087711713287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2188925167904725141142191 3283387751857087711713287)
        ·
          refine ⟨4925081627785631567569931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3283387751857087711713287 4925081627785631567569931)
          ·
            refine ⟨7387622441678447351354897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4925081627785631567569931 7387622441678447351354897)
            ·
              refine ⟨5540716831258835513516173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7387622441678447351354897 5540716831258835513516173)
              ·
                refine ⟨2077768811722063317568565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5540716831258835513516173 2077768811722063317568565)
                ·
                  refine ⟨194790826098943436022053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2077768811722063317568565 194790826098943436022053)
                  ·
                    rfl

theorem cell21_853546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_853546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_853546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_853546 prefixEnd_853546 := by exact prefixLift 853546
  have htrace : WordTrace (prefixWord ++ tailWord_853546) baseStart_853546 baseEnd_853546 := by
    simpa [prefixWord, tailWord_853546, baseEnd_853546] using wordTrace_append hprefix tailTrace_853546
  have hstable : (prefixWord ++ tailWord_853546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853546).length < 2 ^ (prefixWord ++ tailWord_853546).sum := by decide
  have hdescent : baseEnd_853546 < baseStart_853546 := by decide
  rcases family_descends (prefixWord ++ tailWord_853546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853639 : List Nat := [1, 1, 4, 2, 1, 3, 3, 3, 3]
def baseStart_853639 : Nat := 118140960795 + 853639 * 2 ^ 59
def prefixEnd_853639 : Nat := 4983230072969 + 3 ^ 40 * 853639 * 2
def baseEnd_853639 : Nat := 194812049965995940971863

theorem tailTrace_853639 : CollatzResearch.WordTrace tailWord_853639 prefixEnd_853639 194812049965995940971863 := by
  unfold tailWord_853639
  simp only [CollatzResearch.WordTrace]
  refine ⟨31134772154419167779379971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20756514769612778519586647 31134772154419167779379971)
  ·
    refine ⟨46702158231628751669069957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31134772154419167779379971 46702158231628751669069957)
    ·
      refine ⟨8756654668430390937950617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46702158231628751669069957 8756654668430390937950617)
      ·
        refine ⟨6567491001322793203462963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8756654668430390937950617 6567491001322793203462963)
        ·
          refine ⟨9851236501984189805194445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6567491001322793203462963 9851236501984189805194445)
          ·
            refine ⟨3694213688244071176947917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9851236501984189805194445 3694213688244071176947917)
            ·
              refine ⟨1385330133091526691355469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3694213688244071176947917 1385330133091526691355469)
              ·
                refine ⟨519498799909322509258301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1385330133091526691355469 519498799909322509258301)
                ·
                  refine ⟨194812049965995940971863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 519498799909322509258301 194812049965995940971863)
                  ·
                    rfl

theorem cell21_853639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 3, 3].length) (baseStart_853639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_853639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_853639 prefixEnd_853639 := by exact prefixLift 853639
  have htrace : WordTrace (prefixWord ++ tailWord_853639) baseStart_853639 baseEnd_853639 := by
    simpa [prefixWord, tailWord_853639, baseEnd_853639] using wordTrace_append hprefix tailTrace_853639
  have hstable : (prefixWord ++ tailWord_853639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853639).length < 2 ^ (prefixWord ++ tailWord_853639).sum := by decide
  have hdescent : baseEnd_853639 < baseStart_853639 := by decide
  rcases family_descends (prefixWord ++ tailWord_853639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853656 : List Nat := [2, 1, 2, 4, 1, 3, 3, 2, 3]
def baseStart_853656 : Nat := 118140960795 + 853656 * 2 ^ 59
def prefixEnd_853656 : Nat := 4983230072969 + 3 ^ 40 * 853656 * 2
def baseEnd_853656 : Nat := 194815929597607689188495

theorem tailTrace_853656 : CollatzResearch.WordTrace tailWord_853656 prefixEnd_853656 194815929597607689188495 := by
  unfold tailWord_853656
  simp only [CollatzResearch.WordTrace]
  refine ⟨15567696097678789841374411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20756928130238386455165881 15567696097678789841374411)
  ·
    refine ⟨23351544146518184762061617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15567696097678789841374411 23351544146518184762061617)
    ·
      refine ⟨17513658109888638571546213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23351544146518184762061617 17513658109888638571546213)
      ·
        refine ⟨3283810895604119732164915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17513658109888638571546213 3283810895604119732164915)
        ·
          refine ⟨4925716343406179598247373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3283810895604119732164915 4925716343406179598247373)
          ·
            refine ⟨1847143628777317349342765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4925716343406179598247373 1847143628777317349342765)
            ·
              refine ⟨692678860791494006003537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1847143628777317349342765 692678860791494006003537)
              ·
                refine ⟨519509145593620504502653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 692678860791494006003537 519509145593620504502653)
                ·
                  refine ⟨194815929597607689188495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 519509145593620504502653 194815929597607689188495)
                  ·
                    rfl

theorem cell21_853656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 2, 3].length) (baseStart_853656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_853656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_853656 prefixEnd_853656 := by exact prefixLift 853656
  have htrace : WordTrace (prefixWord ++ tailWord_853656) baseStart_853656 baseEnd_853656 := by
    simpa [prefixWord, tailWord_853656, baseEnd_853656] using wordTrace_append hprefix tailTrace_853656
  have hstable : (prefixWord ++ tailWord_853656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853656).length < 2 ^ (prefixWord ++ tailWord_853656).sum := by decide
  have hdescent : baseEnd_853656 < baseStart_853656 := by decide
  rcases family_descends (prefixWord ++ tailWord_853656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853718 : List Nat := [5, 2, 1, 3, 1, 2, 1, 6]
def baseStart_853718 : Nat := 118140960795 + 853718 * 2 ^ 59
def prefixEnd_853718 : Nat := 4983230072969 + 3 ^ 40 * 853718 * 2
def baseEnd_853718 : Nat := 64943359614103119718345

theorem tailTrace_853718 : CollatzResearch.WordTrace tailWord_853718 prefixEnd_853718 64943359614103119718345 := by
  unfold tailWord_853718
  simp only [CollatzResearch.WordTrace]
  refine ⟨1946103345070810266969113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20758435680755309514337205 1946103345070810266969113)
  ·
    refine ⟨1459577508803107700226835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1946103345070810266969113 1459577508803107700226835)
    ·
      refine ⟨2189366263204661550340253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1459577508803107700226835 2189366263204661550340253)
      ·
        refine ⟨821012348701748081377595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2189366263204661550340253 821012348701748081377595)
        ·
          refine ⟨1231518523052622122066393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 821012348701748081377595 1231518523052622122066393)
          ·
            refine ⟨923638892289466591549795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1231518523052622122066393 923638892289466591549795)
            ·
              refine ⟨1385458338434199887324693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 923638892289466591549795 1385458338434199887324693)
              ·
                refine ⟨64943359614103119718345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1385458338434199887324693 64943359614103119718345)
                ·
                  rfl

theorem cell21_853718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_853718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_853718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_853718 prefixEnd_853718 := by exact prefixLift 853718
  have htrace : WordTrace (prefixWord ++ tailWord_853718) baseStart_853718 baseEnd_853718 := by
    simpa [prefixWord, tailWord_853718, baseEnd_853718] using wordTrace_append hprefix tailTrace_853718
  have hstable : (prefixWord ++ tailWord_853718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853718).length < 2 ^ (prefixWord ++ tailWord_853718).sum := by decide
  have hdescent : baseEnd_853718 < baseStart_853718 := by decide
  rcases family_descends (prefixWord ++ tailWord_853718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853743 : List Nat := [1, 1, 2, 1, 5, 1, 5, 5]
def baseStart_853743 : Nat := 118140960795 + 853743 * 2 ^ 59
def prefixEnd_853743 : Nat := 4983230072969 + 3 ^ 40 * 853743 * 2
def baseEnd_853743 : Nat := 64945261394304957079439

theorem tailTrace_853743 : CollatzResearch.WordTrace tailWord_853743 prefixEnd_853743 64945261394304957079439 := by
  unfold tailWord_853743
  simp only [CollatzResearch.WordTrace]
  refine ⟨31138565346042393541165883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20759043564028262360777255 31138565346042393541165883)
  ·
    refine ⟨46707848019063590311748825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31138565346042393541165883 46707848019063590311748825)
    ·
      refine ⟨35030886014297692733811619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46707848019063590311748825 35030886014297692733811619)
      ·
        refine ⟨52546329021446539100717429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35030886014297692733811619 52546329021446539100717429)
        ·
          refine ⟨4926218345760613040692259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52546329021446539100717429 4926218345760613040692259)
          ·
            refine ⟨7389327518640919561038389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4926218345760613040692259 7389327518640919561038389)
            ·
              refine ⟨692749454872586208847349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7389327518640919561038389 692749454872586208847349)
              ·
                refine ⟨64945261394304957079439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 692749454872586208847349 64945261394304957079439)
                ·
                  rfl

theorem cell21_853743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 5].length) (baseStart_853743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_853743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_853743 prefixEnd_853743 := by exact prefixLift 853743
  have htrace : WordTrace (prefixWord ++ tailWord_853743) baseStart_853743 baseEnd_853743 := by
    simpa [prefixWord, tailWord_853743, baseEnd_853743] using wordTrace_append hprefix tailTrace_853743
  have hstable : (prefixWord ++ tailWord_853743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853743).length < 2 ^ (prefixWord ++ tailWord_853743).sum := by decide
  have hdescent : baseEnd_853743 < baseStart_853743 := by decide
  rcases family_descends (prefixWord ++ tailWord_853743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853909 : List Nat := [1, 3, 2, 1, 1, 3, 3, 2, 5]
def baseStart_853909 : Nat := 118140960795 + 853909 * 2 ^ 59
def prefixEnd_853909 : Nat := 4983230072969 + 3 ^ 40 * 853909 * 2
def baseEnd_853909 : Nat := 194873667644535471471311

theorem tailTrace_853909 : CollatzResearch.WordTrace tailWord_853909 prefixEnd_853909 194873667644535471471311 := by
  unfold tailWord_853909
  simp only [CollatzResearch.WordTrace]
  refine ⟨31144619863441003891708781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20763079908960669261139187 31144619863441003891708781)
  ·
    refine ⟨11679232448790376459390793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31144619863441003891708781 11679232448790376459390793)
    ·
      refine ⟨8759424336592782344543095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11679232448790376459390793 8759424336592782344543095)
      ·
        refine ⟨13139136504889173516814643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8759424336592782344543095 13139136504889173516814643)
        ·
          refine ⟨19708704757333760275221965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13139136504889173516814643 19708704757333760275221965)
          ·
            refine ⟨7390764284000160103208237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19708704757333760275221965 7390764284000160103208237)
            ·
              refine ⟨2771536606500060038703089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7390764284000160103208237 2771536606500060038703089)
              ·
                refine ⟨2078652454875045029027317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2771536606500060038703089 2078652454875045029027317)
                ·
                  refine ⟨194873667644535471471311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2078652454875045029027317 194873667644535471471311)
                  ·
                    rfl

theorem cell21_853909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_853909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_853909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_853909 prefixEnd_853909 := by exact prefixLift 853909
  have htrace : WordTrace (prefixWord ++ tailWord_853909) baseStart_853909 baseEnd_853909 := by
    simpa [prefixWord, tailWord_853909, baseEnd_853909] using wordTrace_append hprefix tailTrace_853909
  have hstable : (prefixWord ++ tailWord_853909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853909).length < 2 ^ (prefixWord ++ tailWord_853909).sum := by decide
  have hdescent : baseEnd_853909 < baseStart_853909 := by decide
  rcases family_descends (prefixWord ++ tailWord_853909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853923 : List Nat := [1, 1, 1, 4, 1, 2, 1, 4, 6]
def baseStart_853923 : Nat := 118140960795 + 853923 * 2 ^ 59
def prefixEnd_853923 : Nat := 4983230072969 + 3 ^ 40 * 853923 * 2
def baseEnd_853923 : Nat := 194876862635274558237949

theorem tailTrace_853923 : CollatzResearch.WordTrace tailWord_853923 prefixEnd_853923 194876862635274558237949 := by
  unfold tailWord_853923
  simp only [CollatzResearch.WordTrace]
  refine ⟨31145130485390284282718423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20763420323593522855145615 31145130485390284282718423)
  ·
    refine ⟨46717695728085426424077635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31145130485390284282718423 46717695728085426424077635)
    ·
      refine ⟨70076543592128139636116453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46717695728085426424077635 70076543592128139636116453)
      ·
        refine ⟨13139351923524026181771835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70076543592128139636116453 13139351923524026181771835)
        ·
          refine ⟨19709027885286039272657753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13139351923524026181771835 19709027885286039272657753)
          ·
            refine ⟨14781770913964529454493315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19709027885286039272657753 14781770913964529454493315)
            ·
              refine ⟨22172656370946794181739973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14781770913964529454493315 22172656370946794181739973)
              ·
                refine ⟨4157373069552523909076245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22172656370946794181739973 4157373069552523909076245)
                ·
                  refine ⟨194876862635274558237949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4157373069552523909076245 194876862635274558237949)
                  ·
                    rfl

theorem cell21_853923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 6].length) (baseStart_853923 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_853923 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_853923 prefixEnd_853923 := by exact prefixLift 853923
  have htrace : WordTrace (prefixWord ++ tailWord_853923) baseStart_853923 baseEnd_853923 := by
    simpa [prefixWord, tailWord_853923, baseEnd_853923] using wordTrace_append hprefix tailTrace_853923
  have hstable : (prefixWord ++ tailWord_853923).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853923).length < 2 ^ (prefixWord ++ tailWord_853923).sum := by decide
  have hdescent : baseEnd_853923 < baseStart_853923 := by decide
  rcases family_descends (prefixWord ++ tailWord_853923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853999 : List Nat := [1, 1, 2, 1, 4, 2, 1, 3, 6]
def baseStart_853999 : Nat := 118140960795 + 853999 * 2 ^ 59
def prefixEnd_853999 : Nat := 4983230072969 + 3 ^ 40 * 853999 * 2
def baseEnd_853999 : Nat := 194894206870715314971127

theorem tailTrace_853999 : CollatzResearch.WordTrace tailWord_853999 prefixEnd_853999 194894206870715314971127 := by
  unfold tailWord_853999
  simp only [CollatzResearch.WordTrace]
  refine ⟨31147902433114949262485051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20765268288743299508323367 31147902433114949262485051)
  ·
    refine ⟨46721853649672423893727577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31147902433114949262485051 46721853649672423893727577)
    ·
      refine ⟨35041390237254317920295683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46721853649672423893727577 35041390237254317920295683)
      ·
        refine ⟨52562085355881476880443525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35041390237254317920295683 52562085355881476880443525)
        ·
          refine ⟨9855391004227776915083161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52562085355881476880443525 9855391004227776915083161)
          ·
            refine ⟨7391543253170832686312371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9855391004227776915083161 7391543253170832686312371)
            ·
              refine ⟨11087314879756249029468557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7391543253170832686312371 11087314879756249029468557)
              ·
                refine ⟨4157743079908593386050709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11087314879756249029468557 4157743079908593386050709)
                ·
                  refine ⟨194894206870715314971127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4157743079908593386050709 194894206870715314971127)
                  ·
                    rfl

theorem cell21_853999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 6].length) (baseStart_853999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_853999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_853999 prefixEnd_853999 := by exact prefixLift 853999
  have htrace : WordTrace (prefixWord ++ tailWord_853999) baseStart_853999 baseEnd_853999 := by
    simpa [prefixWord, tailWord_853999, baseEnd_853999] using wordTrace_append hprefix tailTrace_853999
  have hstable : (prefixWord ++ tailWord_853999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853999).length < 2 ^ (prefixWord ++ tailWord_853999).sum := by decide
  have hdescent : baseEnd_853999 < baseStart_853999 := by decide
  rcases family_descends (prefixWord ++ tailWord_853999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854030 : List Nat := [4, 1, 1, 2, 2, 1, 1, 9]
def baseStart_854030 : Nat := 118140960795 + 854030 * 2 ^ 59
def prefixEnd_854030 : Nat := 4983230072969 + 3 ^ 40 * 854030 * 2
def baseEnd_854030 : Nat := 64967093831022049984799

theorem tailTrace_854030 : CollatzResearch.WordTrace tailWord_854030 prefixEnd_854030 64967093831022049984799 := by
  unfold tailWord_854030
  simp only [CollatzResearch.WordTrace]
  refine ⟨3893629137000330194607943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20766022064001761037909029 3893629137000330194607943)
  ·
    refine ⟨5840443705500495291911915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3893629137000330194607943 5840443705500495291911915)
    ·
      refine ⟨8760665558250742937867873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5840443705500495291911915 8760665558250742937867873)
      ·
        refine ⟨6570499168688057203400905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8760665558250742937867873 6570499168688057203400905)
        ·
          refine ⟨4927874376516042902550679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6570499168688057203400905 4927874376516042902550679)
          ·
            refine ⟨7391811564774064353826019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4927874376516042902550679 7391811564774064353826019)
            ·
              refine ⟨11087717347161096530739029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7391811564774064353826019 11087717347161096530739029)
              ·
                refine ⟨64967093831022049984799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11087717347161096530739029 64967093831022049984799)
                ·
                  rfl

theorem cell21_854030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_854030 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_854030 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_854030 prefixEnd_854030 := by exact prefixLift 854030
  have htrace : WordTrace (prefixWord ++ tailWord_854030) baseStart_854030 baseEnd_854030 := by
    simpa [prefixWord, tailWord_854030, baseEnd_854030] using wordTrace_append hprefix tailTrace_854030
  have hstable : (prefixWord ++ tailWord_854030).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854030).length < 2 ^ (prefixWord ++ tailWord_854030).sum := by decide
  have hdescent : baseEnd_854030 < baseStart_854030 := by decide
  rcases family_descends (prefixWord ++ tailWord_854030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854109 : List Nat := [1, 4, 4, 1, 1, 2, 1, 1, 6]
def baseStart_854109 : Nat := 118140960795 + 854109 * 2 ^ 59
def prefixEnd_854109 : Nat := 4983230072969 + 3 ^ 40 * 854109 * 2
def baseEnd_854109 : Nat := 194919310369379568137569

theorem tailTrace_854109 : CollatzResearch.WordTrace tailWord_854109 prefixEnd_854109 194919310369379568137569 := by
  unfold tailWord_854109
  simp only [CollatzResearch.WordTrace]
  refine ⟨31151914462716438048989381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20767942975144292032659587 31151914462716438048989381)
  ·
    refine ⟨5840983961759332134185509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31151914462716438048989381 5840983961759332134185509)
    ·
      refine ⟨1095184492829874775159783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5840983961759332134185509 1095184492829874775159783)
      ·
        refine ⟨1642776739244812162739675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1095184492829874775159783 1642776739244812162739675)
        ·
          refine ⟨2464165108867218244109513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1642776739244812162739675 2464165108867218244109513)
          ·
            refine ⟨1848123831650413683082135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2464165108867218244109513 1848123831650413683082135)
            ·
              refine ⟨2772185747475620524623203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1848123831650413683082135 2772185747475620524623203)
              ·
                refine ⟨4158278621213430786934805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2772185747475620524623203 4158278621213430786934805)
                ·
                  refine ⟨194919310369379568137569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4158278621213430786934805 194919310369379568137569)
                  ·
                    rfl

theorem cell21_854109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_854109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_854109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_854109 prefixEnd_854109 := by exact prefixLift 854109
  have htrace : WordTrace (prefixWord ++ tailWord_854109) baseStart_854109 baseEnd_854109 := by
    simpa [prefixWord, tailWord_854109, baseEnd_854109] using wordTrace_append hprefix tailTrace_854109
  have hstable : (prefixWord ++ tailWord_854109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854109).length < 2 ^ (prefixWord ++ tailWord_854109).sum := by decide
  have hdescent : baseEnd_854109 < baseStart_854109 := by decide
  rcases family_descends (prefixWord ++ tailWord_854109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854137 : List Nat := [1, 2, 1, 3, 4, 1, 2, 2, 5]
def baseStart_854137 : Nat := 118140960795 + 854137 * 2 ^ 59
def prefixEnd_854137 : Nat := 4983230072969 + 3 ^ 40 * 854137 * 2
def baseEnd_854137 : Nat := 194925700350857741670845

theorem tailTrace_854137 : CollatzResearch.WordTrace tailWord_854137 prefixEnd_854137 194925700350857741670845 := by
  unfold tailWord_854137
  simp only [CollatzResearch.WordTrace]
  refine ⟨31152935706614998831008665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20768623804409999220672443 31152935706614998831008665)
  ·
    refine ⟨23364701779961249123256499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31152935706614998831008665 23364701779961249123256499)
    ·
      refine ⟨35047052669941873684884749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23364701779961249123256499 35047052669941873684884749)
      ·
        refine ⟨13142644751228202631831781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35047052669941873684884749 13142644751228202631831781)
        ·
          refine ⟨2464245890855287993468459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13142644751228202631831781 2464245890855287993468459)
          ·
            refine ⟨3696368836282931990202689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2464245890855287993468459 3696368836282931990202689)
            ·
              refine ⟨2772276627212198992652017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3696368836282931990202689 2772276627212198992652017)
              ·
                refine ⟨2079207470409149244489013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2772276627212198992652017 2079207470409149244489013)
                ·
                  refine ⟨194925700350857741670845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2079207470409149244489013 194925700350857741670845)
                  ·
                    rfl

theorem cell21_854137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 5].length) (baseStart_854137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_854137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_854137 prefixEnd_854137 := by exact prefixLift 854137
  have htrace : WordTrace (prefixWord ++ tailWord_854137) baseStart_854137 baseEnd_854137 := by
    simpa [prefixWord, tailWord_854137, baseEnd_854137] using wordTrace_append hprefix tailTrace_854137
  have hstable : (prefixWord ++ tailWord_854137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854137).length < 2 ^ (prefixWord ++ tailWord_854137).sum := by decide
  have hdescent : baseEnd_854137 < baseStart_854137 := by decide
  rcases family_descends (prefixWord ++ tailWord_854137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854151 : List Nat := [1, 1, 4, 2, 1, 1, 3, 2, 6]
def baseStart_854151 : Nat := 118140960795 + 854151 * 2 ^ 59
def prefixEnd_854151 : Nat := 4983230072969 + 3 ^ 40 * 854151 * 2
def baseEnd_854151 : Nat := 194928895341596828437483

theorem tailTrace_854151 : CollatzResearch.WordTrace tailWord_854151 prefixEnd_854151 194928895341596828437483 := by
  unfold tailWord_854151
  simp only [CollatzResearch.WordTrace]
  refine ⟨31153446328564279222018307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20768964219042852814678871 31153446328564279222018307)
  ·
    refine ⟨46730169492846418833027461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31153446328564279222018307 46730169492846418833027461)
    ·
      refine ⟨8761906779908703531192649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46730169492846418833027461 8761906779908703531192649)
      ·
        refine ⟨6571430084931527648394487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8761906779908703531192649 6571430084931527648394487)
        ·
          refine ⟨9857145127397291472591731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6571430084931527648394487 9857145127397291472591731)
          ·
            refine ⟨14785717691095937208887597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9857145127397291472591731 14785717691095937208887597)
            ·
              refine ⟨5544644134160976453332849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14785717691095937208887597 5544644134160976453332849)
              ·
                refine ⟨4158483100620732339999637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5544644134160976453332849 4158483100620732339999637)
                ·
                  refine ⟨194928895341596828437483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4158483100620732339999637 194928895341596828437483)
                  ·
                    rfl

theorem cell21_854151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 6].length) (baseStart_854151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_854151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_854151 prefixEnd_854151 := by exact prefixLift 854151
  have htrace : WordTrace (prefixWord ++ tailWord_854151) baseStart_854151 baseEnd_854151 := by
    simpa [prefixWord, tailWord_854151, baseEnd_854151] using wordTrace_append hprefix tailTrace_854151
  have hstable : (prefixWord ++ tailWord_854151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854151).length < 2 ^ (prefixWord ++ tailWord_854151).sum := by decide
  have hdescent : baseEnd_854151 < baseStart_854151 := by decide
  rcases family_descends (prefixWord ++ tailWord_854151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854289 : List Nat := [1, 2, 2, 1, 1, 6, 2, 1, 5]
def baseStart_854289 : Nat := 118140960795 + 854289 * 2 ^ 59
def prefixEnd_854289 : Nat := 4983230072969 + 3 ^ 40 * 854289 * 2
def baseEnd_854289 : Nat := 194960388821739255137201

theorem tailTrace_854289 : CollatzResearch.WordTrace tailWord_854289 prefixEnd_854289 194960388821739255137201 := by
  unfold tailWord_854289
  simp only [CollatzResearch.WordTrace]
  refine ⟨31158479602064328790541921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20772319734709552527027947 31158479602064328790541921)
  ·
    refine ⟨23368859701548246592906441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31158479602064328790541921 23368859701548246592906441)
    ·
      refine ⟨17526644776161184944679831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23368859701548246592906441 17526644776161184944679831)
      ·
        refine ⟨26289967164241777417019747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17526644776161184944679831 26289967164241777417019747)
        ·
          refine ⟨39434950746362666125529621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26289967164241777417019747 39434950746362666125529621)
          ·
            refine ⟨1848513316235749974634201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 39434950746362666125529621 1848513316235749974634201)
            ·
              refine ⟨1386384987176812480975651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1848513316235749974634201 1386384987176812480975651)
              ·
                refine ⟨2079577480765218721463477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1386384987176812480975651 2079577480765218721463477)
                ·
                  refine ⟨194960388821739255137201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2079577480765218721463477 194960388821739255137201)
                  ·
                    rfl

theorem cell21_854289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 5].length) (baseStart_854289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_854289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_854289 prefixEnd_854289 := by exact prefixLift 854289
  have htrace : WordTrace (prefixWord ++ tailWord_854289) baseStart_854289 baseEnd_854289 := by
    simpa [prefixWord, tailWord_854289, baseEnd_854289] using wordTrace_append hprefix tailTrace_854289
  have hstable : (prefixWord ++ tailWord_854289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854289).length < 2 ^ (prefixWord ++ tailWord_854289).sum := by decide
  have hdescent : baseEnd_854289 < baseStart_854289 := by decide
  rcases family_descends (prefixWord ++ tailWord_854289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854334 : List Nat := [4, 2, 1, 2, 1, 2, 9]
def baseStart_854334 : Nat := 118140960795 + 854334 * 2 ^ 59
def prefixEnd_854334 : Nat := 4983230072969 + 3 ^ 40 * 854334 * 2
def baseEnd_854334 : Nat := 21663406492758797431901

theorem tailTrace_854334 : CollatzResearch.WordTrace tailWord_854334 prefixEnd_854334 21663406492758797431901 := by
  unfold tailWord_854334
  simp only [CollatzResearch.WordTrace]
  refine ⟨3895015110862662684491257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20773413924600867650620037 3895015110862662684491257)
  ·
    refine ⟨2921261333146997013368443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3895015110862662684491257 2921261333146997013368443)
    ·
      refine ⟨4381891999720495520052665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2921261333146997013368443 4381891999720495520052665)
      ·
        refine ⟨3286418999790371640039499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4381891999720495520052665 3286418999790371640039499)
        ·
          refine ⟨4929628499685557460059249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3286418999790371640039499 4929628499685557460059249)
          ·
            refine ⟨3697221374764168095044437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4929628499685557460059249 3697221374764168095044437)
            ·
              refine ⟨21663406492758797431901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3697221374764168095044437 21663406492758797431901)
              ·
                rfl

theorem cell21_854334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 9].length) (baseStart_854334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_854334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_854334 prefixEnd_854334 := by exact prefixLift 854334
  have htrace : WordTrace (prefixWord ++ tailWord_854334) baseStart_854334 baseEnd_854334 := by
    simpa [prefixWord, tailWord_854334, baseEnd_854334] using wordTrace_append hprefix tailTrace_854334
  have hstable : (prefixWord ++ tailWord_854334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854334).length < 2 ^ (prefixWord ++ tailWord_854334).sum := by decide
  have hdescent : baseEnd_854334 < baseStart_854334 := by decide
  rcases family_descends (prefixWord ++ tailWord_854334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854340 : List Nat := [2, 3, 4, 1, 3, 1, 1, 1, 5]
def baseStart_854340 : Nat := 118140960795 + 854340 * 2 ^ 59
def prefixEnd_854340 : Nat := 4983230072969 + 3 ^ 40 * 854340 * 2
def baseEnd_854340 : Nat := 194972027716574499787097

theorem tailTrace_854340 : CollatzResearch.WordTrace tailWord_854340 prefixEnd_854340 194972027716574499787097 := by
  unfold tailWord_854340
  simp only [CollatzResearch.WordTrace]
  refine ⟨15580169862439782250324237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20773559816586376333765649 15580169862439782250324237)
  ·
    refine ⟨5842563698414918343871589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15580169862439782250324237 5842563698414918343871589)
    ·
      refine ⟨1095480693452797189475923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5842563698414918343871589 1095480693452797189475923)
      ·
        refine ⟨1643221040179195784213885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1095480693452797189475923 1643221040179195784213885)
        ·
          refine ⟨616207890067198419080207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1643221040179195784213885 616207890067198419080207)
          ·
            refine ⟨924311835100797628620311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616207890067198419080207 924311835100797628620311)
            ·
              refine ⟨1386467752651196442930467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 924311835100797628620311 1386467752651196442930467)
              ·
                refine ⟨2079701628976794664395701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1386467752651196442930467 2079701628976794664395701)
                ·
                  refine ⟨194972027716574499787097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2079701628976794664395701 194972027716574499787097)
                  ·
                    rfl

theorem cell21_854340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_854340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_854340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_854340 prefixEnd_854340 := by exact prefixLift 854340
  have htrace : WordTrace (prefixWord ++ tailWord_854340) baseStart_854340 baseEnd_854340 := by
    simpa [prefixWord, tailWord_854340, baseEnd_854340] using wordTrace_append hprefix tailTrace_854340
  have hstable : (prefixWord ++ tailWord_854340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854340).length < 2 ^ (prefixWord ++ tailWord_854340).sum := by decide
  have hdescent : baseEnd_854340 < baseStart_854340 := by decide
  rcases family_descends (prefixWord ++ tailWord_854340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854455 : List Nat := [1, 1, 3, 1, 3, 4, 1, 1, 6]
def baseStart_854455 : Nat := 118140960795 + 854455 * 2 ^ 59
def prefixEnd_854455 : Nat := 4983230072969 + 3 ^ 40 * 854455 * 2
def baseEnd_854455 : Nat := 194998272283359855370195

theorem tailTrace_854455 : CollatzResearch.WordTrace tailWord_854455 prefixEnd_854455 194998272283359855370195 := by
  unfold tailWord_854455
  simp only [CollatzResearch.WordTrace]
  refine ⟨31164534119462939141084819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20776356079641959427389879 31164534119462939141084819)
  ·
    refine ⟨46746801179194408711627229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31164534119462939141084819 46746801179194408711627229)
    ·
      refine ⟨17530050442197903266860211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46746801179194408711627229 17530050442197903266860211)
      ·
        refine ⟨26295075663296854900290317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17530050442197903266860211 26295075663296854900290317)
        ·
          refine ⟨9860653373736320587608869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26295075663296854900290317 9860653373736320587608869)
          ·
            refine ⟨1848872507575560110176663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9860653373736320587608869 1848872507575560110176663)
            ·
              refine ⟨2773308761363340165264995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1848872507575560110176663 2773308761363340165264995)
              ·
                refine ⟨4159963142045010247897493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2773308761363340165264995 4159963142045010247897493)
                ·
                  refine ⟨194998272283359855370195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4159963142045010247897493 194998272283359855370195)
                  ·
                    rfl

theorem cell21_854455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 6].length) (baseStart_854455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_854455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_854455 prefixEnd_854455 := by exact prefixLift 854455
  have htrace : WordTrace (prefixWord ++ tailWord_854455) baseStart_854455 baseEnd_854455 := by
    simpa [prefixWord, tailWord_854455, baseEnd_854455] using wordTrace_append hprefix tailTrace_854455
  have hstable : (prefixWord ++ tailWord_854455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854455).length < 2 ^ (prefixWord ++ tailWord_854455).sum := by decide
  have hdescent : baseEnd_854455 < baseStart_854455 := by decide
  rcases family_descends (prefixWord ++ tailWord_854455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854531 : List Nat := [1, 1, 1, 3, 2, 1, 5, 3, 4]
def baseStart_854531 : Nat := 118140960795 + 854531 * 2 ^ 59
def prefixEnd_854531 : Nat := 4983230072969 + 3 ^ 40 * 854531 * 2
def baseEnd_854531 : Nat := 195015616518800612103373

theorem tailTrace_854531 : CollatzResearch.WordTrace tailWord_854531 prefixEnd_854531 195015616518800612103373 := by
  unfold tailWord_854531
  simp only [CollatzResearch.WordTrace]
  refine ⟨31167306067187604120851447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20778204044791736080567631 31167306067187604120851447)
  ·
    refine ⟨46750959100781406181277171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31167306067187604120851447 46750959100781406181277171)
    ·
      refine ⟨70126438651172109271915757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46750959100781406181277171 70126438651172109271915757)
      ·
        refine ⟨26297414494189540976968409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70126438651172109271915757 26297414494189540976968409)
        ·
          refine ⟨19723060870642155732726307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26297414494189540976968409 19723060870642155732726307)
          ·
            refine ⟨29584591305963233599089461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19723060870642155732726307 29584591305963233599089461)
            ·
              refine ⟨2773555434934053149914637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29584591305963233599089461 2773555434934053149914637)
              ·
                refine ⟨1040083288100269931217989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2773555434934053149914637 1040083288100269931217989)
                ·
                  refine ⟨195015616518800612103373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1040083288100269931217989 195015616518800612103373)
                  ·
                    rfl

theorem cell21_854531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 4].length) (baseStart_854531 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_854531 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_854531 prefixEnd_854531 := by exact prefixLift 854531
  have htrace : WordTrace (prefixWord ++ tailWord_854531) baseStart_854531 baseEnd_854531 := by
    simpa [prefixWord, tailWord_854531, baseEnd_854531] using wordTrace_append hprefix tailTrace_854531
  have hstable : (prefixWord ++ tailWord_854531).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854531).length < 2 ^ (prefixWord ++ tailWord_854531).sum := by decide
  have hdescent : baseEnd_854531 < baseStart_854531 := by decide
  rcases family_descends (prefixWord ++ tailWord_854531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854568 : List Nat := [2, 1, 5, 2, 1, 3, 2, 2, 3]
def baseStart_854568 : Nat := 118140960795 + 854568 * 2 ^ 59
def prefixEnd_854568 : Nat := 4983230072969 + 3 ^ 40 * 854568 * 2
def baseEnd_854568 : Nat := 195024060422896769986631

theorem tailTrace_854568 : CollatzResearch.WordTrace tailWord_854568 prefixEnd_854568 195024060422896769986631 := by
  unfold tailWord_854568
  simp only [CollatzResearch.WordTrace]
  refine ⟨15584327784026779719974179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20779103712035706293298905 15584327784026779719974179)
  ·
    refine ⟨23376491676040169579961269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15584327784026779719974179 23376491676040169579961269)
    ·
      refine ⟨2191546094628765898121369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23376491676040169579961269 2191546094628765898121369)
      ·
        refine ⟨1643659570971574423591027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2191546094628765898121369 1643659570971574423591027)
        ·
          refine ⟨2465489356457361635386541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1643659570971574423591027 2465489356457361635386541)
          ·
            refine ⟨924558508671510613269953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2465489356457361635386541 924558508671510613269953)
            ·
              refine ⟨693418881503632959952465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 924558508671510613269953 693418881503632959952465)
              ·
                refine ⟨520064161127724719964349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 693418881503632959952465 520064161127724719964349)
                ·
                  refine ⟨195024060422896769986631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 520064161127724719964349 195024060422896769986631)
                  ·
                    rfl

theorem cell21_854568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 2, 3].length) (baseStart_854568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_854568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_854568 prefixEnd_854568 := by exact prefixLift 854568
  have htrace : WordTrace (prefixWord ++ tailWord_854568) baseStart_854568 baseEnd_854568 := by
    simpa [prefixWord, tailWord_854568, baseEnd_854568] using wordTrace_append hprefix tailTrace_854568
  have hstable : (prefixWord ++ tailWord_854568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854568).length < 2 ^ (prefixWord ++ tailWord_854568).sum := by decide
  have hdescent : baseEnd_854568 < baseStart_854568 := by decide
  rcases family_descends (prefixWord ++ tailWord_854568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854593 : List Nat := [1, 2, 5, 1, 1, 3, 1, 2, 5]
def baseStart_854593 : Nat := 118140960795 + 854593 * 2 ^ 59
def prefixEnd_854593 : Nat := 4983230072969 + 3 ^ 40 * 854593 * 2
def baseEnd_854593 : Nat := 195029765763502282069913

theorem tailTrace_854593 : CollatzResearch.WordTrace tailWord_854593 prefixEnd_854593 195029765763502282069913 := by
  unfold tailWord_854593
  simp only [CollatzResearch.WordTrace]
  refine ⟨31169567392962988709608433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20779711595308659139738955 31169567392962988709608433)
  ·
    refine ⟨23377175544722241532206325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31169567392962988709608433 23377175544722241532206325)
    ·
      refine ⟨2191610207317710143644343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23377175544722241532206325 2191610207317710143644343)
      ·
        refine ⟨3287415310976565215466515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2191610207317710143644343 3287415310976565215466515)
        ·
          refine ⟨4931122966464847823199773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3287415310976565215466515 4931122966464847823199773)
          ·
            refine ⟨1849171112424317933699915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4931122966464847823199773 1849171112424317933699915)
            ·
              refine ⟨2773756668636476900549873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1849171112424317933699915 2773756668636476900549873)
              ·
                refine ⟨2080317501477357675412405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2773756668636476900549873 2080317501477357675412405)
                ·
                  refine ⟨195029765763502282069913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2080317501477357675412405 195029765763502282069913)
                  ·
                    rfl

theorem cell21_854593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 5].length) (baseStart_854593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_854593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_854593 prefixEnd_854593 := by exact prefixLift 854593
  have htrace : WordTrace (prefixWord ++ tailWord_854593) baseStart_854593 baseEnd_854593 := by
    simpa [prefixWord, tailWord_854593, baseEnd_854593] using wordTrace_append hprefix tailTrace_854593
  have hstable : (prefixWord ++ tailWord_854593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854593).length < 2 ^ (prefixWord ++ tailWord_854593).sum := by decide
  have hdescent : baseEnd_854593 < baseStart_854593 := by decide
  rcases family_descends (prefixWord ++ tailWord_854593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854610 : List Nat := [3, 2, 2, 1, 2, 1, 4, 3, 3]
def baseStart_854610 : Nat := 118140960795 + 854610 * 2 ^ 59
def prefixEnd_854610 : Nat := 4983230072969 + 3 ^ 40 * 854610 * 2
def baseEnd_854610 : Nat := 195033645395114030286545

theorem tailTrace_854610 : CollatzResearch.WordTrace tailWord_854610 prefixEnd_854610 195033645395114030286545 := by
  unfold tailWord_854610
  simp only [CollatzResearch.WordTrace]
  refine ⟨7792546858475350153244321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20780124955934267075318189 7792546858475350153244321)
  ·
    refine ⟨5844410143856512614933241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7792546858475350153244321 5844410143856512614933241)
    ·
      refine ⟨4383307607892384461199931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5844410143856512614933241 4383307607892384461199931)
      ·
        refine ⟨6574961411838576691799897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4383307607892384461199931 6574961411838576691799897)
        ·
          refine ⟨4931221058878932518849923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6574961411838576691799897 4931221058878932518849923)
          ·
            refine ⟨7396831588318398778274885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4931221058878932518849923 7396831588318398778274885)
            ·
              refine ⟨1386905922809699770926541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7396831588318398778274885 1386905922809699770926541)
              ·
                refine ⟨520089721053637414097453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1386905922809699770926541 520089721053637414097453)
                ·
                  refine ⟨195033645395114030286545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 520089721053637414097453 195033645395114030286545)
                  ·
                    rfl

theorem cell21_854610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_854610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_854610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_854610 prefixEnd_854610 := by exact prefixLift 854610
  have htrace : WordTrace (prefixWord ++ tailWord_854610) baseStart_854610 baseEnd_854610 := by
    simpa [prefixWord, tailWord_854610, baseEnd_854610] using wordTrace_append hprefix tailTrace_854610
  have hstable : (prefixWord ++ tailWord_854610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854610).length < 2 ^ (prefixWord ++ tailWord_854610).sum := by decide
  have hdescent : baseEnd_854610 < baseStart_854610 := by decide
  rcases family_descends (prefixWord ++ tailWord_854610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854652 : List Nat := [2, 2, 2, 1, 1, 2, 4, 2, 5]
def baseStart_854652 : Nat := 118140960795 + 854652 * 2 ^ 59
def prefixEnd_854652 : Nat := 4983230072969 + 3 ^ 40 * 854652 * 2
def baseEnd_854652 : Nat := 195043230367331290586459

theorem tailTrace_854652 : CollatzResearch.WordTrace tailWord_854652 prefixEnd_854652 195043230367331290586459 := by
  unfold tailWord_854652
  simp only [CollatzResearch.WordTrace]
  refine ⟨15585859649874620893003105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20781146199832827857337473 15585859649874620893003105)
  ·
    refine ⟨11689394737405965669752329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15585859649874620893003105 11689394737405965669752329)
    ·
      refine ⟨8767046053054474252314247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11689394737405965669752329 8767046053054474252314247)
      ·
        refine ⟨13150569079581711378471371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8767046053054474252314247 13150569079581711378471371)
        ·
          refine ⟨19725853619372567067707057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13150569079581711378471371 19725853619372567067707057)
          ·
            refine ⟨14794390214529425300780293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19725853619372567067707057 14794390214529425300780293)
            ·
              refine ⟨2773948165224267243896305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14794390214529425300780293 2773948165224267243896305)
              ·
                refine ⟨2080461123918200432922229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2773948165224267243896305 2080461123918200432922229)
                ·
                  refine ⟨195043230367331290586459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2080461123918200432922229 195043230367331290586459)
                  ·
                    rfl

theorem cell21_854652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_854652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_854652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_854652 prefixEnd_854652 := by exact prefixLift 854652
  have htrace : WordTrace (prefixWord ++ tailWord_854652) baseStart_854652 baseEnd_854652 := by
    simpa [prefixWord, tailWord_854652, baseEnd_854652] using wordTrace_append hprefix tailTrace_854652
  have hstable : (prefixWord ++ tailWord_854652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854652).length < 2 ^ (prefixWord ++ tailWord_854652).sum := by decide
  have hdescent : baseEnd_854652 < baseStart_854652 := by decide
  rcases family_descends (prefixWord ++ tailWord_854652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854745 : List Nat := [1, 2, 1, 2, 3, 2, 3, 4, 3]
def baseStart_854745 : Nat := 118140960795 + 854745 * 2 ^ 59
def prefixEnd_854745 : Nat := 4983230072969 + 3 ^ 40 * 854745 * 2
def baseEnd_854745 : Nat := 195064454234383795536269

theorem tailTrace_854745 : CollatzResearch.WordTrace tailWord_854745 prefixEnd_854745 195064454234383795536269 := by
  unfold tailWord_854745
  simp only [CollatzResearch.WordTrace]
  refine ⟨31175111288412318669141689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20783407525608212446094459 31175111288412318669141689)
  ·
    refine ⟨23381333466309239001856267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31175111288412318669141689 23381333466309239001856267)
    ·
      refine ⟨35072000199463858502784401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23381333466309239001856267 35072000199463858502784401)
      ·
        refine ⟨26304000149597893877088301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35072000199463858502784401 26304000149597893877088301)
        ·
          refine ⟨9864000056099210203908113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26304000149597893877088301 9864000056099210203908113)
          ·
            refine ⟨7398000042074407652931085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9864000056099210203908113 7398000042074407652931085)
            ·
              refine ⟨2774250015777902869849157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7398000042074407652931085 2774250015777902869849157)
              ·
                refine ⟨520171877958356788096717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2774250015777902869849157 520171877958356788096717)
                ·
                  refine ⟨195064454234383795536269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 520171877958356788096717 195064454234383795536269)
                  ·
                    rfl

theorem cell21_854745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 4, 3].length) (baseStart_854745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_854745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_854745 prefixEnd_854745 := by exact prefixLift 854745
  have htrace : WordTrace (prefixWord ++ tailWord_854745) baseStart_854745 baseEnd_854745 := by
    simpa [prefixWord, tailWord_854745, baseEnd_854745] using wordTrace_append hprefix tailTrace_854745
  have hstable : (prefixWord ++ tailWord_854745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854745).length < 2 ^ (prefixWord ++ tailWord_854745).sum := by decide
  have hdescent : baseEnd_854745 < baseStart_854745 := by decide
  rcases family_descends (prefixWord ++ tailWord_854745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854787 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 9]
def baseStart_854787 : Nat := 118140960795 + 854787 * 2 ^ 59
def prefixEnd_854787 : Nat := 4983230072969 + 3 ^ 40 * 854787 * 2
def baseEnd_854787 : Nat := 195074039206601055836183

theorem tailTrace_854787 : CollatzResearch.WordTrace tailWord_854787 prefixEnd_854787 195074039206601055836183 := by
  unfold tailWord_854787
  simp only [CollatzResearch.WordTrace]
  refine ⟨31176643154260159842170615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20784428769506773228113743 31176643154260159842170615)
  ·
    refine ⟨46764964731390239763255923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31176643154260159842170615 46764964731390239763255923)
    ·
      refine ⟨70147447097085359644883885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46764964731390239763255923 70147447097085359644883885)
      ·
        refine ⟨26305292661407009866831457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70147447097085359644883885 26305292661407009866831457)
        ·
          refine ⟨19728969496055257400123593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26305292661407009866831457 19728969496055257400123593)
          ·
            refine ⟨14796727122041443050092695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19728969496055257400123593 14796727122041443050092695)
            ·
              refine ⟨22195090683062164575139043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14796727122041443050092695 22195090683062164575139043)
              ·
                refine ⟨33292636024593246862708565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22195090683062164575139043 33292636024593246862708565)
                ·
                  refine ⟨195074039206601055836183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 33292636024593246862708565 195074039206601055836183)
                  ·
                    rfl

theorem cell21_854787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 9].length) (baseStart_854787 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_854787 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_854787 prefixEnd_854787 := by exact prefixLift 854787
  have htrace : WordTrace (prefixWord ++ tailWord_854787) baseStart_854787 baseEnd_854787 := by
    simpa [prefixWord, tailWord_854787, baseEnd_854787] using wordTrace_append hprefix tailTrace_854787
  have hstable : (prefixWord ++ tailWord_854787).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854787).length < 2 ^ (prefixWord ++ tailWord_854787).sum := by decide
  have hdescent : baseEnd_854787 < baseStart_854787 := by decide
  rcases family_descends (prefixWord ++ tailWord_854787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854970 : List Nat := [3, 1, 1, 1, 2, 1, 5, 1, 6]
def baseStart_854970 : Nat := 118140960795 + 854970 * 2 ^ 59
def prefixEnd_854970 : Nat := 4983230072969 + 3 ^ 40 * 854970 * 2
def baseEnd_854970 : Nat := 195115802299833404285809

theorem tailTrace_854970 : CollatzResearch.WordTrace tailWord_854970 prefixEnd_854970 195115802299833404285809 := by
  unfold tailWord_854970
  simp only [CollatzResearch.WordTrace]
  refine ⟨7795829428149295524020591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20788878475064788064054909 7795829428149295524020591)
  ·
    refine ⟨11693744142223943286030887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7795829428149295524020591 11693744142223943286030887)
    ·
      refine ⟨17540616213335914929046331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11693744142223943286030887 17540616213335914929046331)
      ·
        refine ⟨26310924320003872393569497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17540616213335914929046331 26310924320003872393569497)
        ·
          refine ⟨19733193240002904295177123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26310924320003872393569497 19733193240002904295177123)
          ·
            refine ⟨29599789860004356442765685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19733193240002904295177123 29599789860004356442765685)
            ·
              refine ⟨2774980299375408416509283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29599789860004356442765685 2774980299375408416509283)
              ·
                refine ⟨4162470449063112624763925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2774980299375408416509283 4162470449063112624763925)
                ·
                  refine ⟨195115802299833404285809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4162470449063112624763925 195115802299833404285809)
                  ·
                    rfl

theorem cell21_854970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_854970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_854970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_854970 prefixEnd_854970 := by exact prefixLift 854970
  have htrace : WordTrace (prefixWord ++ tailWord_854970) baseStart_854970 baseEnd_854970 := by
    simpa [prefixWord, tailWord_854970, baseEnd_854970] using wordTrace_append hprefix tailTrace_854970
  have hstable : (prefixWord ++ tailWord_854970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854970).length < 2 ^ (prefixWord ++ tailWord_854970).sum := by decide
  have hdescent : baseEnd_854970 < baseStart_854970 := by decide
  rcases family_descends (prefixWord ++ tailWord_854970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854973 : List Nat := [1, 4, 1, 2, 4, 1, 2, 1, 5]
def baseStart_854973 : Nat := 118140960795 + 854973 * 2 ^ 59
def prefixEnd_854973 : Nat := 4983230072969 + 3 ^ 40 * 854973 * 2
def baseEnd_854973 : Nat := 195116486940706065735803

theorem tailTrace_854973 : CollatzResearch.WordTrace tailWord_854973 prefixEnd_854973 195116486940706065735803 := by
  unfold tailWord_854973
  simp only [CollatzResearch.WordTrace]
  refine ⟨31183427131586313608441573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20788951421057542405627715 31183427131586313608441573)
  ·
    refine ⟨5846892587172433801582795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31183427131586313608441573 5846892587172433801582795)
    ·
      refine ⟨8770338880758650702374193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5846892587172433801582795 8770338880758650702374193)
      ·
        refine ⟨6577754160568988026780645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8770338880758650702374193 6577754160568988026780645)
        ·
          refine ⟨1233328905106685255021371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6577754160568988026780645 1233328905106685255021371)
          ·
            refine ⟨1849993357660027882532057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1233328905106685255021371 1849993357660027882532057)
            ·
              refine ⟨1387495018245020911899043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1849993357660027882532057 1387495018245020911899043)
              ·
                refine ⟨2081242527367531367848565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1387495018245020911899043 2081242527367531367848565)
                ·
                  refine ⟨195116486940706065735803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2081242527367531367848565 195116486940706065735803)
                  ·
                    rfl

theorem cell21_854973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_854973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_854973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_854973 prefixEnd_854973 := by exact prefixLift 854973
  have htrace : WordTrace (prefixWord ++ tailWord_854973) baseStart_854973 baseEnd_854973 := by
    simpa [prefixWord, tailWord_854973, baseEnd_854973] using wordTrace_append hprefix tailTrace_854973
  have hstable : (prefixWord ++ tailWord_854973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854973).length < 2 ^ (prefixWord ++ tailWord_854973).sum := by decide
  have hdescent : baseEnd_854973 < baseStart_854973 := by decide
  rcases family_descends (prefixWord ++ tailWord_854973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855001 : List Nat := [1, 2, 1, 2, 5, 2, 1, 7]
def baseStart_855001 : Nat := 118140960795 + 855001 * 2 ^ 59
def prefixEnd_855001 : Nat := 4983230072969 + 3 ^ 40 * 855001 * 2
def baseEnd_855001 : Nat := 65040958974061413089693

theorem tailTrace_855001 : CollatzResearch.WordTrace tailWord_855001 prefixEnd_855001 65040958974061413089693 := by
  unfold tailWord_855001
  simp only [CollatzResearch.WordTrace]
  refine ⟨31184448375484874390460857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20789632250323249593640571 31184448375484874390460857)
  ·
    refine ⟨23388336281613655792845643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31184448375484874390460857 23388336281613655792845643)
    ·
      refine ⟨35082504422420483689268465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23388336281613655792845643 35082504422420483689268465)
      ·
        refine ⟨26311878316815362766951349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35082504422420483689268465 26311878316815362766951349)
        ·
          refine ⟨2466738592201440259401689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26311878316815362766951349 2466738592201440259401689)
          ·
            refine ⟨1850053944151080194551267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2466738592201440259401689 1850053944151080194551267)
            ·
              refine ⟨2775080916226620291826901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1850053944151080194551267 2775080916226620291826901)
              ·
                refine ⟨65040958974061413089693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2775080916226620291826901 65040958974061413089693)
                ·
                  rfl

theorem cell21_855001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 7].length) (baseStart_855001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_855001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_855001 prefixEnd_855001 := by exact prefixLift 855001
  have htrace : WordTrace (prefixWord ++ tailWord_855001) baseStart_855001 baseEnd_855001 := by
    simpa [prefixWord, tailWord_855001, baseEnd_855001] using wordTrace_append hprefix tailTrace_855001
  have hstable : (prefixWord ++ tailWord_855001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855001).length < 2 ^ (prefixWord ++ tailWord_855001).sum := by decide
  have hdescent : baseEnd_855001 < baseStart_855001 := by decide
  rcases family_descends (prefixWord ++ tailWord_855001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855007 : List Nat := [1, 1, 2, 3, 6, 1, 1, 3, 3]
def baseStart_855007 : Nat := 118140960795 + 855007 * 2 ^ 59
def prefixEnd_855007 : Nat := 4983230072969 + 3 ^ 40 * 855007 * 2
def baseEnd_855007 : Nat := 195124246203929562169067

theorem tailTrace_855007 : CollatzResearch.WordTrace tailWord_855007 prefixEnd_855007 195124246203929562169067 := by
  unfold tailWord_855007
  simp only [CollatzResearch.WordTrace]
  refine ⟨31184667213463137415179275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20789778142308758276786183 31184667213463137415179275)
  ·
    refine ⟨46777000820194706122768913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31184667213463137415179275 46777000820194706122768913)
    ·
      refine ⟨35082750615146029592076685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46777000820194706122768913 35082750615146029592076685)
      ·
        refine ⟨13156031480679761097028757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35082750615146029592076685 13156031480679761097028757)
        ·
          refine ⟨616688975656863801423223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13156031480679761097028757 616688975656863801423223)
          ·
            refine ⟨925033463485295702134835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616688975656863801423223 925033463485295702134835)
            ·
              refine ⟨1387550195227943553202253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 925033463485295702134835 1387550195227943553202253)
              ·
                refine ⟨520331323210478832450845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1387550195227943553202253 520331323210478832450845)
                ·
                  refine ⟨195124246203929562169067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 520331323210478832450845 195124246203929562169067)
                  ·
                    rfl

theorem cell21_855007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 3, 3].length) (baseStart_855007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_855007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_855007 prefixEnd_855007 := by exact prefixLift 855007
  have htrace : WordTrace (prefixWord ++ tailWord_855007) baseStart_855007 baseEnd_855007 := by
    simpa [prefixWord, tailWord_855007, baseEnd_855007] using wordTrace_append hprefix tailTrace_855007
  have hstable : (prefixWord ++ tailWord_855007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855007).length < 2 ^ (prefixWord ++ tailWord_855007).sum := by decide
  have hdescent : baseEnd_855007 < baseStart_855007 := by decide
  rcases family_descends (prefixWord ++ tailWord_855007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855038 : List Nat := [4, 2, 2, 2, 2, 2, 2, 1, 4]
def baseStart_855038 : Nat := 118140960795 + 855038 * 2 ^ 59
def prefixEnd_855038 : Nat := 4983230072969 + 3 ^ 40 * 855038 * 2
def baseEnd_855038 : Nat := 195131320826280397152337

theorem tailTrace_855038 : CollatzResearch.WordTrace tailWord_855038 prefixEnd_855038 195131320826280397152337 := by
  unfold tailWord_855038
  simp only [CollatzResearch.WordTrace]
  refine ⟨3898224734543853713694721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20790531917567219806371845 3898224734543853713694721)
  ·
    refine ⟨2923668550907890285271041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3898224734543853713694721 2923668550907890285271041)
    ·
      refine ⟨2192751413180917713953281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2923668550907890285271041 2192751413180917713953281)
      ·
        refine ⟨1644563559885688285464961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2192751413180917713953281 1644563559885688285464961)
        ·
          refine ⟨1233422669914266214098721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1644563559885688285464961 1233422669914266214098721)
          ·
            refine ⟨925067002435699660574041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1233422669914266214098721 925067002435699660574041)
            ·
              refine ⟨693800251826774745430531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 925067002435699660574041 693800251826774745430531)
              ·
                refine ⟨1040700377740162118145797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 693800251826774745430531 1040700377740162118145797)
                ·
                  refine ⟨195131320826280397152337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1040700377740162118145797 195131320826280397152337)
                  ·
                    rfl

theorem cell21_855038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_855038 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_855038 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_855038 prefixEnd_855038 := by exact prefixLift 855038
  have htrace : WordTrace (prefixWord ++ tailWord_855038) baseStart_855038 baseEnd_855038 := by
    simpa [prefixWord, tailWord_855038, baseEnd_855038] using wordTrace_append hprefix tailTrace_855038
  have hstable : (prefixWord ++ tailWord_855038).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855038).length < 2 ^ (prefixWord ++ tailWord_855038).sum := by decide
  have hdescent : baseEnd_855038 < baseStart_855038 := by decide
  rcases family_descends (prefixWord ++ tailWord_855038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855091 : List Nat := [1, 1, 1, 2, 4, 1, 1, 5, 5]
def baseStart_855091 : Nat := 118140960795 + 855091 * 2 ^ 59
def prefixEnd_855091 : Nat := 4983230072969 + 3 ^ 40 * 855091 * 2
def baseEnd_855091 : Nat := 195143416148364082768895

theorem tailTrace_855091 : CollatzResearch.WordTrace tailWord_855091 prefixEnd_855091 195143416148364082768895 := by
  unfold tailWord_855091
  simp only [CollatzResearch.WordTrace]
  refine ⟨31187730945158819761237127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20791820630105879840824751 31187730945158819761237127)
  ·
    refine ⟨46781596417738229641855691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31187730945158819761237127 46781596417738229641855691)
    ·
      refine ⟨70172394626607344462783537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46781596417738229641855691 70172394626607344462783537)
      ·
        refine ⟨52629295969955508347087653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70172394626607344462783537 52629295969955508347087653)
        ·
          refine ⟨9867992994366657815078935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52629295969955508347087653 9867992994366657815078935)
          ·
            refine ⟨14801989491549986722618403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9867992994366657815078935 14801989491549986722618403)
            ·
              refine ⟨22202984237324980083927605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14801989491549986722618403 22202984237324980083927605)
              ·
                refine ⟨2081529772249216882868213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22202984237324980083927605 2081529772249216882868213)
                ·
                  refine ⟨195143416148364082768895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2081529772249216882868213 195143416148364082768895)
                  ·
                    rfl

theorem cell21_855091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 5].length) (baseStart_855091 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_855091 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_855091 prefixEnd_855091 := by exact prefixLift 855091
  have htrace : WordTrace (prefixWord ++ tailWord_855091) baseStart_855091 baseEnd_855091 := by
    simpa [prefixWord, tailWord_855091, baseEnd_855091] using wordTrace_append hprefix tailTrace_855091
  have hstable : (prefixWord ++ tailWord_855091).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855091).length < 2 ^ (prefixWord ++ tailWord_855091).sum := by decide
  have hdescent : baseEnd_855091 < baseStart_855091 := by decide
  rcases family_descends (prefixWord ++ tailWord_855091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855094 : List Nat := [5, 1, 2, 1, 1, 2, 3, 6]
def baseStart_855094 : Nat := 118140960795 + 855094 * 2 ^ 59
def prefixEnd_855094 : Nat := 4983230072969 + 3 ^ 40 * 855094 * 2
def baseEnd_855094 : Nat := 65048033596412248072963

theorem tailTrace_855094 : CollatzResearch.WordTrace tailWord_855094 prefixEnd_855094 65048033596412248072963 := by
  unfold tailWord_855094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1949240022759246954599771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20791893576098634182397557 1949240022759246954599771)
  ·
    refine ⟨2923860034138870431899657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1949240022759246954599771 2923860034138870431899657)
    ·
      refine ⟨2192895025604152823924743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2923860034138870431899657 2192895025604152823924743)
      ·
        refine ⟨3289342538406229235887115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2192895025604152823924743 3289342538406229235887115)
        ·
          refine ⟨4934013807609343853830673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3289342538406229235887115 4934013807609343853830673)
          ·
            refine ⟨3700510355707007890373005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4934013807609343853830673 3700510355707007890373005)
            ·
              refine ⟨1387691383390127958889877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3700510355707007890373005 1387691383390127958889877)
              ·
                refine ⟨65048033596412248072963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1387691383390127958889877 65048033596412248072963)
                ·
                  rfl

theorem cell21_855094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_855094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_855094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_855094 prefixEnd_855094 := by exact prefixLift 855094
  have htrace : WordTrace (prefixWord ++ tailWord_855094) baseStart_855094 baseEnd_855094 := by
    simpa [prefixWord, tailWord_855094, baseEnd_855094] using wordTrace_append hprefix tailTrace_855094
  have hstable : (prefixWord ++ tailWord_855094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855094).length < 2 ^ (prefixWord ++ tailWord_855094).sum := by decide
  have hdescent : baseEnd_855094 < baseStart_855094 := by decide
  rcases family_descends (prefixWord ++ tailWord_855094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855125 : List Nat := [1, 3, 2, 2, 1, 2, 4, 3, 3]
def baseStart_855125 : Nat := 118140960795 + 855125 * 2 ^ 59
def prefixEnd_855125 : Nat := 4983230072969 + 3 ^ 40 * 855125 * 2
def baseEnd_855125 : Nat := 195151175411587579202159

theorem tailTrace_855125 : CollatzResearch.WordTrace tailWord_855125 prefixEnd_855125 195151175411587579202159 := by
  unfold tailWord_855125
  simp only [CollatzResearch.WordTrace]
  refine ⟨31188971027035643567974829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20792647351357095711983219 31188971027035643567974829)
  ·
    refine ⟨11695864135138366337990561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31188971027035643567974829 11695864135138366337990561)
    ·
      refine ⟨8771898101353774753492921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11695864135138366337990561 8771898101353774753492921)
      ·
        refine ⟨6578923576015331065119691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8771898101353774753492921 6578923576015331065119691)
        ·
          refine ⟨9868385364022996597679537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6578923576015331065119691 9868385364022996597679537)
          ·
            refine ⟨7401289023017247448259653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9868385364022996597679537 7401289023017247448259653)
            ·
              refine ⟨1387741691815733896548685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7401289023017247448259653 1387741691815733896548685)
              ·
                refine ⟨520403134430900211205757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1387741691815733896548685 520403134430900211205757)
                ·
                  refine ⟨195151175411587579202159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 520403134430900211205757 195151175411587579202159)
                  ·
                    rfl

theorem cell21_855125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 3, 3].length) (baseStart_855125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_855125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_855125 prefixEnd_855125 := by exact prefixLift 855125
  have htrace : WordTrace (prefixWord ++ tailWord_855125) baseStart_855125 baseEnd_855125 := by
    simpa [prefixWord, tailWord_855125, baseEnd_855125] using wordTrace_append hprefix tailTrace_855125
  have hstable : (prefixWord ++ tailWord_855125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855125).length < 2 ^ (prefixWord ++ tailWord_855125).sum := by decide
  have hdescent : baseEnd_855125 < baseStart_855125 := by decide
  rcases family_descends (prefixWord ++ tailWord_855125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855136 : List Nat := [2, 1, 1, 3, 2, 2, 10]
def baseStart_855136 : Nat := 118140960795 + 855136 * 2 ^ 59
def prefixEnd_855136 : Nat := 4983230072969 + 3 ^ 40 * 855136 * 2
def baseEnd_855136 : Nat := 21683742862383778279867

theorem tailTrace_855136 : CollatzResearch.WordTrace tailWord_855136 prefixEnd_855136 21683742862383778279867 := by
  unfold tailWord_855136
  simp only [CollatzResearch.WordTrace]
  refine ⟨15594686114997896223312631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20792914819997194964416841 15594686114997896223312631)
  ·
    refine ⟨23392029172496844334968947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15594686114997896223312631 23392029172496844334968947)
    ·
      refine ⟨35088043758745266502453421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23392029172496844334968947 35088043758745266502453421)
      ·
        refine ⟨13158016409529474938420033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35088043758745266502453421 13158016409529474938420033)
        ·
          refine ⟨9868512307147106203815025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13158016409529474938420033 9868512307147106203815025)
          ·
            refine ⟨7401384230360329652861269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9868512307147106203815025 7401384230360329652861269)
            ·
              refine ⟨21683742862383778279867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7401384230360329652861269 21683742862383778279867)
              ·
                rfl

theorem cell21_855136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 10].length) (baseStart_855136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_855136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_855136 prefixEnd_855136 := by exact prefixLift 855136
  have htrace : WordTrace (prefixWord ++ tailWord_855136) baseStart_855136 baseEnd_855136 := by
    simpa [prefixWord, tailWord_855136, baseEnd_855136] using wordTrace_append hprefix tailTrace_855136
  have hstable : (prefixWord ++ tailWord_855136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855136).length < 2 ^ (prefixWord ++ tailWord_855136).sum := by decide
  have hdescent : baseEnd_855136 < baseStart_855136 := by decide
  rcases family_descends (prefixWord ++ tailWord_855136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855184 : List Nat := [2, 1, 1, 1, 1, 1, 4, 7, 3]
def baseStart_855184 : Nat := 118140960795 + 855184 * 2 ^ 59
def prefixEnd_855184 : Nat := 4983230072969 + 3 ^ 40 * 855184 * 2
def baseEnd_855184 : Nat := 195164640015416587718705

theorem tailTrace_855184 : CollatzResearch.WordTrace tailWord_855184 prefixEnd_855184 195164640015416587718705 := by
  unfold tailWord_855184
  simp only [CollatzResearch.WordTrace]
  refine ⟨15595561466910948322186303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20794081955881264429581737 15595561466910948322186303)
  ·
    refine ⟨23393342200366422483279455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15595561466910948322186303 23393342200366422483279455)
    ·
      refine ⟨35090013300549633724919183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23393342200366422483279455 35090013300549633724919183)
      ·
        refine ⟨52635019950824450587378775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35090013300549633724919183 52635019950824450587378775)
        ·
          refine ⟨78952529926236675881068163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52635019950824450587378775 78952529926236675881068163)
          ·
            refine ⟨118428794889355013821602245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78952529926236675881068163 118428794889355013821602245)
            ·
              refine ⟨22205399041754065091550421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118428794889355013821602245 22205399041754065091550421)
              ·
                refine ⟨520439040041110900583213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 22205399041754065091550421 520439040041110900583213)
                ·
                  refine ⟨195164640015416587718705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 520439040041110900583213 195164640015416587718705)
                  ·
                    rfl

theorem cell21_855184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 7, 3].length) (baseStart_855184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_855184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_855184 prefixEnd_855184 := by exact prefixLift 855184
  have htrace : WordTrace (prefixWord ++ tailWord_855184) baseStart_855184 baseEnd_855184 := by
    simpa [prefixWord, tailWord_855184, baseEnd_855184] using wordTrace_append hprefix tailTrace_855184
  have hstable : (prefixWord ++ tailWord_855184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855184).length < 2 ^ (prefixWord ++ tailWord_855184).sum := by decide
  have hdescent : baseEnd_855184 < baseStart_855184 := by decide
  rcases family_descends (prefixWord ++ tailWord_855184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855215 : List Nat := [1, 1, 2, 1, 2, 3, 6, 1, 4]
def baseStart_855215 : Nat := 118140960795 + 855215 * 2 ^ 59
def prefixEnd_855215 : Nat := 4983230072969 + 3 ^ 40 * 855215 * 2
def baseEnd_855215 : Nat := 195171714637767422701975

theorem tailTrace_855215 : CollatzResearch.WordTrace tailWord_855215 prefixEnd_855215 195171714637767422701975 := by
  unfold tailWord_855215
  simp only [CollatzResearch.WordTrace]
  refine ⟨31192253596709588938751099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20794835731139725959167399 31192253596709588938751099)
  ·
    refine ⟨46788380395064383408126649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31192253596709588938751099 46788380395064383408126649)
    ·
      refine ⟨35091285296298287556094987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46788380395064383408126649 35091285296298287556094987)
      ·
        refine ⟨52636927944447431334142481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35091285296298287556094987 52636927944447431334142481)
        ·
          refine ⟨39477695958335573500606861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52636927944447431334142481 39477695958335573500606861)
          ·
            refine ⟨14804135984375840062727573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39477695958335573500606861 14804135984375840062727573)
            ·
              refine ⟨693943874267617502940355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14804135984375840062727573 693943874267617502940355)
              ·
                refine ⟨1040915811401426254410533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 693943874267617502940355 1040915811401426254410533)
                ·
                  refine ⟨195171714637767422701975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1040915811401426254410533 195171714637767422701975)
                  ·
                    rfl

theorem cell21_855215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 4].length) (baseStart_855215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_855215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_855215 prefixEnd_855215 := by exact prefixLift 855215
  have htrace : WordTrace (prefixWord ++ tailWord_855215) baseStart_855215 baseEnd_855215 := by
    simpa [prefixWord, tailWord_855215, baseEnd_855215] using wordTrace_append hprefix tailTrace_855215
  have hstable : (prefixWord ++ tailWord_855215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855215).length < 2 ^ (prefixWord ++ tailWord_855215).sum := by decide
  have hdescent : baseEnd_855215 < baseStart_855215 := by decide
  rcases family_descends (prefixWord ++ tailWord_855215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855252 : List Nat := [2, 4, 1, 4, 1, 2, 2, 2, 3]
def baseStart_855252 : Nat := 118140960795 + 855252 * 2 ^ 59
def prefixEnd_855252 : Nat := 4983230072969 + 3 ^ 40 * 855252 * 2
def baseEnd_855252 : Nat := 195180158541863580585233

theorem tailTrace_855252 : CollatzResearch.WordTrace tailWord_855252 prefixEnd_855252 195180158541863580585233 := by
  unfold tailWord_855252
  simp only [CollatzResearch.WordTrace]
  refine ⟨15596801548787772128924005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20795735398383696171898673 15596801548787772128924005)
  ·
    refine ⟨2924400290397707274173251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15596801548787772128924005 2924400290397707274173251)
    ·
      refine ⟨4386600435596560911259877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2924400290397707274173251 4386600435596560911259877)
      ·
        refine ⟨822487581674355170861227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4386600435596560911259877 822487581674355170861227)
        ·
          refine ⟨1233731372511532756291841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 822487581674355170861227 1233731372511532756291841)
          ·
            refine ⟨925298529383649567218881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1233731372511532756291841 925298529383649567218881)
            ·
              refine ⟨693973897037737175414161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 925298529383649567218881 693973897037737175414161)
              ·
                refine ⟨520480422778302881560621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 693973897037737175414161 520480422778302881560621)
                ·
                  refine ⟨195180158541863580585233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 520480422778302881560621 195180158541863580585233)
                  ·
                    rfl

theorem cell21_855252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_855252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_855252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_855252 prefixEnd_855252 := by exact prefixLift 855252
  have htrace : WordTrace (prefixWord ++ tailWord_855252) baseStart_855252 baseEnd_855252 := by
    simpa [prefixWord, tailWord_855252, baseEnd_855252] using wordTrace_append hprefix tailTrace_855252
  have hstable : (prefixWord ++ tailWord_855252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855252).length < 2 ^ (prefixWord ++ tailWord_855252).sum := by decide
  have hdescent : baseEnd_855252 < baseStart_855252 := by decide
  rcases family_descends (prefixWord ++ tailWord_855252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855294 : List Nat := [4, 2, 2, 1, 1, 3, 2, 3, 3]
def baseStart_855294 : Nat := 118140960795 + 855294 * 2 ^ 59
def prefixEnd_855294 : Nat := 4983230072969 + 3 ^ 40 * 855294 * 2
def baseEnd_855294 : Nat := 195189743514080840885147

theorem tailTrace_855294 : CollatzResearch.WordTrace tailWord_855294 prefixEnd_855294 195189743514080840885147 := by
  unfold tailWord_855294
  simp only [CollatzResearch.WordTrace]
  refine ⟨3899391870427923178859617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20796756642282256953917957 3899391870427923178859617)
  ·
    refine ⟨2924543902820942384144713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3899391870427923178859617 2924543902820942384144713)
    ·
      refine ⟨2193407927115706788108535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2924543902820942384144713 2193407927115706788108535)
      ·
        refine ⟨3290111890673560182162803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2193407927115706788108535 3290111890673560182162803)
        ·
          refine ⟨4935167836010340273244205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3290111890673560182162803 4935167836010340273244205)
          ·
            refine ⟨1850687938503877602466577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4935167836010340273244205 1850687938503877602466577)
            ·
              refine ⟨1388015953877908201849933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1850687938503877602466577 1388015953877908201849933)
              ·
                refine ⟨520505982704215575693725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1388015953877908201849933 520505982704215575693725)
                ·
                  refine ⟨195189743514080840885147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 520505982704215575693725 195189743514080840885147)
                  ·
                    rfl

theorem cell21_855294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_855294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_855294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_855294 prefixEnd_855294 := by exact prefixLift 855294
  have htrace : WordTrace (prefixWord ++ tailWord_855294) baseStart_855294 baseEnd_855294 := by
    simpa [prefixWord, tailWord_855294, baseEnd_855294] using wordTrace_append hprefix tailTrace_855294
  have hstable : (prefixWord ++ tailWord_855294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855294).length < 2 ^ (prefixWord ++ tailWord_855294).sum := by decide
  have hdescent : baseEnd_855294 < baseStart_855294 := by decide
  rcases family_descends (prefixWord ++ tailWord_855294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855336 : List Nat := [2, 1, 5, 1, 2, 1, 2, 2, 5]
def baseStart_855336 : Nat := 118140960795 + 855336 * 2 ^ 59
def prefixEnd_855336 : Nat := 4983230072969 + 3 ^ 40 * 855336 * 2
def baseEnd_855336 : Nat := 195199328486298101185061

theorem tailTrace_855336 : CollatzResearch.WordTrace tailWord_855336 prefixEnd_855336 195199328486298101185061 := by
  unfold tailWord_855336
  simp only [CollatzResearch.WordTrace]
  refine ⟨15598333414635613301952931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20797777886180817735937241 15598333414635613301952931)
  ·
    refine ⟨23397500121953419952929397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15598333414635613301952931 23397500121953419952929397)
    ·
      refine ⟨2193515636433133120587131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23397500121953419952929397 2193515636433133120587131)
      ·
        refine ⟨3290273454649699680880697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2193515636433133120587131 3290273454649699680880697)
        ·
          refine ⟨2467705090987274760660523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3290273454649699680880697 2467705090987274760660523)
          ·
            refine ⟨3701557636480912140990785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2467705090987274760660523 3701557636480912140990785)
            ·
              refine ⟨2776168227360684105743089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3701557636480912140990785 2776168227360684105743089)
              ·
                refine ⟨2082126170520513079307317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2776168227360684105743089 2082126170520513079307317)
                ·
                  refine ⟨195199328486298101185061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2082126170520513079307317 195199328486298101185061)
                  ·
                    rfl

theorem cell21_855336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 5].length) (baseStart_855336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_855336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_855336 prefixEnd_855336 := by exact prefixLift 855336
  have htrace : WordTrace (prefixWord ++ tailWord_855336) baseStart_855336 baseEnd_855336 := by
    simpa [prefixWord, tailWord_855336, baseEnd_855336] using wordTrace_append hprefix tailTrace_855336
  have hstable : (prefixWord ++ tailWord_855336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855336).length < 2 ^ (prefixWord ++ tailWord_855336).sum := by decide
  have hdescent : baseEnd_855336 < baseStart_855336 := by decide
  rcases family_descends (prefixWord ++ tailWord_855336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855381 : List Nat := [1, 3, 2, 2, 3, 2, 2, 6]
def baseStart_855381 : Nat := 118140960795 + 855381 * 2 ^ 59
def prefixEnd_855381 : Nat := 4983230072969 + 3 ^ 40 * 855381 * 2
def baseEnd_855381 : Nat := 65069866033129340978323

theorem tailTrace_855381 : CollatzResearch.WordTrace tailWord_855381 prefixEnd_855381 65069866033129340978323 := by
  unfold tailWord_855381
  simp only [CollatzResearch.WordTrace]
  refine ⟨31198308114108199289293997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20798872076072132859529331 31198308114108199289293997)
  ·
    refine ⟨11699365542790574733485249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31198308114108199289293997 11699365542790574733485249)
    ·
      refine ⟨8774524157092931050113937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11699365542790574733485249 8774524157092931050113937)
      ·
        refine ⟨6580893117819698287585453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8774524157092931050113937 6580893117819698287585453)
        ·
          refine ⟨2467834919182386857844545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6580893117819698287585453 2467834919182386857844545)
          ·
            refine ⟨1850876189386790143383409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2467834919182386857844545 1850876189386790143383409)
            ·
              refine ⟨1388157142040092607537557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1850876189386790143383409 1388157142040092607537557)
              ·
                refine ⟨65069866033129340978323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1388157142040092607537557 65069866033129340978323)
                ·
                  rfl

theorem cell21_855381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 6].length) (baseStart_855381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_855381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_855381 prefixEnd_855381 := by exact prefixLift 855381
  have htrace : WordTrace (prefixWord ++ tailWord_855381) baseStart_855381 baseEnd_855381 := by
    simpa [prefixWord, tailWord_855381, baseEnd_855381] using wordTrace_append hprefix tailTrace_855381
  have hstable : (prefixWord ++ tailWord_855381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855381).length < 2 ^ (prefixWord ++ tailWord_855381).sum := by decide
  have hdescent : baseEnd_855381 < baseStart_855381 := by decide
  rcases family_descends (prefixWord ++ tailWord_855381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855409 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 8]
def baseStart_855409 : Nat := 118140960795 + 855409 * 2 ^ 59
def prefixEnd_855409 : Nat := 4983230072969 + 3 ^ 40 * 855409 * 2
def baseEnd_855409 : Nat := 195215988080866196468245

theorem tailTrace_855409 : CollatzResearch.WordTrace tailWord_855409 prefixEnd_855409 195215988080866196468245 := by
  unfold tailWord_855409
  simp only [CollatzResearch.WordTrace]
  refine ⟨31199329358006760071313281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20799552905337840047542187 31199329358006760071313281)
  ·
    refine ⟨23399497018505070053484961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31199329358006760071313281 23399497018505070053484961)
    ·
      refine ⟨17549622763878802540113721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23399497018505070053484961 17549622763878802540113721)
      ·
        refine ⟨13162217072909101905085291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17549622763878802540113721 13162217072909101905085291)
        ·
          refine ⟨19743325609363652857627937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13162217072909101905085291 19743325609363652857627937)
          ·
            refine ⟨14807494207022739643220953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19743325609363652857627937 14807494207022739643220953)
            ·
              refine ⟨11105620655267054732415715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14807494207022739643220953 11105620655267054732415715)
              ·
                refine ⟨16658430982900582098623573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11105620655267054732415715 16658430982900582098623573)
                ·
                  refine ⟨195215988080866196468245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16658430982900582098623573 195215988080866196468245)
                  ·
                    rfl

theorem cell21_855409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 8].length) (baseStart_855409 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_855409 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_855409 prefixEnd_855409 := by exact prefixLift 855409
  have htrace : WordTrace (prefixWord ++ tailWord_855409) baseStart_855409 baseEnd_855409 := by
    simpa [prefixWord, tailWord_855409, baseEnd_855409] using wordTrace_append hprefix tailTrace_855409
  have hstable : (prefixWord ++ tailWord_855409).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855409).length < 2 ^ (prefixWord ++ tailWord_855409).sum := by decide
  have hdescent : baseEnd_855409 < baseStart_855409 := by decide
  rcases family_descends (prefixWord ++ tailWord_855409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855429 : List Nat := [1, 3, 1, 1, 3, 1, 6, 2, 3]
def baseStart_855429 : Nat := 118140960795 + 855429 * 2 ^ 59
def prefixEnd_855429 : Nat := 4983230072969 + 3 ^ 40 * 855429 * 2
def baseEnd_855429 : Nat := 195220552353350606134871

theorem tailTrace_855429 : CollatzResearch.WordTrace tailWord_855429 prefixEnd_855429 195220552353350606134871 := by
  unfold tailWord_855429
  simp only [CollatzResearch.WordTrace]
  refine ⟨31200058817934303487041341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20800039211956202324694227 31200058817934303487041341)
  ·
    refine ⟨11700022056725363807640503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31200058817934303487041341 11700022056725363807640503)
    ·
      refine ⟨17550033085088045711460755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11700022056725363807640503 17550033085088045711460755)
      ·
        refine ⟨26325049627632068567191133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17550033085088045711460755 26325049627632068567191133)
        ·
          refine ⟨9871893610362025712696675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26325049627632068567191133 9871893610362025712696675)
          ·
            refine ⟨14807840415543038569045013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9871893610362025712696675 14807840415543038569045013)
            ·
              refine ⟨694117519478579932923985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14807840415543038569045013 694117519478579932923985)
              ·
                refine ⟨520588139608934949692989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 694117519478579932923985 520588139608934949692989)
                ·
                  refine ⟨195220552353350606134871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 520588139608934949692989 195220552353350606134871)
                  ·
                    rfl

theorem cell21_855429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 2, 3].length) (baseStart_855429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_855429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_855429 prefixEnd_855429 := by exact prefixLift 855429
  have htrace : WordTrace (prefixWord ++ tailWord_855429) baseStart_855429 baseEnd_855429 := by
    simpa [prefixWord, tailWord_855429, baseEnd_855429] using wordTrace_append hprefix tailTrace_855429
  have hstable : (prefixWord ++ tailWord_855429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855429).length < 2 ^ (prefixWord ++ tailWord_855429).sum := by decide
  have hdescent : baseEnd_855429 < baseStart_855429 := by decide
  rcases family_descends (prefixWord ++ tailWord_855429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855488 : List Nat := [2, 1, 1, 2, 3, 1, 4, 4, 3]
def baseStart_855488 : Nat := 118140960795 + 855488 * 2 ^ 59
def prefixEnd_855488 : Nat := 4983230072969 + 3 ^ 40 * 855488 * 2
def baseEnd_855488 : Nat := 195234016957179614651417

theorem tailTrace_855488 : CollatzResearch.WordTrace tailWord_855488 prefixEnd_855488 195234016957179614651417 := by
  unfold tailWord_855488
  simp only [CollatzResearch.WordTrace]
  refine ⟨15601105362360278281719559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20801473816480371042292745 15601105362360278281719559)
  ·
    refine ⟨23401658043540417422579339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15601105362360278281719559 23401658043540417422579339)
    ·
      refine ⟨35102487065310626133869009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23401658043540417422579339 35102487065310626133869009)
      ·
        refine ⟨26326865298982969600401757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35102487065310626133869009 26326865298982969600401757)
        ·
          refine ⟨9872574487118613600150659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26326865298982969600401757 9872574487118613600150659)
          ·
            refine ⟨14808861730677920400225989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9872574487118613600150659 14808861730677920400225989)
            ·
              refine ⟨2776661574502110075042373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14808861730677920400225989 2776661574502110075042373)
              ·
                refine ⟨520624045219145639070445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2776661574502110075042373 520624045219145639070445)
                ·
                  refine ⟨195234016957179614651417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 520624045219145639070445 195234016957179614651417)
                  ·
                    rfl

theorem cell21_855488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 4, 3].length) (baseStart_855488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_855488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_855488 prefixEnd_855488 := by exact prefixLift 855488
  have htrace : WordTrace (prefixWord ++ tailWord_855488) baseStart_855488 baseEnd_855488 := by
    simpa [prefixWord, tailWord_855488, baseEnd_855488] using wordTrace_append hprefix tailTrace_855488
  have hstable : (prefixWord ++ tailWord_855488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855488).length < 2 ^ (prefixWord ++ tailWord_855488).sum := by decide
  have hdescent : baseEnd_855488 < baseStart_855488 := by decide
  rcases family_descends (prefixWord ++ tailWord_855488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855502 : List Nat := [4, 1, 1, 1, 2, 1, 2, 5, 4]
def baseStart_855502 : Nat := 118140960795 + 855502 * 2 ^ 59
def prefixEnd_855502 : Nat := 4983230072969 + 3 ^ 40 * 855502 * 2
def baseEnd_855502 : Nat := 195237211947918701418055

theorem tailTrace_855502 : CollatzResearch.WordTrace tailWord_855502 prefixEnd_855502 195237211947918701418055 := by
  unfold tailWord_855502
  simp only [CollatzResearch.WordTrace]
  refine ⟨3900340168333729619306095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20801814231113224636299173 3900340168333729619306095)
  ·
    refine ⟨5850510252500594428959143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3900340168333729619306095 5850510252500594428959143)
    ·
      refine ⟨8775765378750891643438715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5850510252500594428959143 8775765378750891643438715)
      ·
        refine ⟨13163648068126337465158073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8775765378750891643438715 13163648068126337465158073)
        ·
          refine ⟨9872736051094753098868555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13163648068126337465158073 9872736051094753098868555)
          ·
            refine ⟨14809104076642129648302833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9872736051094753098868555 14809104076642129648302833)
            ·
              refine ⟨11106828057481597236227125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14809104076642129648302833 11106828057481597236227125)
              ·
                refine ⟨1041265130388899740896293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11106828057481597236227125 1041265130388899740896293)
                ·
                  refine ⟨195237211947918701418055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1041265130388899740896293 195237211947918701418055)
                  ·
                    rfl

theorem cell21_855502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_855502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_855502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_855502 prefixEnd_855502 := by exact prefixLift 855502
  have htrace : WordTrace (prefixWord ++ tailWord_855502) baseStart_855502 baseEnd_855502 := by
    simpa [prefixWord, tailWord_855502, baseEnd_855502] using wordTrace_append hprefix tailTrace_855502
  have hstable : (prefixWord ++ tailWord_855502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855502).length < 2 ^ (prefixWord ++ tailWord_855502).sum := by decide
  have hdescent : baseEnd_855502 < baseStart_855502 := by decide
  rcases family_descends (prefixWord ++ tailWord_855502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855553 : List Nat := [1, 2, 4, 1, 5, 1, 2, 1, 4]
def baseStart_855553 : Nat := 118140960795 + 855553 * 2 ^ 59
def prefixEnd_855553 : Nat := 4983230072969 + 3 ^ 40 * 855553 * 2
def baseEnd_855553 : Nat := 195248850842753946067951

theorem tailTrace_855553 : CollatzResearch.WordTrace tailWord_855553 prefixEnd_855553 195248850842753946067951 := by
  unfold tailWord_855553
  simp only [CollatzResearch.WordTrace]
  refine ⟨31204581469485072664555313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20803054312990048443036875 31204581469485072664555313)
  ·
    refine ⟨23403436102113804498416485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31204581469485072664555313 23403436102113804498416485)
    ·
      refine ⟨4388144269146338343453091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23403436102113804498416485 4388144269146338343453091)
      ·
        refine ⟨6582216403719507515179637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4388144269146338343453091 6582216403719507515179637)
        ·
          refine ⟨617082787848703829548091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6582216403719507515179637 617082787848703829548091)
          ·
            refine ⟨925624181773055744322137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617082787848703829548091 925624181773055744322137)
            ·
              refine ⟨694218136329791808241603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 925624181773055744322137 694218136329791808241603)
              ·
                refine ⟨1041327204494687712362405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 694218136329791808241603 1041327204494687712362405)
                ·
                  refine ⟨195248850842753946067951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1041327204494687712362405 195248850842753946067951)
                  ·
                    rfl

theorem cell21_855553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 4].length) (baseStart_855553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_855553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_855553 prefixEnd_855553 := by exact prefixLift 855553
  have htrace : WordTrace (prefixWord ++ tailWord_855553) baseStart_855553 baseEnd_855553 := by
    simpa [prefixWord, tailWord_855553, baseEnd_855553] using wordTrace_append hprefix tailTrace_855553
  have hstable : (prefixWord ++ tailWord_855553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855553).length < 2 ^ (prefixWord ++ tailWord_855553).sum := by decide
  have hdescent : baseEnd_855553 < baseStart_855553 := by decide
  rcases family_descends (prefixWord ++ tailWord_855553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855592 : List Nat := [2, 1, 5, 2, 11]
def baseStart_855592 : Nat := 118140960795 + 855592 * 2 ^ 59
def prefixEnd_855592 : Nat := 4983230072969 + 3 ^ 40 * 855592 * 2
def baseEnd_855592 : Nat := 2410589520667883270591

theorem tailTrace_855592 : CollatzResearch.WordTrace tailWord_855592 prefixEnd_855592 2410589520667883270591 := by
  unfold tailWord_855592
  simp only [CollatzResearch.WordTrace]
  refine ⟨15603001958171891162612515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20804002610895854883483353 15603001958171891162612515)
  ·
    refine ⟨23404502937257836743918773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15603001958171891162612515 23404502937257836743918773)
    ·
      refine ⟨2194172150367922194742385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23404502937257836743918773 2194172150367922194742385)
      ·
        refine ⟨1645629112775941646056789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2194172150367922194742385 1645629112775941646056789)
        ·
          refine ⟨2410589520667883270591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1645629112775941646056789 2410589520667883270591)
          ·
            rfl

theorem cell21_855592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 11].length) (baseStart_855592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_855592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_855592 prefixEnd_855592 := by exact prefixLift 855592
  have htrace : WordTrace (prefixWord ++ tailWord_855592) baseStart_855592 baseEnd_855592 := by
    simpa [prefixWord, tailWord_855592, baseEnd_855592] using wordTrace_append hprefix tailTrace_855592
  have hstable : (prefixWord ++ tailWord_855592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855592).length < 2 ^ (prefixWord ++ tailWord_855592).sum := by decide
  have hdescent : baseEnd_855592 < baseStart_855592 := by decide
  rcases family_descends (prefixWord ++ tailWord_855592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855598 : List Nat := [4, 1, 3, 1, 2, 1, 4, 2, 3]
def baseStart_855598 : Nat := 118140960795 + 855598 * 2 ^ 59
def prefixEnd_855598 : Nat := 4983230072969 + 3 ^ 40 * 855598 * 2
def baseEnd_855598 : Nat := 195259120455843867817859

theorem tailTrace_855598 : CollatzResearch.WordTrace tailWord_855598 prefixEnd_855598 195259120455843867817859 := by
  unfold tailWord_855598
  simp only [CollatzResearch.WordTrace]
  refine ⟨3900777844290255668742931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20804148502881363566628965 3900777844290255668742931)
  ·
    refine ⟨5851166766435383503114397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3900777844290255668742931 5851166766435383503114397)
    ·
      refine ⟨2194187537413268813667899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5851166766435383503114397 2194187537413268813667899)
      ·
        refine ⟨3291281306119903220501849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2194187537413268813667899 3291281306119903220501849)
        ·
          refine ⟨2468460979589927415376387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3291281306119903220501849 2468460979589927415376387)
          ·
            refine ⟨3702691469384891123064581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2468460979589927415376387 3702691469384891123064581)
            ·
              refine ⟨694254650509667085574609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3702691469384891123064581 694254650509667085574609)
              ·
                refine ⟨520690987882250314180957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 694254650509667085574609 520690987882250314180957)
                ·
                  refine ⟨195259120455843867817859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 520690987882250314180957 195259120455843867817859)
                  ·
                    rfl

theorem cell21_855598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_855598 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_855598 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_855598 prefixEnd_855598 := by exact prefixLift 855598
  have htrace : WordTrace (prefixWord ++ tailWord_855598) baseStart_855598 baseEnd_855598 := by
    simpa [prefixWord, tailWord_855598, baseEnd_855598] using wordTrace_append hprefix tailTrace_855598
  have hstable : (prefixWord ++ tailWord_855598).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855598).length < 2 ^ (prefixWord ++ tailWord_855598).sum := by decide
  have hdescent : baseEnd_855598 < baseStart_855598 := by decide
  rcases family_descends (prefixWord ++ tailWord_855598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855609 : List Nat := [1, 2, 1, 5, 1, 4, 1, 6]
def baseStart_855609 : Nat := 118140960795 + 855609 * 2 ^ 59
def prefixEnd_855609 : Nat := 4983230072969 + 3 ^ 40 * 855609 * 2
def baseEnd_855609 : Nat := 65087210268570097711501

theorem tailTrace_855609 : CollatzResearch.WordTrace tailWord_855609 prefixEnd_855609 65087210268570097711501 := by
  unfold tailWord_855609
  simp only [CollatzResearch.WordTrace]
  refine ⟨31206623957282194228593881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20804415971521462819062587 31206623957282194228593881)
  ·
    refine ⟨23404967967961645671445411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31206623957282194228593881 23404967967961645671445411)
    ·
      refine ⟨35107451951942468507168117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23404967967961645671445411 35107451951942468507168117)
      ·
        refine ⟨3291323620494606422547011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35107451951942468507168117 3291323620494606422547011)
        ·
          refine ⟨4936985430741909633820517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3291323620494606422547011 4936985430741909633820517)
          ·
            refine ⟨925684768264108056341347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4936985430741909633820517 925684768264108056341347)
            ·
              refine ⟨1388527152396162084512021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 925684768264108056341347 1388527152396162084512021)
              ·
                refine ⟨65087210268570097711501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1388527152396162084512021 65087210268570097711501)
                ·
                  rfl

theorem cell21_855609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 6].length) (baseStart_855609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_855609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_855609 prefixEnd_855609 := by exact prefixLift 855609
  have htrace : WordTrace (prefixWord ++ tailWord_855609) baseStart_855609 baseEnd_855609 := by
    simpa [prefixWord, tailWord_855609, baseEnd_855609] using wordTrace_append hprefix tailTrace_855609
  have hstable : (prefixWord ++ tailWord_855609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855609).length < 2 ^ (prefixWord ++ tailWord_855609).sum := by decide
  have hdescent : baseEnd_855609 < baseStart_855609 := by decide
  rcases family_descends (prefixWord ++ tailWord_855609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855637 : List Nat := [1, 3, 2, 2, 1, 1, 1, 4, 6]
def baseStart_855637 : Nat := 118140960795 + 855637 * 2 ^ 59
def prefixEnd_855637 : Nat := 4983230072969 + 3 ^ 40 * 855637 * 2
def baseEnd_855637 : Nat := 195268020787188466667779

theorem tailTrace_855637 : CollatzResearch.WordTrace tailWord_855637 prefixEnd_855637 195268020787188466667779 := by
  unfold tailWord_855637
  simp only [CollatzResearch.WordTrace]
  refine ⟨31207645201180755010613165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20805096800787170007075443 31207645201180755010613165)
  ·
    refine ⟨11702866950442783128979937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31207645201180755010613165 11702866950442783128979937)
    ·
      refine ⟨8777150212832087346734953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11702866950442783128979937 8777150212832087346734953)
      ·
        refine ⟨6582862659624065510051215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8777150212832087346734953 6582862659624065510051215)
        ·
          refine ⟨9874293989436098265076823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6582862659624065510051215 9874293989436098265076823)
          ·
            refine ⟨14811440984154147397615235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9874293989436098265076823 14811440984154147397615235)
            ·
              refine ⟨22217161476231221096422853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14811440984154147397615235 22217161476231221096422853)
              ·
                refine ⟨4165717776793353955579285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22217161476231221096422853 4165717776793353955579285)
                ·
                  refine ⟨195268020787188466667779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4165717776793353955579285 195268020787188466667779)
                  ·
                    rfl

theorem cell21_855637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_855637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_855637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_855637 prefixEnd_855637 := by exact prefixLift 855637
  have htrace : WordTrace (prefixWord ++ tailWord_855637) baseStart_855637 baseEnd_855637 := by
    simpa [prefixWord, tailWord_855637, baseEnd_855637] using wordTrace_append hprefix tailTrace_855637
  have hstable : (prefixWord ++ tailWord_855637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855637).length < 2 ^ (prefixWord ++ tailWord_855637).sum := by decide
  have hdescent : baseEnd_855637 < baseStart_855637 := by decide
  rcases family_descends (prefixWord ++ tailWord_855637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855716 : List Nat := [2, 3, 1, 2, 2, 4, 1, 1, 5]
def baseStart_855716 : Nat := 118140960795 + 855716 * 2 ^ 59
def prefixEnd_855716 : Nat := 4983230072969 + 3 ^ 40 * 855716 * 2
def baseEnd_855716 : Nat := 195286049663501884850951

theorem tailTrace_855716 : CollatzResearch.WordTrace tailWord_855716 prefixEnd_855716 195286049663501884850951 := by
  unfold tailWord_855716
  simp only [CollatzResearch.WordTrace]
  refine ⟨15605263283947275751369501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20807017711929701001826001 15605263283947275751369501)
  ·
    refine ⟨5851973731480228406763563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15605263283947275751369501 5851973731480228406763563)
    ·
      refine ⟨8777960597220342610145345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5851973731480228406763563 8777960597220342610145345)
      ·
        refine ⟨6583470447915256957609009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8777960597220342610145345 6583470447915256957609009)
        ·
          refine ⟨4937602835936442718206757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6583470447915256957609009 4937602835936442718206757)
          ·
            refine ⟨925800531738083009663767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4937602835936442718206757 925800531738083009663767)
            ·
              refine ⟨1388700797607124514495651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 925800531738083009663767 1388700797607124514495651)
              ·
                refine ⟨2083051196410686771743477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1388700797607124514495651 2083051196410686771743477)
                ·
                  refine ⟨195286049663501884850951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2083051196410686771743477 195286049663501884850951)
                  ·
                    rfl

theorem cell21_855716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_855716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_855716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_855716 prefixEnd_855716 := by exact prefixLift 855716
  have htrace : WordTrace (prefixWord ++ tailWord_855716) baseStart_855716 baseEnd_855716 := by
    simpa [prefixWord, tailWord_855716, baseEnd_855716] using wordTrace_append hprefix tailTrace_855716
  have hstable : (prefixWord ++ tailWord_855716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855716).length < 2 ^ (prefixWord ++ tailWord_855716).sum := by decide
  have hdescent : baseEnd_855716 < baseStart_855716 := by decide
  rcases family_descends (prefixWord ++ tailWord_855716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855868 : List Nat := [2, 2, 2, 2, 1, 1, 5, 3, 3]
def baseStart_855868 : Nat := 118140960795 + 855868 * 2 ^ 59
def prefixEnd_855868 : Nat := 4983230072969 + 3 ^ 40 * 855868 * 2
def baseEnd_855868 : Nat := 195320738134383398317307

theorem tailTrace_855868 : CollatzResearch.WordTrace tailWord_855868 prefixEnd_855868 195320738134383398317307 := by
  unfold tailWord_855868
  simp only [CollatzResearch.WordTrace]
  refine ⟨15608035231671940731136129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20810713642229254308181505 15608035231671940731136129)
  ·
    refine ⟨11706026423753955548352097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15608035231671940731136129 11706026423753955548352097)
    ·
      refine ⟨8779519817815466661264073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11706026423753955548352097 8779519817815466661264073)
      ·
        refine ⟨6584639863361599995948055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8779519817815466661264073 6584639863361599995948055)
        ·
          refine ⟨9876959795042399993922083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6584639863361599995948055 9876959795042399993922083)
          ·
            refine ⟨14815439692563599990883125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9876959795042399993922083 14815439692563599990883125)
            ·
              refine ⟨1388947471177837499145293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14815439692563599990883125 1388947471177837499145293)
              ·
                refine ⟨520855301691689062179485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1388947471177837499145293 520855301691689062179485)
                ·
                  refine ⟨195320738134383398317307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 520855301691689062179485 195320738134383398317307)
                  ·
                    rfl

theorem cell21_855868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 3, 3].length) (baseStart_855868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_855868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_855868 prefixEnd_855868 := by exact prefixLift 855868
  have htrace : WordTrace (prefixWord ++ tailWord_855868) baseStart_855868 baseEnd_855868 := by
    simpa [prefixWord, tailWord_855868, baseEnd_855868] using wordTrace_append hprefix tailTrace_855868
  have hstable : (prefixWord ++ tailWord_855868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855868).length < 2 ^ (prefixWord ++ tailWord_855868).sum := by decide
  have hdescent : baseEnd_855868 < baseStart_855868 := by decide
  rcases family_descends (prefixWord ++ tailWord_855868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855879 : List Nat := [1, 1, 4, 1, 2, 1, 11]
def baseStart_855879 : Nat := 118140960795 + 855879 * 2 ^ 59
def prefixEnd_855879 : Nat := 4983230072969 + 3 ^ 40 * 855879 * 2
def baseEnd_855879 : Nat := 21702583164916647070439

theorem tailTrace_855879 : CollatzResearch.WordTrace tailWord_855879 prefixEnd_855879 21702583164916647070439 := by
  unfold tailWord_855879
  simp only [CollatzResearch.WordTrace]
  refine ⟨31216471666304030340922691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20810981110869353560615127 31216471666304030340922691)
  ·
    refine ⟨46824707499456045511384037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31216471666304030340922691 46824707499456045511384037)
    ·
      refine ⟨8779632656148008533384507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46824707499456045511384037 8779632656148008533384507)
      ·
        refine ⟨13169448984222012800076761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8779632656148008533384507 13169448984222012800076761)
        ·
          refine ⟨9877086738166509600057571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13169448984222012800076761 9877086738166509600057571)
          ·
            refine ⟨14815630107249764400086357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9877086738166509600057571 14815630107249764400086357)
            ·
              refine ⟨21702583164916647070439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 14815630107249764400086357 21702583164916647070439)
              ·
                rfl

theorem cell21_855879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 11].length) (baseStart_855879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_855879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_855879 prefixEnd_855879 := by exact prefixLift 855879
  have htrace : WordTrace (prefixWord ++ tailWord_855879) baseStart_855879 baseEnd_855879 := by
    simpa [prefixWord, tailWord_855879, baseEnd_855879] using wordTrace_append hprefix tailTrace_855879
  have hstable : (prefixWord ++ tailWord_855879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855879).length < 2 ^ (prefixWord ++ tailWord_855879).sum := by decide
  have hdescent : baseEnd_855879 < baseStart_855879 := by decide
  rcases family_descends (prefixWord ++ tailWord_855879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855885 : List Nat := [1, 6, 1, 2, 1, 3, 1, 1, 5]
def baseStart_855885 : Nat := 118140960795 + 855885 * 2 ^ 59
def prefixEnd_855885 : Nat := 4983230072969 + 3 ^ 40 * 855885 * 2
def baseEnd_855885 : Nat := 195324617765995146533939

theorem tailTrace_855885 : CollatzResearch.WordTrace tailWord_855885 prefixEnd_855885 195324617765995146533939 := by
  unfold tailWord_855885
  simp only [CollatzResearch.WordTrace]
  refine ⟨31216690504282293365641109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20811127002854862243760739 31216690504282293365641109)
  ·
    refine ⟨1463282367388232501514427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31216690504282293365641109 1463282367388232501514427)
    ·
      refine ⟨2194923551082348752271641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1463282367388232501514427 2194923551082348752271641)
      ·
        refine ⟨1646192663311761564203731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2194923551082348752271641 1646192663311761564203731)
        ·
          refine ⟨2469288994967642346305597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1646192663311761564203731 2469288994967642346305597)
          ·
            refine ⟨925983373112865879864599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2469288994967642346305597 925983373112865879864599)
            ·
              refine ⟨1388975059669298819796899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 925983373112865879864599 1388975059669298819796899)
              ·
                refine ⟨2083462589503948229695349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1388975059669298819796899 2083462589503948229695349)
                ·
                  refine ⟨195324617765995146533939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2083462589503948229695349 195324617765995146533939)
                  ·
                    rfl

theorem cell21_855885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_855885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_855885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_855885 prefixEnd_855885 := by exact prefixLift 855885
  have htrace : WordTrace (prefixWord ++ tailWord_855885) baseStart_855885 baseEnd_855885 := by
    simpa [prefixWord, tailWord_855885, baseEnd_855885] using wordTrace_append hprefix tailTrace_855885
  have hstable : (prefixWord ++ tailWord_855885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855885).length < 2 ^ (prefixWord ++ tailWord_855885).sum := by decide
  have hdescent : baseEnd_855885 < baseStart_855885 := by decide
  rcases family_descends (prefixWord ++ tailWord_855885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856054 : List Nat := [5, 1, 1, 1, 4, 1, 3, 2, 3]
def baseStart_856054 : Nat := 118140960795 + 856054 * 2 ^ 59
def prefixEnd_856054 : Nat := 4983230072969 + 3 ^ 40 * 856054 * 2
def baseEnd_856054 : Nat := 195363185868488408216927

theorem tailTrace_856054 : CollatzResearch.WordTrace tailWord_856054 prefixEnd_856054 195363185868488408216927 := by
  unfold tailWord_856054
  simp only [CollatzResearch.WordTrace]
  refine ⟨1951428402541877201783951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20815236293780023485695477 1951428402541877201783951)
  ·
    refine ⟨2927142603812815802675927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1951428402541877201783951 2927142603812815802675927)
    ·
      refine ⟨4390713905719223704013891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2927142603812815802675927 4390713905719223704013891)
      ·
        refine ⟨6586070858578835556020837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4390713905719223704013891 6586070858578835556020837)
        ·
          refine ⟨1234888285983531666753907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6586070858578835556020837 1234888285983531666753907)
          ·
            refine ⟨1852332428975297500130861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1234888285983531666753907 1852332428975297500130861)
            ·
              refine ⟨694624660865736562549073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1852332428975297500130861 694624660865736562549073)
              ·
                refine ⟨520968495649302421911805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 694624660865736562549073 520968495649302421911805)
                ·
                  refine ⟨195363185868488408216927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 520968495649302421911805 195363185868488408216927)
                  ·
                    rfl

theorem cell21_856054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_856054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_856054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_856054 prefixEnd_856054 := by exact prefixLift 856054
  have htrace : WordTrace (prefixWord ++ tailWord_856054) baseStart_856054 baseEnd_856054 := by
    simpa [prefixWord, tailWord_856054, baseEnd_856054] using wordTrace_append hprefix tailTrace_856054
  have hstable : (prefixWord ++ tailWord_856054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856054).length < 2 ^ (prefixWord ++ tailWord_856054).sum := by decide
  have hdescent : baseEnd_856054 < baseStart_856054 := by decide
  rcases family_descends (prefixWord ++ tailWord_856054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856110 : List Nat := [4, 1, 3, 1, 1, 2, 1, 4, 4]
def baseStart_856110 : Nat := 118140960795 + 856110 * 2 ^ 59
def prefixEnd_856110 : Nat := 4983230072969 + 3 ^ 40 * 856110 * 2
def baseEnd_856110 : Nat := 195375965831444755283479

theorem tailTrace_856110 : CollatzResearch.WordTrace tailWord_856110 prefixEnd_856110 195375965831444755283479 := by
  unfold tailWord_856110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3903112116058394599072723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20816597952311437861721189 3903112116058394599072723)
  ·
    refine ⟨5854668174087591898609085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3903112116058394599072723 5854668174087591898609085)
    ·
      refine ⟨2195500565282846961978407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5854668174087591898609085 2195500565282846961978407)
      ·
        refine ⟨3293250847924270442967611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2195500565282846961978407 3293250847924270442967611)
        ·
          refine ⟨4939876271886405664451417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3293250847924270442967611 4939876271886405664451417)
          ·
            refine ⟨3704907203914804248338563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4939876271886405664451417 3704907203914804248338563)
            ·
              refine ⟨5557360805872206372507845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3704907203914804248338563 5557360805872206372507845)
              ·
                refine ⟨1042005151101038694845221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5557360805872206372507845 1042005151101038694845221)
                ·
                  refine ⟨195375965831444755283479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1042005151101038694845221 195375965831444755283479)
                  ·
                    rfl

theorem cell21_856110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_856110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_856110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_856110 prefixEnd_856110 := by exact prefixLift 856110
  have htrace : WordTrace (prefixWord ++ tailWord_856110) baseStart_856110 baseEnd_856110 := by
    simpa [prefixWord, tailWord_856110, baseEnd_856110] using wordTrace_append hprefix tailTrace_856110
  have hstable : (prefixWord ++ tailWord_856110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856110).length < 2 ^ (prefixWord ++ tailWord_856110).sum := by decide
  have hdescent : baseEnd_856110 < baseStart_856110 := by decide
  rcases family_descends (prefixWord ++ tailWord_856110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856113 : List Nat := [1, 2, 2, 3, 1, 5, 2, 2, 3]
def baseStart_856113 : Nat := 118140960795 + 856113 * 2 ^ 59
def prefixEnd_856113 : Nat := 4983230072969 + 3 ^ 40 * 856113 * 2
def baseEnd_856113 : Nat := 195376650472317416733473

theorem tailTrace_856113 : CollatzResearch.WordTrace tailWord_856113 prefixEnd_856113 195376650472317416733473 := by
  unfold tailWord_856113
  simp only [CollatzResearch.WordTrace]
  refine ⟨31225006347456288304940993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20816670898304192203293995 31225006347456288304940993)
  ·
    refine ⟨23418754760592216228705745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31225006347456288304940993 23418754760592216228705745)
    ·
      refine ⟨17564066070444162171529309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23418754760592216228705745 17564066070444162171529309)
      ·
        refine ⟨6586524776416560814323491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17564066070444162171529309 6586524776416560814323491)
        ·
          refine ⟨9879787164624841221485237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6586524776416560814323491 9879787164624841221485237)
          ·
            refine ⟨926230046683578864514241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9879787164624841221485237 926230046683578864514241)
            ·
              refine ⟨694672535012684148385681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 926230046683578864514241 694672535012684148385681)
              ·
                refine ⟨521004401259513111289261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 694672535012684148385681 521004401259513111289261)
                ·
                  refine ⟨195376650472317416733473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 521004401259513111289261 195376650472317416733473)
                  ·
                    rfl

theorem cell21_856113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 2, 3].length) (baseStart_856113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_856113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_856113 prefixEnd_856113 := by exact prefixLift 856113
  have htrace : WordTrace (prefixWord ++ tailWord_856113) baseStart_856113 baseEnd_856113 := by
    simpa [prefixWord, tailWord_856113, baseEnd_856113] using wordTrace_append hprefix tailTrace_856113
  have hstable : (prefixWord ++ tailWord_856113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856113).length < 2 ^ (prefixWord ++ tailWord_856113).sum := by decide
  have hdescent : baseEnd_856113 < baseStart_856113 := by decide
  rcases family_descends (prefixWord ++ tailWord_856113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856141 : List Nat := [1, 6, 1, 1, 1, 1, 5, 5]
def baseStart_856141 : Nat := 118140960795 + 856141 * 2 ^ 59
def prefixEnd_856141 : Nat := 4983230072969 + 3 ^ 40 * 856141 * 2
def baseEnd_856141 : Nat := 65127680151265196755583

theorem tailTrace_856141 : CollatzResearch.WordTrace tailWord_856141 prefixEnd_856141 65127680151265196755583 := by
  unfold tailWord_856141
  simp only [CollatzResearch.WordTrace]
  refine ⟨31226027591354849086960277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20817351727569899391306851 31226027591354849086960277)
  ·
    refine ⟨1463720043344758550951263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31226027591354849086960277 1463720043344758550951263)
    ·
      refine ⟨2195580065017137826426895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1463720043344758550951263 2195580065017137826426895)
      ·
        refine ⟨3293370097525706739640343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2195580065017137826426895 3293370097525706739640343)
        ·
          refine ⟨4940055146288560109460515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3293370097525706739640343 4940055146288560109460515)
          ·
            refine ⟨7410082719432840164190773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4940055146288560109460515 7410082719432840164190773)
            ·
              refine ⟨694695254946828765392885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7410082719432840164190773 694695254946828765392885)
              ·
                refine ⟨65127680151265196755583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 694695254946828765392885 65127680151265196755583)
                ·
                  rfl

theorem cell21_856141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 5].length) (baseStart_856141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_856141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_856141 prefixEnd_856141 := by exact prefixLift 856141
  have htrace : WordTrace (prefixWord ++ tailWord_856141) baseStart_856141 baseEnd_856141 := by
    simpa [prefixWord, tailWord_856141, baseEnd_856141] using wordTrace_append hprefix tailTrace_856141
  have hstable : (prefixWord ++ tailWord_856141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856141).length < 2 ^ (prefixWord ++ tailWord_856141).sum := by decide
  have hdescent : baseEnd_856141 < baseStart_856141 := by decide
  rcases family_descends (prefixWord ++ tailWord_856141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856158 : List Nat := [4, 4, 1, 1, 2, 1, 8]
def baseStart_856158 : Nat := 118140960795 + 856158 * 2 ^ 59
def prefixEnd_856158 : Nat := 4983230072969 + 3 ^ 40 * 856158 * 2
def baseEnd_856158 : Nat := 21709657787267482053709

theorem tailTrace_856158 : CollatzResearch.WordTrace tailWord_856158 prefixEnd_856158 21709657787267482053709 := by
  unfold tailWord_856158
  simp only [CollatzResearch.WordTrace]
  refine ⟨3903330954036657623791141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20817765088195507326886085 3903330954036657623791141)
  ·
    refine ⟨731874553881873304460839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3903330954036657623791141 731874553881873304460839)
    ·
      refine ⟨1097811830822809956691259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 731874553881873304460839 1097811830822809956691259)
      ·
        refine ⟨1646717746234214935036889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1097811830822809956691259 1646717746234214935036889)
        ·
          refine ⟨1235038309675661201277667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1646717746234214935036889 1235038309675661201277667)
          ·
            refine ⟨1852557464513491801916501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1235038309675661201277667 1852557464513491801916501)
            ·
              refine ⟨21709657787267482053709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1852557464513491801916501 21709657787267482053709)
              ·
                rfl

theorem cell21_856158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 8].length) (baseStart_856158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_856158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_856158 prefixEnd_856158 := by exact prefixLift 856158
  have htrace : WordTrace (prefixWord ++ tailWord_856158) baseStart_856158 baseEnd_856158 := by
    simpa [prefixWord, tailWord_856158, baseEnd_856158] using wordTrace_append hprefix tailTrace_856158
  have hstable : (prefixWord ++ tailWord_856158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856158).length < 2 ^ (prefixWord ++ tailWord_856158).sum := by decide
  have hdescent : baseEnd_856158 < baseStart_856158 := by decide
  rcases family_descends (prefixWord ++ tailWord_856158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856200 : List Nat := [2, 1, 3, 4, 1, 2, 1, 7]
def baseStart_856200 : Nat := 118140960795 + 856200 * 2 ^ 59
def prefixEnd_856200 : Nat := 4983230072969 + 3 ^ 40 * 856200 * 2
def baseEnd_856200 : Nat := 65132168352541532927765

theorem tailTrace_856200 : CollatzResearch.WordTrace tailWord_856200 prefixEnd_856200 65132168352541532927765 := by
  unfold tailWord_856200
  simp only [CollatzResearch.WordTrace]
  refine ⟨15614089749070551081679027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20818786332094068108905369 15614089749070551081679027)
  ·
    refine ⟨23421134623605826622518541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15614089749070551081679027 23421134623605826622518541)
    ·
      refine ⟨8782925483852184983444453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23421134623605826622518541 8782925483852184983444453)
      ·
        refine ⟨1646798528222284684395835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8782925483852184983444453 1646798528222284684395835)
        ·
          refine ⟨2470197792333427026593753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1646798528222284684395835 2470197792333427026593753)
          ·
            refine ⟨1852648344250070269945315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2470197792333427026593753 1852648344250070269945315)
            ·
              refine ⟨2778972516375105404917973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1852648344250070269945315 2778972516375105404917973)
              ·
                refine ⟨65132168352541532927765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2778972516375105404917973 65132168352541532927765)
                ·
                  rfl

theorem cell21_856200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 7].length) (baseStart_856200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_856200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_856200 prefixEnd_856200 := by exact prefixLift 856200
  have htrace : WordTrace (prefixWord ++ tailWord_856200) baseStart_856200 baseEnd_856200 := by
    simpa [prefixWord, tailWord_856200, baseEnd_856200] using wordTrace_append hprefix tailTrace_856200
  have hstable : (prefixWord ++ tailWord_856200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856200).length < 2 ^ (prefixWord ++ tailWord_856200).sum := by decide
  have hdescent : baseEnd_856200 < baseStart_856200 := by decide
  rcases family_descends (prefixWord ++ tailWord_856200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856206 : List Nat := [4, 1, 1, 3, 4, 1, 1, 3, 3]
def baseStart_856206 : Nat := 118140960795 + 856206 * 2 ^ 59
def prefixEnd_856206 : Nat := 4983230072969 + 3 ^ 40 * 856206 * 2
def baseEnd_856206 : Nat := 195397874339369921683283

theorem tailTrace_856206 : CollatzResearch.WordTrace tailWord_856206 prefixEnd_856206 195397874339369921683283 := by
  unfold tailWord_856206
  simp only [CollatzResearch.WordTrace]
  refine ⟨3903549792014920648509559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20818932224079576792050981 3903549792014920648509559)
  ·
    refine ⟨5855324688022380972764339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3903549792014920648509559 5855324688022380972764339)
    ·
      refine ⟨8782987032033571459146509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5855324688022380972764339 8782987032033571459146509)
      ·
        refine ⟨3293620137012589297179941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8782987032033571459146509 3293620137012589297179941)
        ·
          refine ⟨617553775689860493221239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3293620137012589297179941 617553775689860493221239)
          ·
            refine ⟨926330663534790739831859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617553775689860493221239 926330663534790739831859)
            ·
              refine ⟨1389495995302186109747789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 926330663534790739831859 1389495995302186109747789)
              ·
                refine ⟨521060998238319791155421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1389495995302186109747789 521060998238319791155421)
                ·
                  refine ⟨195397874339369921683283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 521060998238319791155421 195397874339369921683283)
                  ·
                    rfl

theorem cell21_856206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_856206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_856206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_856206 prefixEnd_856206 := by exact prefixLift 856206
  have htrace : WordTrace (prefixWord ++ tailWord_856206) baseStart_856206 baseEnd_856206 := by
    simpa [prefixWord, tailWord_856206, baseEnd_856206] using wordTrace_append hprefix tailTrace_856206
  have hstable : (prefixWord ++ tailWord_856206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856206).length < 2 ^ (prefixWord ++ tailWord_856206).sum := by decide
  have hdescent : baseEnd_856206 < baseStart_856206 := by decide
  rcases family_descends (prefixWord ++ tailWord_856206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856369 : List Nat := [1, 2, 2, 3, 4, 2, 2, 5]
def baseStart_856369 : Nat := 118140960795 + 856369 * 2 ^ 59
def prefixEnd_856369 : Nat := 4983230072969 + 3 ^ 40 * 856369 * 2
def baseEnd_856369 : Nat := 65145024386705953488761

theorem tailTrace_856369 : CollatzResearch.WordTrace tailWord_856369 prefixEnd_856369 65145024386705953488761 := by
  unfold tailWord_856369
  simp only [CollatzResearch.WordTrace]
  refine ⟨31234343434528844026260161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20822895623019229350840107 31234343434528844026260161)
  ·
    refine ⟨23425757575896633019695121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31234343434528844026260161 23425757575896633019695121)
    ·
      refine ⟨17569318181922474764771341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23425757575896633019695121 17569318181922474764771341)
      ·
        refine ⟨6588494318220928036789253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17569318181922474764771341 6588494318220928036789253)
        ·
          refine ⟨1235342684666424006897985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6588494318220928036789253 1235342684666424006897985)
          ·
            refine ⟨926507013499818005173489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1235342684666424006897985 926507013499818005173489)
            ·
              refine ⟨694880260124863503880117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 926507013499818005173489 694880260124863503880117)
              ·
                refine ⟨65145024386705953488761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 694880260124863503880117 65145024386705953488761)
                ·
                  rfl

theorem cell21_856369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 5].length) (baseStart_856369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_856369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_856369 prefixEnd_856369 := by exact prefixLift 856369
  have htrace : WordTrace (prefixWord ++ tailWord_856369) baseStart_856369 baseEnd_856369 := by
    simpa [prefixWord, tailWord_856369, baseEnd_856369] using wordTrace_append hprefix tailTrace_856369
  have hstable : (prefixWord ++ tailWord_856369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856369).length < 2 ^ (prefixWord ++ tailWord_856369).sum := by decide
  have hdescent : baseEnd_856369 < baseStart_856369 := by decide
  rcases family_descends (prefixWord ++ tailWord_856369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856380 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 8]
def baseStart_856380 : Nat := 118140960795 + 856380 * 2 ^ 59
def prefixEnd_856380 : Nat := 4983230072969 + 3 ^ 40 * 856380 * 2
def baseEnd_856380 : Nat := 195437583509984285782927

theorem tailTrace_856380 : CollatzResearch.WordTrace tailWord_856380 prefixEnd_856380 195437583509984285782927 := by
  unfold tailWord_856380
  simp only [CollatzResearch.WordTrace]
  refine ⟨15617372318744496452455297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20823163091659328603273729 15617372318744496452455297)
  ·
    refine ⟨11713029239058372339341473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15617372318744496452455297 11713029239058372339341473)
    ·
      refine ⟨8784771929293779254506105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11713029239058372339341473 8784771929293779254506105)
      ·
        refine ⟨6588578946970334440879579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8784771929293779254506105 6588578946970334440879579)
        ·
          refine ⟨9882868420455501661319369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6588578946970334440879579 9882868420455501661319369)
          ·
            refine ⟨7412151315341626245989527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9882868420455501661319369 7412151315341626245989527)
            ·
              refine ⟨11118226973012439368984291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7412151315341626245989527 11118226973012439368984291)
              ·
                refine ⟨16677340459518659053476437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11118226973012439368984291 16677340459518659053476437)
                ·
                  refine ⟨195437583509984285782927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16677340459518659053476437 195437583509984285782927)
                  ·
                    rfl

theorem cell21_856380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_856380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_856380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_856380 prefixEnd_856380 := by exact prefixLift 856380
  have htrace : WordTrace (prefixWord ++ tailWord_856380) baseStart_856380 baseEnd_856380 := by
    simpa [prefixWord, tailWord_856380, baseEnd_856380] using wordTrace_append hprefix tailTrace_856380
  have hstable : (prefixWord ++ tailWord_856380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856380).length < 2 ^ (prefixWord ++ tailWord_856380).sum := by decide
  have hdescent : baseEnd_856380 < baseStart_856380 := by decide
  rcases family_descends (prefixWord ++ tailWord_856380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856400 : List Nat := [2, 1, 1, 1, 1, 7, 3, 2, 3]
def baseStart_856400 : Nat := 118140960795 + 856400 * 2 ^ 59
def prefixEnd_856400 : Nat := 4983230072969 + 3 ^ 40 * 856400 * 2
def baseEnd_856400 : Nat := 195442147782468695449553

theorem tailTrace_856400 : CollatzResearch.WordTrace tailWord_856400 prefixEnd_856400 195442147782468695449553 := by
  unfold tailWord_856400
  simp only [CollatzResearch.WordTrace]
  refine ⟨15617737048708268160319327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20823649398277690880425769 15617737048708268160319327)
  ·
    refine ⟨23426605573062402240478991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15617737048708268160319327 23426605573062402240478991)
    ·
      refine ⟨35139908359593603360718487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23426605573062402240478991 35139908359593603360718487)
      ·
        refine ⟨52709862539390405041077731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35139908359593603360718487 52709862539390405041077731)
        ·
          refine ⟨79064793809085607561616597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52709862539390405041077731 79064793809085607561616597)
          ·
            refine ⟨1853081104900443927225389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 79064793809085607561616597 1853081104900443927225389)
            ·
              refine ⟨694905414337666472709521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1853081104900443927225389 694905414337666472709521)
              ·
                refine ⟨521179060753249854532141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 694905414337666472709521 521179060753249854532141)
                ·
                  refine ⟨195442147782468695449553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 521179060753249854532141 195442147782468695449553)
                  ·
                    rfl

theorem cell21_856400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 2, 3].length) (baseStart_856400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_856400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_856400 prefixEnd_856400 := by exact prefixLift 856400
  have htrace : WordTrace (prefixWord ++ tailWord_856400) baseStart_856400 baseEnd_856400 := by
    simpa [prefixWord, tailWord_856400, baseEnd_856400] using wordTrace_append hprefix tailTrace_856400
  have hstable : (prefixWord ++ tailWord_856400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856400).length < 2 ^ (prefixWord ++ tailWord_856400).sum := by decide
  have hdescent : baseEnd_856400 < baseStart_856400 := by decide
  rcases family_descends (prefixWord ++ tailWord_856400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856425 : List Nat := [1, 2, 1, 1, 1, 3, 4, 1, 7]
def baseStart_856425 : Nat := 118140960795 + 856425 * 2 ^ 59
def prefixEnd_856425 : Nat := 4983230072969 + 3 ^ 40 * 856425 * 2
def baseEnd_856425 : Nat := 195447853123074207532835

theorem tailTrace_856425 : CollatzResearch.WordTrace tailWord_856425 prefixEnd_856425 195447853123074207532835 := by
  unfold tailWord_856425
  simp only [CollatzResearch.WordTrace]
  refine ⟨31236385922325965590298729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20824257281550643726865819 31236385922325965590298729)
  ·
    refine ⟨23427289441744474192724047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31236385922325965590298729 23427289441744474192724047)
    ·
      refine ⟨35140934162616711289086071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23427289441744474192724047 35140934162616711289086071)
      ·
        refine ⟨52711401243925066933629107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35140934162616711289086071 52711401243925066933629107)
        ·
          refine ⟨79067101865887600400443661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52711401243925066933629107 79067101865887600400443661)
          ·
            refine ⟨29650163199707850150166373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79067101865887600400443661 29650163199707850150166373)
            ·
              refine ⟨5559405599945221903156195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29650163199707850150166373 5559405599945221903156195)
              ·
                refine ⟨8339108399917832854734293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5559405599945221903156195 8339108399917832854734293)
                ·
                  refine ⟨195447853123074207532835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8339108399917832854734293 195447853123074207532835)
                  ·
                    rfl

theorem cell21_856425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 7].length) (baseStart_856425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_856425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_856425 prefixEnd_856425 := by exact prefixLift 856425
  have htrace : WordTrace (prefixWord ++ tailWord_856425) baseStart_856425 baseEnd_856425 := by
    simpa [prefixWord, tailWord_856425, baseEnd_856425] using wordTrace_append hprefix tailTrace_856425
  have hstable : (prefixWord ++ tailWord_856425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856425).length < 2 ^ (prefixWord ++ tailWord_856425).sum := by decide
  have hdescent : baseEnd_856425 < baseStart_856425 := by decide
  rcases family_descends (prefixWord ++ tailWord_856425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856459 : List Nat := [1, 1, 1, 1, 4, 5, 1, 4, 3]
def baseStart_856459 : Nat := 118140960795 + 856459 * 2 ^ 59
def prefixEnd_856459 : Nat := 4983230072969 + 3 ^ 40 * 856459 * 2
def baseEnd_856459 : Nat := 195455612386297703966099

theorem tailTrace_856459 : CollatzResearch.WordTrace tailWord_856459 prefixEnd_856459 195455612386297703966099 := by
  unfold tailWord_856459
  simp only [CollatzResearch.WordTrace]
  refine ⟨31237626004202789397036431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20825084002801859598024287 31237626004202789397036431)
  ·
    refine ⟨46856439006304184095554647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31237626004202789397036431 46856439006304184095554647)
    ·
      refine ⟨70284658509456276143331971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46856439006304184095554647 70284658509456276143331971)
      ·
        refine ⟨105426987764184414214997957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70284658509456276143331971 105426987764184414214997957)
        ·
          refine ⟨19767560205784577665312117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105426987764184414214997957 19767560205784577665312117)
          ·
            refine ⟨1853208769292304156123011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19767560205784577665312117 1853208769292304156123011)
            ·
              refine ⟨2779813153938456234184517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1853208769292304156123011 2779813153938456234184517)
              ·
                refine ⟨521214966363460543909597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2779813153938456234184517 521214966363460543909597)
                ·
                  refine ⟨195455612386297703966099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 521214966363460543909597 195455612386297703966099)
                  ·
                    rfl

theorem cell21_856459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 4, 3].length) (baseStart_856459 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_856459 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_856459 prefixEnd_856459 := by exact prefixLift 856459
  have htrace : WordTrace (prefixWord ++ tailWord_856459) baseStart_856459 baseEnd_856459 := by
    simpa [prefixWord, tailWord_856459, baseEnd_856459] using wordTrace_append hprefix tailTrace_856459
  have hstable : (prefixWord ++ tailWord_856459).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856459).length < 2 ^ (prefixWord ++ tailWord_856459).sum := by decide
  have hdescent : baseEnd_856459 < baseStart_856459 := by decide
  rcases family_descends (prefixWord ++ tailWord_856459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856493 : List Nat := [1, 5, 2, 2, 2, 1, 2, 3, 3]
def baseStart_856493 : Nat := 118140960795 + 856493 * 2 ^ 59
def prefixEnd_856493 : Nat := 4983230072969 + 3 ^ 40 * 856493 * 2
def baseEnd_856493 : Nat := 195463371649521200399363

theorem tailTrace_856493 : CollatzResearch.WordTrace tailWord_856493 prefixEnd_856493 195463371649521200399363 := by
  unfold tailWord_856493
  simp only [CollatzResearch.WordTrace]
  refine ⟨31238866086079613203774133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20825910724053075469182755 31238866086079613203774133)
  ·
    refine ⟨2928643695569963737853825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31238866086079613203774133 2928643695569963737853825)
    ·
      refine ⟨2196482771677472803390369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2928643695569963737853825 2196482771677472803390369)
      ·
        refine ⟨1647362078758104602542777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2196482771677472803390369 1647362078758104602542777)
        ·
          refine ⟨1235521559068578451907083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1647362078758104602542777 1235521559068578451907083)
          ·
            refine ⟨1853282338602867677860625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1235521559068578451907083 1853282338602867677860625)
            ·
              refine ⟨1389961753952150758395469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1853282338602867677860625 1389961753952150758395469)
              ·
                refine ⟨521235657732056534398301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1389961753952150758395469 521235657732056534398301)
                ·
                  refine ⟨195463371649521200399363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 521235657732056534398301 195463371649521200399363)
                  ·
                    rfl

theorem cell21_856493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_856493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_856493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_856493 prefixEnd_856493 := by exact prefixLift 856493
  have htrace : WordTrace (prefixWord ++ tailWord_856493) baseStart_856493 baseEnd_856493 := by
    simpa [prefixWord, tailWord_856493, baseEnd_856493] using wordTrace_append hprefix tailTrace_856493
  have hstable : (prefixWord ++ tailWord_856493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856493).length < 2 ^ (prefixWord ++ tailWord_856493).sum := by decide
  have hdescent : baseEnd_856493 < baseStart_856493 := by decide
  rcases family_descends (prefixWord ++ tailWord_856493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856552 : List Nat := [2, 1, 4, 1, 1, 5, 1, 3, 3]
def baseStart_856552 : Nat := 118140960795 + 856552 * 2 ^ 59
def prefixEnd_856552 : Nat := 4983230072969 + 3 ^ 40 * 856552 * 2
def baseEnd_856552 : Nat := 195476836253350208915909

theorem tailTrace_856552 : CollatzResearch.WordTrace tailWord_856552 prefixEnd_856552 195476836253350208915909 := by
  unfold tailWord_856552
  simp only [CollatzResearch.WordTrace]
  refine ⟨15620508996432933140085955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20827345328577244186781273 15620508996432933140085955)
  ·
    refine ⟨23430763494649399710128933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15620508996432933140085955 23430763494649399710128933)
    ·
      refine ⟨4393268155246762445649175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23430763494649399710128933 4393268155246762445649175)
      ·
        refine ⟨6589902232870143668473763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4393268155246762445649175 6589902232870143668473763)
        ·
          refine ⟨9884853349305215502710645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6589902232870143668473763 9884853349305215502710645)
          ·
            refine ⟨926705001497363953379123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9884853349305215502710645 926705001497363953379123)
            ·
              refine ⟨1390057502246045930068685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 926705001497363953379123 1390057502246045930068685)
              ·
                refine ⟨521271563342267223775757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1390057502246045930068685 521271563342267223775757)
                ·
                  refine ⟨195476836253350208915909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 521271563342267223775757 195476836253350208915909)
                  ·
                    rfl

theorem cell21_856552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 3, 3].length) (baseStart_856552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_856552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_856552 prefixEnd_856552 := by exact prefixLift 856552
  have htrace : WordTrace (prefixWord ++ tailWord_856552) baseStart_856552 baseEnd_856552 := by
    simpa [prefixWord, tailWord_856552, baseEnd_856552] using wordTrace_append hprefix tailTrace_856552
  have hstable : (prefixWord ++ tailWord_856552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856552).length < 2 ^ (prefixWord ++ tailWord_856552).sum := by decide
  have hdescent : baseEnd_856552 < baseStart_856552 := by decide
  rcases family_descends (prefixWord ++ tailWord_856552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856580 : List Nat := [2, 3, 2, 3, 1, 2, 2, 6]
def baseStart_856580 : Nat := 118140960795 + 856580 * 2 ^ 59
def prefixEnd_856580 : Nat := 4983230072969 + 3 ^ 40 * 856580 * 2
def baseEnd_856580 : Nat := 65161075411609460816395

theorem tailTrace_856580 : CollatzResearch.WordTrace tailWord_856580 prefixEnd_856580 65161075411609460816395 := by
  unfold tailWord_856580
  simp only [CollatzResearch.WordTrace]
  refine ⟨15621019618382213531095597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20828026157842951374794129 15621019618382213531095597)
  ·
    refine ⟨5857882356893330074160849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15621019618382213531095597 5857882356893330074160849)
    ·
      refine ⟨4393411767669997555620637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5857882356893330074160849 4393411767669997555620637)
      ·
        refine ⟨1647529412876249083357739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4393411767669997555620637 1647529412876249083357739)
        ·
          refine ⟨2471294119314373625036609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1647529412876249083357739 2471294119314373625036609)
          ·
            refine ⟨1853470589485780218777457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2471294119314373625036609 1853470589485780218777457)
            ·
              refine ⟨1390102942114335164083093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1853470589485780218777457 1390102942114335164083093)
              ·
                refine ⟨65161075411609460816395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1390102942114335164083093 65161075411609460816395)
                ·
                  rfl

theorem cell21_856580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 6].length) (baseStart_856580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_856580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_856580 prefixEnd_856580 := by exact prefixLift 856580
  have htrace : WordTrace (prefixWord ++ tailWord_856580) baseStart_856580 baseEnd_856580 := by
    simpa [prefixWord, tailWord_856580, baseEnd_856580] using wordTrace_append hprefix tailTrace_856580
  have hstable : (prefixWord ++ tailWord_856580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856580).length < 2 ^ (prefixWord ++ tailWord_856580).sum := by decide
  have hdescent : baseEnd_856580 < baseStart_856580 := by decide
  rcases family_descends (prefixWord ++ tailWord_856580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856583 : List Nat := [1, 1, 4, 3, 3, 2, 2, 1, 4]
def baseStart_856583 : Nat := 118140960795 + 856583 * 2 ^ 59
def prefixEnd_856583 : Nat := 4983230072969 + 3 ^ 40 * 856583 * 2
def baseEnd_856583 : Nat := 195483910875701043899179

theorem tailTrace_856583 : CollatzResearch.WordTrace tailWord_856583 prefixEnd_856583 195483910875701043899179 := by
  unfold tailWord_856583
  simp only [CollatzResearch.WordTrace]
  refine ⟨31242148655753558574550403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20828099103835705716366935 31242148655753558574550403)
  ·
    refine ⟨46863222983630337861825605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31242148655753558574550403 46863222983630337861825605)
    ·
      refine ⟨8786854309430688349092301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46863222983630337861825605 8786854309430688349092301)
      ·
        refine ⟨3295070366036508130909613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8786854309430688349092301 3295070366036508130909613)
        ·
          refine ⟨1235651387263690549091105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3295070366036508130909613 1235651387263690549091105)
          ·
            refine ⟨926738540447767911818329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1235651387263690549091105 926738540447767911818329)
            ·
              refine ⟨695053905335825933863747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 926738540447767911818329 695053905335825933863747)
              ·
                refine ⟨1042580858003738900795621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 695053905335825933863747 1042580858003738900795621)
                ·
                  refine ⟨195483910875701043899179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1042580858003738900795621 195483910875701043899179)
                  ·
                    rfl

theorem cell21_856583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 4].length) (baseStart_856583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_856583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_856583 prefixEnd_856583 := by exact prefixLift 856583
  have htrace : WordTrace (prefixWord ++ tailWord_856583) baseStart_856583 baseEnd_856583 := by
    simpa [prefixWord, tailWord_856583, baseEnd_856583] using wordTrace_append hprefix tailTrace_856583
  have hstable : (prefixWord ++ tailWord_856583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856583).length < 2 ^ (prefixWord ++ tailWord_856583).sum := by decide
  have hdescent : baseEnd_856583 < baseStart_856583 := by decide
  rcases family_descends (prefixWord ++ tailWord_856583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856808 : List Nat := [2, 1, 4, 1, 4, 2, 1, 6]
def baseStart_856808 : Nat := 118140960795 + 856808 * 2 ^ 59
def prefixEnd_856808 : Nat := 4983230072969 + 3 ^ 40 * 856808 * 2
def baseEnd_856808 : Nat := 65178419647050217549573

theorem tailTrace_856808 : CollatzResearch.WordTrace tailWord_856808 prefixEnd_856808 65178419647050217549573 := by
  unfold tailWord_856808
  simp only [CollatzResearch.WordTrace]
  refine ⟨15625177539969211000745539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20833570053292281334327385 15625177539969211000745539)
  ·
    refine ⟨23437766309953816501118309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15625177539969211000745539 23437766309953816501118309)
    ·
      refine ⟨4394581183116340593959683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23437766309953816501118309 4394581183116340593959683)
      ·
        refine ⟨6591871774674510890939525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4394581183116340593959683 6591871774674510890939525)
        ·
          refine ⟨1235975957751470792051161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6591871774674510890939525 1235975957751470792051161)
          ·
            refine ⟨926981968313603094038371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1235975957751470792051161 926981968313603094038371)
            ·
              refine ⟨1390472952470404641057557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 926981968313603094038371 1390472952470404641057557)
              ·
                refine ⟨65178419647050217549573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1390472952470404641057557 65178419647050217549573)
                ·
                  rfl

theorem cell21_856808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 6].length) (baseStart_856808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_856808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_856808 prefixEnd_856808 := by exact prefixLift 856808
  have htrace : WordTrace (prefixWord ++ tailWord_856808) baseStart_856808 baseEnd_856808 := by
    simpa [prefixWord, tailWord_856808, baseEnd_856808] using wordTrace_append hprefix tailTrace_856808
  have hstable : (prefixWord ++ tailWord_856808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856808).length < 2 ^ (prefixWord ++ tailWord_856808).sum := by decide
  have hdescent : baseEnd_856808 < baseStart_856808 := by decide
  rcases family_descends (prefixWord ++ tailWord_856808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856819 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 8]
def baseStart_856819 : Nat := 118140960795 + 856819 * 2 ^ 59
def prefixEnd_856819 : Nat := 4983230072969 + 3 ^ 40 * 856819 * 2
def baseEnd_856819 : Nat := 195537769291017077965363

theorem tailTrace_856819 : CollatzResearch.WordTrace tailWord_856819 prefixEnd_856819 195537769291017077965363 := by
  unfold tailWord_856819
  simp only [CollatzResearch.WordTrace]
  refine ⟨31250756282898570880141511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20833837521932380586761007 31250756282898570880141511)
  ·
    refine ⟨46876134424347856320212267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31250756282898570880141511 46876134424347856320212267)
    ·
      refine ⟨70314201636521784480318401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46876134424347856320212267 70314201636521784480318401)
      ·
        refine ⟨52735651227391338360238801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70314201636521784480318401 52735651227391338360238801)
        ·
          refine ⟨39551738420543503770179101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52735651227391338360238801 39551738420543503770179101)
          ·
            refine ⟨14831901907703813913817163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39551738420543503770179101 14831901907703813913817163)
            ·
              refine ⟨22247852861555720870725745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14831901907703813913817163 22247852861555720870725745)
              ·
                refine ⟨16685889646166790653044309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22247852861555720870725745 16685889646166790653044309)
                ·
                  refine ⟨195537769291017077965363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16685889646166790653044309 195537769291017077965363)
                  ·
                    rfl

theorem cell21_856819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 8].length) (baseStart_856819 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_856819 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_856819 prefixEnd_856819 := by exact prefixLift 856819
  have htrace : WordTrace (prefixWord ++ tailWord_856819) baseStart_856819 baseEnd_856819 := by
    simpa [prefixWord, tailWord_856819, baseEnd_856819] using wordTrace_append hprefix tailTrace_856819
  have hstable : (prefixWord ++ tailWord_856819).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856819).length < 2 ^ (prefixWord ++ tailWord_856819).sum := by decide
  have hdescent : baseEnd_856819 < baseStart_856819 := by decide
  rcases family_descends (prefixWord ++ tailWord_856819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856822 : List Nat := [5, 1, 1, 1, 1, 2, 3, 2, 5]
def baseStart_856822 : Nat := 118140960795 + 856822 * 2 ^ 59
def prefixEnd_856822 : Nat := 4983230072969 + 3 ^ 40 * 856822 * 2
def baseEnd_856822 : Nat := 195538453931889739415357

theorem tailTrace_856822 : CollatzResearch.WordTrace tailWord_856822 prefixEnd_856822 195538453931889739415357 := by
  unfold tailWord_856822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1953179106367981399531295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20833910467925134928333813 1953179106367981399531295)
  ·
    refine ⟨2929768659551972099296943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1953179106367981399531295 2929768659551972099296943)
    ·
      refine ⟨4394652989327958148945415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2929768659551972099296943 4394652989327958148945415)
      ·
        refine ⟨6591979483991937223418123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4394652989327958148945415 6591979483991937223418123)
        ·
          refine ⟨9887969225987905835127185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6591979483991937223418123 9887969225987905835127185)
          ·
            refine ⟨7415976919490929376345389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9887969225987905835127185 7415976919490929376345389)
            ·
              refine ⟨2780991344809098516129521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7415976919490929376345389 2780991344809098516129521)
              ·
                refine ⟨2085743508606823887097141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2780991344809098516129521 2085743508606823887097141)
                ·
                  refine ⟨195538453931889739415357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2085743508606823887097141 195538453931889739415357)
                  ·
                    rfl

theorem cell21_856822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_856822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_856822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_856822 prefixEnd_856822 := by exact prefixLift 856822
  have htrace : WordTrace (prefixWord ++ tailWord_856822) baseStart_856822 baseEnd_856822 := by
    simpa [prefixWord, tailWord_856822, baseEnd_856822] using wordTrace_append hprefix tailTrace_856822
  have hstable : (prefixWord ++ tailWord_856822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856822).length < 2 ^ (prefixWord ++ tailWord_856822).sum := by decide
  have hdescent : baseEnd_856822 < baseStart_856822 := by decide
  rcases family_descends (prefixWord ++ tailWord_856822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856836 : List Nat := [2, 3, 2, 2, 1, 1, 2, 2, 6]
def baseStart_856836 : Nat := 118140960795 + 856836 * 2 ^ 59
def prefixEnd_856836 : Nat := 4983230072969 + 3 ^ 40 * 856836 * 2
def baseEnd_856836 : Nat := 195541648922628826181995

theorem tailTrace_856836 : CollatzResearch.WordTrace tailWord_856836 prefixEnd_856836 195541648922628826181995 := by
  unfold tailWord_856836
  simp only [CollatzResearch.WordTrace]
  refine ⟨15625688161918491391755181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20834250882557988522340241 15625688161918491391755181)
  ·
    refine ⟨5859633060719434271908193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15625688161918491391755181 5859633060719434271908193)
    ·
      refine ⟨4394724795539575703931145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5859633060719434271908193 4394724795539575703931145)
      ·
        refine ⟨3296043596654681777948359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4394724795539575703931145 3296043596654681777948359)
        ·
          refine ⟨4944065394982022666922539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3296043596654681777948359 4944065394982022666922539)
          ·
            refine ⟨7416098092473034000383809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4944065394982022666922539 7416098092473034000383809)
            ·
              refine ⟨5562073569354775500287857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7416098092473034000383809 5562073569354775500287857)
              ·
                refine ⟨4171555177016081625215893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5562073569354775500287857 4171555177016081625215893)
                ·
                  refine ⟨195541648922628826181995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4171555177016081625215893 195541648922628826181995)
                  ·
                    rfl

theorem cell21_856836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_856836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_856836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_856836 prefixEnd_856836 := by exact prefixLift 856836
  have htrace : WordTrace (prefixWord ++ tailWord_856836) baseStart_856836 baseEnd_856836 := by
    simpa [prefixWord, tailWord_856836, baseEnd_856836] using wordTrace_append hprefix tailTrace_856836
  have hstable : (prefixWord ++ tailWord_856836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856836).length < 2 ^ (prefixWord ++ tailWord_856836).sum := by decide
  have hdescent : baseEnd_856836 < baseStart_856836 := by decide
  rcases family_descends (prefixWord ++ tailWord_856836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856839 : List Nat := [1, 1, 4, 4, 1, 1, 1, 5, 3]
def baseStart_856839 : Nat := 118140960795 + 856839 * 2 ^ 59
def prefixEnd_856839 : Nat := 4983230072969 + 3 ^ 40 * 856839 * 2
def baseEnd_856839 : Nat := 195542333563501487631989

theorem tailTrace_856839 : CollatzResearch.WordTrace tailWord_856839 prefixEnd_856839 195542333563501487631989 := by
  unfold tailWord_856839
  simp only [CollatzResearch.WordTrace]
  refine ⟨31251485742826114295869571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20834323828550742863913047 31251485742826114295869571)
  ·
    refine ⟨46877228614239171443804357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31251485742826114295869571 46877228614239171443804357)
    ·
      refine ⟨8789480365169844645713317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46877228614239171443804357 8789480365169844645713317)
      ·
        refine ⟨1648027568469345871071247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8789480365169844645713317 1648027568469345871071247)
        ·
          refine ⟨2472041352704018806606871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1648027568469345871071247 2472041352704018806606871)
          ·
            refine ⟨3708062029056028209910307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2472041352704018806606871 3708062029056028209910307)
            ·
              refine ⟨5562093043584042314865461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3708062029056028209910307 5562093043584042314865461)
              ·
                refine ⟨521446222836003967018637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5562093043584042314865461 521446222836003967018637)
                ·
                  refine ⟨195542333563501487631989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 521446222836003967018637 195542333563501487631989)
                  ·
                    rfl

theorem cell21_856839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 5, 3].length) (baseStart_856839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_856839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_856839 prefixEnd_856839 := by exact prefixLift 856839
  have htrace : WordTrace (prefixWord ++ tailWord_856839) baseStart_856839 baseEnd_856839 := by
    simpa [prefixWord, tailWord_856839, baseEnd_856839] using wordTrace_append hprefix tailTrace_856839
  have hstable : (prefixWord ++ tailWord_856839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856839).length < 2 ^ (prefixWord ++ tailWord_856839).sum := by decide
  have hdescent : baseEnd_856839 < baseStart_856839 := by decide
  rcases family_descends (prefixWord ++ tailWord_856839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856881 : List Nat := [1, 2, 2, 3, 2, 1, 1, 4, 5]
def baseStart_856881 : Nat := 118140960795 + 856881 * 2 ^ 59
def prefixEnd_856881 : Nat := 4983230072969 + 3 ^ 40 * 856881 * 2
def baseEnd_856881 : Nat := 195551918535718747931903

theorem tailTrace_856881 : CollatzResearch.WordTrace tailWord_856881 prefixEnd_856881 195551918535718747931903 := by
  unfold tailWord_856881
  simp only [CollatzResearch.WordTrace]
  refine ⟨31253017608673955468898497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20835345072449303645932331 31253017608673955468898497)
  ·
    refine ⟨23439763206505466601673873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31253017608673955468898497 23439763206505466601673873)
    ·
      refine ⟨17579822404879099951255405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23439763206505466601673873 17579822404879099951255405)
      ·
        refine ⟨6592433401829662481720777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17579822404879099951255405 6592433401829662481720777)
        ·
          refine ⟨4944325051372246861290583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6592433401829662481720777 4944325051372246861290583)
          ·
            refine ⟨7416487577058370291935875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4944325051372246861290583 7416487577058370291935875)
            ·
              refine ⟨11124731365587555437903813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7416487577058370291935875 11124731365587555437903813)
              ·
                refine ⟨2085887131047666644606965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11124731365587555437903813 2085887131047666644606965)
                ·
                  refine ⟨195551918535718747931903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2085887131047666644606965 195551918535718747931903)
                  ·
                    rfl

theorem cell21_856881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 5].length) (baseStart_856881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_856881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_856881 prefixEnd_856881 := by exact prefixLift 856881
  have htrace : WordTrace (prefixWord ++ tailWord_856881) baseStart_856881 baseEnd_856881 := by
    simpa [prefixWord, tailWord_856881, baseEnd_856881] using wordTrace_append hprefix tailTrace_856881
  have hstable : (prefixWord ++ tailWord_856881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856881).length < 2 ^ (prefixWord ++ tailWord_856881).sum := by decide
  have hdescent : baseEnd_856881 < baseStart_856881 := by decide
  rcases family_descends (prefixWord ++ tailWord_856881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856884 : List Nat := [2, 5, 1, 1, 3, 1, 1, 7]
def baseStart_856884 : Nat := 118140960795 + 856884 * 2 ^ 59
def prefixEnd_856884 : Nat := 4983230072969 + 3 ^ 40 * 856884 * 2
def baseEnd_856884 : Nat := 65184201058863803127299

theorem tailTrace_856884 : CollatzResearch.WordTrace tailWord_856884 prefixEnd_856884 65184201058863803127299 := by
  unfold tailWord_856884
  simp only [CollatzResearch.WordTrace]
  refine ⟨15626563513831543490628853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20835418018442057987505137 15626563513831543490628853)
  ·
    refine ⟨1464990329421707202246455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15626563513831543490628853 1464990329421707202246455)
    ·
      refine ⟨2197485494132560803369683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1464990329421707202246455 2197485494132560803369683)
      ·
        refine ⟨3296228241198841205054525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2197485494132560803369683 3296228241198841205054525)
        ·
          refine ⟨1236085590449565451895447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3296228241198841205054525 1236085590449565451895447)
          ·
            refine ⟨1854128385674348177843171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1236085590449565451895447 1854128385674348177843171)
            ·
              refine ⟨2781192578511522266764757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1854128385674348177843171 2781192578511522266764757)
              ·
                refine ⟨65184201058863803127299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2781192578511522266764757 65184201058863803127299)
                ·
                  rfl

theorem cell21_856884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 7].length) (baseStart_856884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_856884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_856884 prefixEnd_856884 := by exact prefixLift 856884
  have htrace : WordTrace (prefixWord ++ tailWord_856884) baseStart_856884 baseEnd_856884 := by
    simpa [prefixWord, tailWord_856884, baseEnd_856884] using wordTrace_append hprefix tailTrace_856884
  have hstable : (prefixWord ++ tailWord_856884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856884).length < 2 ^ (prefixWord ++ tailWord_856884).sum := by decide
  have hdescent : baseEnd_856884 < baseStart_856884 := by decide
  rcases family_descends (prefixWord ++ tailWord_856884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856971 : List Nat := [1, 1, 1, 1, 4, 2, 2, 3, 6]
def baseStart_856971 : Nat := 118140960795 + 856971 * 2 ^ 59
def prefixEnd_856971 : Nat := 4983230072969 + 3 ^ 40 * 856971 * 2
def baseEnd_856971 : Nat := 195572457761898591431719

theorem tailTrace_856971 : CollatzResearch.WordTrace tailWord_856971 prefixEnd_856971 195572457761898591431719 := by
  unfold tailWord_856971
  simp only [CollatzResearch.WordTrace]
  refine ⟨31256300178347900839674767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20837533452231933893116511 31256300178347900839674767)
  ·
    refine ⟨46884450267521851259512151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31256300178347900839674767 46884450267521851259512151)
    ·
      refine ⟨70326675401282776889268227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46884450267521851259512151 70326675401282776889268227)
      ·
        refine ⟨105490013101924165333902341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70326675401282776889268227 105490013101924165333902341)
        ·
          refine ⟨19779377456610781000106689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105490013101924165333902341 19779377456610781000106689)
          ·
            refine ⟨14834533092458085750080017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19779377456610781000106689 14834533092458085750080017)
            ·
              refine ⟨11125899819343564312560013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14834533092458085750080017 11125899819343564312560013)
              ·
                refine ⟨4172212432253836617210005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11125899819343564312560013 4172212432253836617210005)
                ·
                  refine ⟨195572457761898591431719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4172212432253836617210005 195572457761898591431719)
                  ·
                    rfl

theorem cell21_856971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 6].length) (baseStart_856971 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_856971 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_856971 prefixEnd_856971 := by exact prefixLift 856971
  have htrace : WordTrace (prefixWord ++ tailWord_856971) baseStart_856971 baseEnd_856971 := by
    simpa [prefixWord, tailWord_856971, baseEnd_856971] using wordTrace_append hprefix tailTrace_856971
  have hstable : (prefixWord ++ tailWord_856971).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856971).length < 2 ^ (prefixWord ++ tailWord_856971).sum := by decide
  have hdescent : baseEnd_856971 < baseStart_856971 := by decide
  rcases family_descends (prefixWord ++ tailWord_856971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857098 : List Nat := [3, 1, 2, 2, 3, 3, 2, 1, 4]
def baseStart_857098 : Nat := 118140960795 + 857098 * 2 ^ 59
def prefixEnd_857098 : Nat := 4983230072969 + 3 ^ 40 * 857098 * 2
def baseEnd_857098 : Nat := 195601440892174592814793

theorem tailTrace_857098 : CollatzResearch.WordTrace tailWord_857098 prefixEnd_857098 195601440892174592814793 := by
  unfold tailWord_857098
  simp only [CollatzResearch.WordTrace]
  refine ⟨7815233062221950382386987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20840621499258534353031965 7815233062221950382386987)
  ·
    refine ⟨11722849593332925573580481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7815233062221950382386987 11722849593332925573580481)
    ·
      refine ⟨8792137194999694180185361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11722849593332925573580481 8792137194999694180185361)
      ·
        refine ⟨6594102896249770635139021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8792137194999694180185361 6594102896249770635139021)
        ·
          refine ⟨2472788586093663988177133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6594102896249770635139021 2472788586093663988177133)
          ·
            refine ⟨927295719785123995566425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2472788586093663988177133 927295719785123995566425)
            ·
              refine ⟨695471789838842996674819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 927295719785123995566425 695471789838842996674819)
              ·
                refine ⟨1043207684758264495012229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 695471789838842996674819 1043207684758264495012229)
                ·
                  refine ⟨195601440892174592814793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1043207684758264495012229 195601440892174592814793)
                  ·
                    rfl

theorem cell21_857098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 4].length) (baseStart_857098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_857098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_857098 prefixEnd_857098 := by exact prefixLift 857098
  have htrace : WordTrace (prefixWord ++ tailWord_857098) baseStart_857098 baseEnd_857098 := by
    simpa [prefixWord, tailWord_857098, baseEnd_857098] using wordTrace_append hprefix tailTrace_857098
  have hstable : (prefixWord ++ tailWord_857098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857098).length < 2 ^ (prefixWord ++ tailWord_857098).sum := by decide
  have hdescent : baseEnd_857098 < baseStart_857098 := by decide
  rcases family_descends (prefixWord ++ tailWord_857098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857199 : List Nat := [1, 1, 2, 1, 3, 3, 3, 1, 6]
def baseStart_857199 : Nat := 118140960795 + 857199 * 2 ^ 59
def prefixEnd_857199 : Nat := 4983230072969 + 3 ^ 40 * 857199 * 2
def baseEnd_857199 : Nat := 195624490468220861631253

theorem tailTrace_857199 : CollatzResearch.WordTrace tailWord_857199 prefixEnd_857199 195624490468220861631253 := by
  unfold tailWord_857199
  simp only [CollatzResearch.WordTrace]
  refine ⟨31264616021521895778974651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20843077347681263852649767 31264616021521895778974651)
  ·
    refine ⟨46896924032282843668461977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31264616021521895778974651 46896924032282843668461977)
    ·
      refine ⟨35172693024212132751346483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46896924032282843668461977 35172693024212132751346483)
      ·
        refine ⟨52759039536318199127019725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35172693024212132751346483 52759039536318199127019725)
        ·
          refine ⟨19784639826119324672632397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52759039536318199127019725 19784639826119324672632397)
          ·
            refine ⟨7419239934794746752237149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19784639826119324672632397 7419239934794746752237149)
            ·
              refine ⟨2782214975548030032088931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7419239934794746752237149 2782214975548030032088931)
              ·
                refine ⟨4173322463322045048133397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2782214975548030032088931 4173322463322045048133397)
                ·
                  refine ⟨195624490468220861631253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4173322463322045048133397 195624490468220861631253)
                  ·
                    rfl

theorem cell21_857199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 6].length) (baseStart_857199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_857199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_857199 prefixEnd_857199 := by exact prefixLift 857199
  have htrace : WordTrace (prefixWord ++ tailWord_857199) baseStart_857199 baseEnd_857199 := by
    simpa [prefixWord, tailWord_857199, baseEnd_857199] using wordTrace_append hprefix tailTrace_857199
  have hstable : (prefixWord ++ tailWord_857199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857199).length < 2 ^ (prefixWord ++ tailWord_857199).sum := by decide
  have hdescent : baseEnd_857199 < baseStart_857199 := by decide
  rcases family_descends (prefixWord ++ tailWord_857199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857202 : List Nat := [3, 2, 1, 2, 2, 1, 1, 6, 3]
def baseStart_857202 : Nat := 118140960795 + 857202 * 2 ^ 59
def prefixEnd_857202 : Nat := 4983230072969 + 3 ^ 40 * 857202 * 2
def baseEnd_857202 : Nat := 195625175109093523081247

theorem tailTrace_857202 : CollatzResearch.WordTrace tailWord_857202 prefixEnd_857202 195625175109093523081247 := by
  unfold tailWord_857202
  simp only [CollatzResearch.WordTrace]
  refine ⟨7816181360127756822833465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20843150293674018194222573 7816181360127756822833465)
  ·
    refine ⟨5862136020095817617125099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7816181360127756822833465 5862136020095817617125099)
    ·
      refine ⟨8793204030143726425687649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5862136020095817617125099 8793204030143726425687649)
      ·
        refine ⟨6594903022607794819265737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8793204030143726425687649 6594903022607794819265737)
        ·
          refine ⟨4946177266955846114449303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6594903022607794819265737 4946177266955846114449303)
          ·
            refine ⟨7419265900433769171673955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4946177266955846114449303 7419265900433769171673955)
            ·
              refine ⟨11128898850650653757510933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7419265900433769171673955 11128898850650653757510933)
              ·
                refine ⟨521667133624249394883325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11128898850650653757510933 521667133624249394883325)
                ·
                  refine ⟨195625175109093523081247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 521667133624249394883325 195625175109093523081247)
                  ·
                    rfl

theorem cell21_857202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_857202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_857202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_857202 prefixEnd_857202 := by exact prefixLift 857202
  have htrace : WordTrace (prefixWord ++ tailWord_857202) baseStart_857202 baseEnd_857202 := by
    simpa [prefixWord, tailWord_857202, baseEnd_857202] using wordTrace_append hprefix tailTrace_857202
  have hstable : (prefixWord ++ tailWord_857202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857202).length < 2 ^ (prefixWord ++ tailWord_857202).sum := by decide
  have hdescent : baseEnd_857202 < baseStart_857202 := by decide
  rcases family_descends (prefixWord ++ tailWord_857202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857247 : List Nat := [1, 1, 2, 6, 2, 2, 7]
def baseStart_857247 : Nat := 118140960795 + 857247 * 2 ^ 59
def prefixEnd_857247 : Nat := 4983230072969 + 3 ^ 40 * 857247 * 2
def baseEnd_857247 : Nat := 21737271635798160536795

theorem tailTrace_857247 : CollatzResearch.WordTrace tailWord_857247 prefixEnd_857247 21737271635798160536795 := by
  unfold tailWord_857247
  simp only [CollatzResearch.WordTrace]
  refine ⟨31266366725347999976721995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20844244483565333317814663 31266366725347999976721995)
  ·
    refine ⟨46899550088021999965082993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31266366725347999976721995 46899550088021999965082993)
    ·
      refine ⟨35174662566016499973812245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46899550088021999965082993 35174662566016499973812245)
      ·
        refine ⟨1648812307782023436272449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 35174662566016499973812245 1648812307782023436272449)
        ·
          refine ⟨1236609230836517577204337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1648812307782023436272449 1236609230836517577204337)
          ·
            refine ⟨927456923127388182903253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1236609230836517577204337 927456923127388182903253)
            ·
              refine ⟨21737271635798160536795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 927456923127388182903253 21737271635798160536795)
              ·
                rfl

theorem cell21_857247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 7].length) (baseStart_857247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_857247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_857247 prefixEnd_857247 := by exact prefixLift 857247
  have htrace : WordTrace (prefixWord ++ tailWord_857247) baseStart_857247 baseEnd_857247 := by
    simpa [prefixWord, tailWord_857247, baseEnd_857247] using wordTrace_append hprefix tailTrace_857247
  have hstable : (prefixWord ++ tailWord_857247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857247).length < 2 ^ (prefixWord ++ tailWord_857247).sum := by decide
  have hdescent : baseEnd_857247 < baseStart_857247 := by decide
  rcases family_descends (prefixWord ++ tailWord_857247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857368 : List Nat := [2, 1, 2, 3, 1, 3, 3, 2, 4]
def baseStart_857368 : Nat := 118140960795 + 857368 * 2 ^ 59
def prefixEnd_857368 : Nat := 4983230072969 + 3 ^ 40 * 857368 * 2
def baseEnd_857368 : Nat := 195663058570714123314241

theorem tailTrace_857368 : CollatzResearch.WordTrace tailWord_857368 prefixEnd_857368 195663058570714123314241 := by
  unfold tailWord_857368
  simp only [CollatzResearch.WordTrace]
  refine ⟨15635389978954818820938379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20847186638606425094584505 15635389978954818820938379)
  ·
    refine ⟨23453084968432228231407569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15635389978954818820938379 23453084968432228231407569)
    ·
      refine ⟨17589813726324171173555677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23453084968432228231407569 17589813726324171173555677)
      ·
        refine ⟨6596180147371564190083379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17589813726324171173555677 6596180147371564190083379)
        ·
          refine ⟨9894270221057346285125069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6596180147371564190083379 9894270221057346285125069)
          ·
            refine ⟨3710351332896504856921901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9894270221057346285125069 3710351332896504856921901)
            ·
              refine ⟨1391381749836189321345713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3710351332896504856921901 1391381749836189321345713)
              ·
                refine ⟨1043536312377141991009285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1391381749836189321345713 1043536312377141991009285)
                ·
                  refine ⟨195663058570714123314241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1043536312377141991009285 195663058570714123314241)
                  ·
                    rfl

theorem cell21_857368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 4].length) (baseStart_857368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_857368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_857368 prefixEnd_857368 := by exact prefixLift 857368
  have htrace : WordTrace (prefixWord ++ tailWord_857368) baseStart_857368 baseEnd_857368 := by
    simpa [prefixWord, tailWord_857368, baseEnd_857368] using wordTrace_append hprefix tailTrace_857368
  have hstable : (prefixWord ++ tailWord_857368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857368).length < 2 ^ (prefixWord ++ tailWord_857368).sum := by decide
  have hdescent : baseEnd_857368 < baseStart_857368 := by decide
  rcases family_descends (prefixWord ++ tailWord_857368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857405 : List Nat := [1, 4, 1, 5, 2, 1, 1, 3, 3]
def baseStart_857405 : Nat := 118140960795 + 857405 * 2 ^ 59
def prefixEnd_857405 : Nat := 4983230072969 + 3 ^ 40 * 857405 * 2
def baseEnd_857405 : Nat := 195671502474810281197499

theorem tailTrace_857405 : CollatzResearch.WordTrace tailWord_857405 prefixEnd_857405 195671502474810281197499 := by
  unfold tailWord_857405
  simp only [CollatzResearch.WordTrace]
  refine ⟨31272129458775592960973669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20848086305850395307315779 31272129458775592960973669)
  ·
    refine ⟨5863524273520423680182563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31272129458775592960973669 5863524273520423680182563)
    ·
      refine ⟨8795286410280635520273845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5863524273520423680182563 8795286410280635520273845)
      ·
        refine ⟨824558100963809580025673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8795286410280635520273845 824558100963809580025673)
        ·
          refine ⟨618418575722857185019255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 824558100963809580025673 618418575722857185019255)
          ·
            refine ⟨927627863584285777528883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618418575722857185019255 927627863584285777528883)
            ·
              refine ⟨1391441795376428666293325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 927627863584285777528883 1391441795376428666293325)
              ·
                refine ⟨521790673266160749859997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1391441795376428666293325 521790673266160749859997)
                ·
                  refine ⟨195671502474810281197499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 521790673266160749859997 195671502474810281197499)
                  ·
                    rfl

theorem cell21_857405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_857405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_857405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_857405 prefixEnd_857405 := by exact prefixLift 857405
  have htrace : WordTrace (prefixWord ++ tailWord_857405) baseStart_857405 baseEnd_857405 := by
    simpa [prefixWord, tailWord_857405, baseEnd_857405] using wordTrace_append hprefix tailTrace_857405
  have hstable : (prefixWord ++ tailWord_857405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857405).length < 2 ^ (prefixWord ++ tailWord_857405).sum := by decide
  have hdescent : baseEnd_857405 < baseStart_857405 := by decide
  rcases family_descends (prefixWord ++ tailWord_857405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857427 : List Nat := [1, 1, 1, 2, 1, 1, 6, 4, 4]
def baseStart_857427 : Nat := 118140960795 + 857427 * 2 ^ 59
def prefixEnd_857427 : Nat := 4983230072969 + 3 ^ 40 * 857427 * 2
def baseEnd_857427 : Nat := 195676523174543131830787

theorem tailTrace_857427 : CollatzResearch.WordTrace tailWord_857427 prefixEnd_857427 195676523174543131830787 := by
  unfold tailWord_857427
  simp only [CollatzResearch.WordTrace]
  refine ⟨31272931864695890718274535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20848621243130593812183023 31272931864695890718274535)
  ·
    refine ⟨46909397797043836077411803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31272931864695890718274535 46909397797043836077411803)
    ·
      refine ⟨70364096695565754116117705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46909397797043836077411803 70364096695565754116117705)
      ·
        refine ⟨52773072521674315587088279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70364096695565754116117705 52773072521674315587088279)
        ·
          refine ⟨79159608782511473380632419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52773072521674315587088279 79159608782511473380632419)
          ·
            refine ⟨118739413173767210070948629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79159608782511473380632419 118739413173767210070948629)
            ·
              refine ⟨5565909992520337972075717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 118739413173767210070948629 5565909992520337972075717)
              ·
                refine ⟨1043608123597563369764197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5565909992520337972075717 1043608123597563369764197)
                ·
                  refine ⟨195676523174543131830787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1043608123597563369764197 195676523174543131830787)
                  ·
                    rfl

theorem cell21_857427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 4].length) (baseStart_857427 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_857427 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_857427 prefixEnd_857427 := by exact prefixLift 857427
  have htrace : WordTrace (prefixWord ++ tailWord_857427) baseStart_857427 baseEnd_857427 := by
    simpa [prefixWord, tailWord_857427, baseEnd_857427] using wordTrace_append hprefix tailTrace_857427
  have hstable : (prefixWord ++ tailWord_857427).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857427).length < 2 ^ (prefixWord ++ tailWord_857427).sum := by decide
  have hdescent : baseEnd_857427 < baseStart_857427 := by decide
  rcases family_descends (prefixWord ++ tailWord_857427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857444 : List Nat := [2, 3, 1, 1, 3, 3, 1, 3, 4]
def baseStart_857444 : Nat := 118140960795 + 857444 * 2 ^ 59
def prefixEnd_857444 : Nat := 4983230072969 + 3 ^ 40 * 857444 * 2
def baseEnd_857444 : Nat := 195680402806154880047419

theorem tailTrace_857444 : CollatzResearch.WordTrace tailWord_857444 prefixEnd_857444 195680402806154880047419 := by
  unfold tailWord_857444
  simp only [CollatzResearch.WordTrace]
  refine ⟨15636775952817151310821693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20849034603756201747762257 15636775952817151310821693)
  ·
    refine ⟨5863790982306431741558135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15636775952817151310821693 5863790982306431741558135)
    ·
      refine ⟨8795686473459647612337203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5863790982306431741558135 8795686473459647612337203)
      ·
        refine ⟨13193529710189471418505805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8795686473459647612337203 13193529710189471418505805)
        ·
          refine ⟨4947573641321051781939677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13193529710189471418505805 4947573641321051781939677)
          ·
            refine ⟨1855340115495394418227379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4947573641321051781939677 1855340115495394418227379)
            ·
              refine ⟨2783010173243091627341069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1855340115495394418227379 2783010173243091627341069)
              ·
                refine ⟨1043628814966159360252901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2783010173243091627341069 1043628814966159360252901)
                ·
                  refine ⟨195680402806154880047419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1043628814966159360252901 195680402806154880047419)
                  ·
                    rfl

theorem cell21_857444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_857444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_857444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_857444 prefixEnd_857444 := by exact prefixLift 857444
  have htrace : WordTrace (prefixWord ++ tailWord_857444) baseStart_857444 baseEnd_857444 := by
    simpa [prefixWord, tailWord_857444, baseEnd_857444] using wordTrace_append hprefix tailTrace_857444
  have hstable : (prefixWord ++ tailWord_857444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857444).length < 2 ^ (prefixWord ++ tailWord_857444).sum := by decide
  have hdescent : baseEnd_857444 < baseStart_857444 := by decide
  rcases family_descends (prefixWord ++ tailWord_857444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857489 : List Nat := [1, 2, 2, 1, 1, 1, 2, 8, 3]
def baseStart_857489 : Nat := 118140960795 + 857489 * 2 ^ 59
def prefixEnd_857489 : Nat := 4983230072969 + 3 ^ 40 * 857489 * 2
def baseEnd_857489 : Nat := 195690672419244801797327

theorem tailTrace_857489 : CollatzResearch.WordTrace tailWord_857489 prefixEnd_857489 195690672419244801797327 := by
  unfold tailWord_857489
  simp only [CollatzResearch.WordTrace]
  refine ⟨31275193190471275307031521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20850128793647516871354347 31275193190471275307031521)
  ·
    refine ⟨23456394892853456480273641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31275193190471275307031521 23456394892853456480273641)
    ·
      refine ⟨17592296169640092360205231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23456394892853456480273641 17592296169640092360205231)
      ·
        refine ⟨26388444254460138540307847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17592296169640092360205231 26388444254460138540307847)
        ·
          refine ⟨39582666381690207810461771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26388444254460138540307847 39582666381690207810461771)
          ·
            refine ⟨59373999572535311715692657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39582666381690207810461771 59373999572535311715692657)
            ·
              refine ⟨44530499679401483786769493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59373999572535311715692657 44530499679401483786769493)
              ·
                refine ⟨521841793117986138126205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 44530499679401483786769493 521841793117986138126205)
                ·
                  refine ⟨195690672419244801797327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 521841793117986138126205 195690672419244801797327)
                  ·
                    rfl

theorem cell21_857489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 8, 3].length) (baseStart_857489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_857489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_857489 prefixEnd_857489 := by exact prefixLift 857489
  have htrace : WordTrace (prefixWord ++ tailWord_857489) baseStart_857489 baseEnd_857489 := by
    simpa [prefixWord, tailWord_857489, baseEnd_857489] using wordTrace_append hprefix tailTrace_857489
  have hstable : (prefixWord ++ tailWord_857489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857489).length < 2 ^ (prefixWord ++ tailWord_857489).sum := by decide
  have hdescent : baseEnd_857489 < baseStart_857489 := by decide
  rcases family_descends (prefixWord ++ tailWord_857489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857565 : List Nat := [1, 4, 3, 1, 1, 2, 2, 2, 5]
def baseStart_857565 : Nat := 118140960795 + 857565 * 2 ^ 59
def prefixEnd_857565 : Nat := 4983230072969 + 3 ^ 40 * 857565 * 2
def baseEnd_857565 : Nat := 195708016654685558530505

theorem tailTrace_857565 : CollatzResearch.WordTrace tailWord_857565 prefixEnd_857565 195708016654685558530505 := by
  unfold tailWord_857565
  simp only [CollatzResearch.WordTrace]
  refine ⟨31277965138195940286798149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20851976758797293524532099 31277965138195940286798149)
  ·
    refine ⟨5864618463411738803774653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31277965138195940286798149 5864618463411738803774653)
    ·
      refine ⟨2199231923779402051415495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5864618463411738803774653 2199231923779402051415495)
      ·
        refine ⟨3298847885669103077123243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2199231923779402051415495 3298847885669103077123243)
        ·
          refine ⟨4948271828503654615684865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3298847885669103077123243 4948271828503654615684865)
          ·
            refine ⟨3711203871377740961763649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4948271828503654615684865 3711203871377740961763649)
            ·
              refine ⟨2783402903533305721322737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3711203871377740961763649 2783402903533305721322737)
              ·
                refine ⟨2087552177649979290992053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2783402903533305721322737 2087552177649979290992053)
                ·
                  refine ⟨195708016654685558530505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2087552177649979290992053 195708016654685558530505)
                  ·
                    rfl

theorem cell21_857565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_857565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_857565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_857565 prefixEnd_857565 := by exact prefixLift 857565
  have htrace : WordTrace (prefixWord ++ tailWord_857565) baseStart_857565 baseEnd_857565 := by
    simpa [prefixWord, tailWord_857565, baseEnd_857565] using wordTrace_append hprefix tailTrace_857565
  have hstable : (prefixWord ++ tailWord_857565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857565).length < 2 ^ (prefixWord ++ tailWord_857565).sum := by decide
  have hdescent : baseEnd_857565 < baseStart_857565 := by decide
  rcases family_descends (prefixWord ++ tailWord_857565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857610 : List Nat := [3, 1, 2, 2, 2, 3, 2, 6]
def baseStart_857610 : Nat := 118140960795 + 857610 * 2 ^ 59
def prefixEnd_857610 : Nat := 4983230072969 + 3 ^ 40 * 857610 * 2
def baseEnd_857610 : Nat := 65239428755925160093471

theorem tailTrace_857610 : CollatzResearch.WordTrace tailWord_857610 prefixEnd_857610 65239428755925160093471 := by
  unfold tailWord_857610
  simp only [CollatzResearch.WordTrace]
  refine ⟨7819901605758228243046571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20853070948688608648124189 7819901605758228243046571)
  ·
    refine ⟨11729852408637342364569857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7819901605758228243046571 11729852408637342364569857)
    ·
      refine ⟨8797389306478006773427393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11729852408637342364569857 8797389306478006773427393)
      ·
        refine ⟨6598041979858505080070545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8797389306478006773427393 6598041979858505080070545)
        ·
          refine ⟨4948531484893878810052909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6598041979858505080070545 4948531484893878810052909)
          ·
            refine ⟨1855699306835204553769841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4948531484893878810052909 1855699306835204553769841)
            ·
              refine ⟨1391774480126403415327381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1855699306835204553769841 1391774480126403415327381)
              ·
                refine ⟨65239428755925160093471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1391774480126403415327381 65239428755925160093471)
                ·
                  rfl

theorem cell21_857610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 6].length) (baseStart_857610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_857610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_857610 prefixEnd_857610 := by exact prefixLift 857610
  have htrace : WordTrace (prefixWord ++ tailWord_857610) baseStart_857610 baseEnd_857610 := by
    simpa [prefixWord, tailWord_857610, baseEnd_857610] using wordTrace_append hprefix tailTrace_857610
  have hstable : (prefixWord ++ tailWord_857610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857610).length < 2 ^ (prefixWord ++ tailWord_857610).sum := by decide
  have hdescent : baseEnd_857610 < baseStart_857610 := by decide
  rcases family_descends (prefixWord ++ tailWord_857610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857655 : List Nat := [1, 1, 3, 1, 2, 4, 1, 4, 4]
def baseStart_857655 : Nat := 118140960795 + 857655 * 2 ^ 59
def prefixEnd_857655 : Nat := 4983230072969 + 3 ^ 40 * 857655 * 2
def baseEnd_857655 : Nat := 195728555880865402030321

theorem tailTrace_857655 : CollatzResearch.WordTrace tailWord_857655 prefixEnd_857655 195728555880865402030321 := by
  unfold tailWord_857655
  simp only [CollatzResearch.WordTrace]
  refine ⟨31281247707869885657574419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20854165138579923771716279 31281247707869885657574419)
  ·
    refine ⟨46921871561804828486361629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31281247707869885657574419 46921871561804828486361629)
    ·
      refine ⟨17595701835676810682385611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46921871561804828486361629 17595701835676810682385611)
      ·
        refine ⟨26393552753515216023578417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17595701835676810682385611 26393552753515216023578417)
        ·
          refine ⟨19795164565136412017683813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26393552753515216023578417 19795164565136412017683813)
          ·
            refine ⟨3711593355963077253315715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19795164565136412017683813 3711593355963077253315715)
            ·
              refine ⟨5567390033944615879973573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3711593355963077253315715 5567390033944615879973573)
              ·
                refine ⟨1043885631364615477495045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5567390033944615879973573 1043885631364615477495045)
                ·
                  refine ⟨195728555880865402030321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1043885631364615477495045 195728555880865402030321)
                  ·
                    rfl

theorem cell21_857655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 4].length) (baseStart_857655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_857655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_857655 prefixEnd_857655 := by exact prefixLift 857655
  have htrace : WordTrace (prefixWord ++ tailWord_857655) baseStart_857655 baseEnd_857655 := by
    simpa [prefixWord, tailWord_857655, baseEnd_857655] using wordTrace_append hprefix tailTrace_857655
  have hstable : (prefixWord ++ tailWord_857655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857655).length < 2 ^ (prefixWord ++ tailWord_857655).sum := by decide
  have hdescent : baseEnd_857655 < baseStart_857655 := by decide
  rcases family_descends (prefixWord ++ tailWord_857655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857717 : List Nat := [1, 3, 4, 2, 1, 1, 1, 3, 5]
def baseStart_857717 : Nat := 118140960795 + 857717 * 2 ^ 59
def prefixEnd_857717 : Nat := 4983230072969 + 3 ^ 40 * 857717 * 2
def baseEnd_857717 : Nat := 195742705125567071996861

theorem tailTrace_857717 : CollatzResearch.WordTrace tailWord_857717 prefixEnd_857717 195742705125567071996861 := by
  unfold tailWord_857717
  simp only [CollatzResearch.WordTrace]
  refine ⟨31283509033645270246331405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20855672689096846830887603 31283509033645270246331405)
  ·
    refine ⟨11731315887616976342374277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31283509033645270246331405 11731315887616976342374277)
    ·
      refine ⟨2199621728928183064195177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11731315887616976342374277 2199621728928183064195177)
      ·
        refine ⟨1649716296696137298146383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2199621728928183064195177 1649716296696137298146383)
        ·
          refine ⟨2474574445044205947219575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1649716296696137298146383 2474574445044205947219575)
          ·
            refine ⟨3711861667566308920829363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2474574445044205947219575 3711861667566308920829363)
            ·
              refine ⟨5567792501349463381244045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3711861667566308920829363 5567792501349463381244045)
              ·
                refine ⟨2087922188006048767966517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5567792501349463381244045 2087922188006048767966517)
                ·
                  refine ⟨195742705125567071996861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2087922188006048767966517 195742705125567071996861)
                  ·
                    rfl

theorem cell21_857717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_857717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_857717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_857717 prefixEnd_857717 := by exact prefixLift 857717
  have htrace : WordTrace (prefixWord ++ tailWord_857717) baseStart_857717 baseEnd_857717 := by
    simpa [prefixWord, tailWord_857717, baseEnd_857717] using wordTrace_append hprefix tailTrace_857717
  have hstable : (prefixWord ++ tailWord_857717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857717).length < 2 ^ (prefixWord ++ tailWord_857717).sum := by decide
  have hdescent : baseEnd_857717 < baseStart_857717 := by decide
  rcases family_descends (prefixWord ++ tailWord_857717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857768 : List Nat := [2, 1, 7, 1, 1, 2, 1, 1, 5]
def baseStart_857768 : Nat := 118140960795 + 857768 * 2 ^ 59
def prefixEnd_857768 : Nat := 4983230072969 + 3 ^ 40 * 857768 * 2
def baseEnd_857768 : Nat := 195754344020402316646757

theorem tailTrace_857768 : CollatzResearch.WordTrace tailWord_857768 prefixEnd_857768 195754344020402316646757 := by
  unfold tailWord_857768
  simp only [CollatzResearch.WordTrace]
  refine ⟨15642684578230252978218979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20856912770973670637625305 15642684578230252978218979)
  ·
    refine ⟨23464026867345379467328469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15642684578230252978218979 23464026867345379467328469)
    ·
      refine ⟨549938129703407331265511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 23464026867345379467328469 549938129703407331265511)
      ·
        refine ⟨824907194555110996898267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 549938129703407331265511 824907194555110996898267)
        ·
          refine ⟨1237360791832666495347401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 824907194555110996898267 1237360791832666495347401)
          ·
            refine ⟨928020593874499871510551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1237360791832666495347401 928020593874499871510551)
            ·
              refine ⟨1392030890811749807265827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 928020593874499871510551 1392030890811749807265827)
              ·
                refine ⟨2088046336217624710898741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1392030890811749807265827 2088046336217624710898741)
                ·
                  refine ⟨195754344020402316646757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2088046336217624710898741 195754344020402316646757)
                  ·
                    rfl

theorem cell21_857768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 5].length) (baseStart_857768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_857768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_857768 prefixEnd_857768 := by exact prefixLift 857768
  have htrace : WordTrace (prefixWord ++ tailWord_857768) baseStart_857768 baseEnd_857768 := by
    simpa [prefixWord, tailWord_857768, baseEnd_857768] using wordTrace_append hprefix tailTrace_857768
  have hstable : (prefixWord ++ tailWord_857768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857768).length < 2 ^ (prefixWord ++ tailWord_857768).sum := by decide
  have hdescent : baseEnd_857768 < baseStart_857768 := by decide
  rcases family_descends (prefixWord ++ tailWord_857768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857776 : List Nat := [2, 1, 1, 1, 2, 1, 7, 1, 5]
def baseStart_857776 : Nat := 118140960795 + 857776 * 2 ^ 59
def prefixEnd_857776 : Nat := 4983230072969 + 3 ^ 40 * 857776 * 2
def baseEnd_857776 : Nat := 195756169729396080513407

theorem tailTrace_857776 : CollatzResearch.WordTrace tailWord_857776 prefixEnd_857776 195756169729396080513407 := by
  unfold tailWord_857776
  simp only [CollatzResearch.WordTrace]
  refine ⟨15642830470215761661364591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20857107293621015548486121 15642830470215761661364591)
  ·
    refine ⟨23464245705323642492046887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15642830470215761661364591 23464245705323642492046887)
    ·
      refine ⟨35196368557985463738070331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23464245705323642492046887 35196368557985463738070331)
      ·
        refine ⟨52794552836978195607105497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35196368557985463738070331 52794552836978195607105497)
        ·
          refine ⟨39595914627733646705329123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52794552836978195607105497 39595914627733646705329123)
          ·
            refine ⟨59393871941600470057993685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39595914627733646705329123 59393871941600470057993685)
            ·
              refine ⟨1392043873631261016984227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 59393871941600470057993685 1392043873631261016984227)
              ·
                refine ⟨2088065810446891525476341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1392043873631261016984227 2088065810446891525476341)
                ·
                  refine ⟨195756169729396080513407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2088065810446891525476341 195756169729396080513407)
                  ·
                    rfl

theorem cell21_857776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 5].length) (baseStart_857776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_857776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_857776 prefixEnd_857776 := by exact prefixLift 857776
  have htrace : WordTrace (prefixWord ++ tailWord_857776) baseStart_857776 baseEnd_857776 := by
    simpa [prefixWord, tailWord_857776, baseEnd_857776] using wordTrace_append hprefix tailTrace_857776
  have hstable : (prefixWord ++ tailWord_857776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857776).length < 2 ^ (prefixWord ++ tailWord_857776).sum := by decide
  have hdescent : baseEnd_857776 < baseStart_857776 := by decide
  rcases family_descends (prefixWord ++ tailWord_857776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857782 : List Nat := [5, 1, 3, 1, 1, 1, 4, 1, 4]
def baseStart_857782 : Nat := 118140960795 + 857782 * 2 ^ 59
def prefixEnd_857782 : Nat := 4983230072969 + 3 ^ 40 * 857782 * 2
def baseEnd_857782 : Nat := 195757539011141403413395

theorem tailTrace_857782 : CollatzResearch.WordTrace tailWord_857782 prefixEnd_857782 195757539011141403413395 := by
  unfold tailWord_857782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1955367486150611646715475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20857253185606524231631733 1955367486150611646715475)
  ·
    refine ⟨2933051229225917470073213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1955367486150611646715475 2933051229225917470073213)
    ·
      refine ⟨1099894210959719051277455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2933051229225917470073213 1099894210959719051277455)
      ·
        refine ⟨1649841316439578576916183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1099894210959719051277455 1649841316439578576916183)
        ·
          refine ⟨2474761974659367865374275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1649841316439578576916183 2474761974659367865374275)
          ·
            refine ⟨3712142961989051798061413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2474761974659367865374275 3712142961989051798061413)
            ·
              refine ⟨696026805372947212136515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3712142961989051798061413 696026805372947212136515)
              ·
                refine ⟨1044040208059420818204773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 696026805372947212136515 1044040208059420818204773)
                ·
                  refine ⟨195757539011141403413395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1044040208059420818204773 195757539011141403413395)
                  ·
                    rfl

theorem cell21_857782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_857782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_857782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_857782 prefixEnd_857782 := by exact prefixLift 857782
  have htrace : WordTrace (prefixWord ++ tailWord_857782) baseStart_857782 baseEnd_857782 := by
    simpa [prefixWord, tailWord_857782, baseEnd_857782] using wordTrace_append hprefix tailTrace_857782
  have hstable : (prefixWord ++ tailWord_857782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857782).length < 2 ^ (prefixWord ++ tailWord_857782).sum := by decide
  have hdescent : baseEnd_857782 < baseStart_857782 := by decide
  rcases family_descends (prefixWord ++ tailWord_857782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857852 : List Nat := [2, 2, 2, 1, 3, 1, 3, 2, 5]
def baseStart_857852 : Nat := 118140960795 + 857852 * 2 ^ 59
def prefixEnd_857852 : Nat := 4983230072969 + 3 ^ 40 * 857852 * 2
def baseEnd_857852 : Nat := 195773513964836837246585

theorem tailTrace_857852 : CollatzResearch.WordTrace tailWord_857852 prefixEnd_857852 195773513964836837246585 := by
  unfold tailWord_857852
  simp only [CollatzResearch.WordTrace]
  refine ⟨15644216444078094151247905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20858955258770792201663873 15644216444078094151247905)
  ·
    refine ⟨11733162333058570613435929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15644216444078094151247905 11733162333058570613435929)
    ·
      refine ⟨8799871749793927960076947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11733162333058570613435929 8799871749793927960076947)
      ·
        refine ⟨13199807624690891940115421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8799871749793927960076947 13199807624690891940115421)
        ·
          refine ⟨4949927859259084477543283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13199807624690891940115421 4949927859259084477543283)
          ·
            refine ⟨7424891788888626716314925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4949927859259084477543283 7424891788888626716314925)
            ·
              refine ⟨2784334420833235018618097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7424891788888626716314925 2784334420833235018618097)
              ·
                refine ⟨2088250815624926263963573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2784334420833235018618097 2088250815624926263963573)
                ·
                  refine ⟨195773513964836837246585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2088250815624926263963573 195773513964836837246585)
                  ·
                    rfl

theorem cell21_857852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_857852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_857852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_857852 prefixEnd_857852 := by exact prefixLift 857852
  have htrace : WordTrace (prefixWord ++ tailWord_857852) baseStart_857852 baseEnd_857852 := by
    simpa [prefixWord, tailWord_857852, baseEnd_857852] using wordTrace_append hprefix tailTrace_857852
  have hstable : (prefixWord ++ tailWord_857852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857852).length < 2 ^ (prefixWord ++ tailWord_857852).sum := by decide
  have hdescent : baseEnd_857852 < baseStart_857852 := by decide
  rcases family_descends (prefixWord ++ tailWord_857852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857900 : List Nat := [2, 2, 1, 1, 1, 6, 3, 1, 4]
def baseStart_857900 : Nat := 118140960795 + 857900 * 2 ^ 59
def prefixEnd_857900 : Nat := 4983230072969 + 3 ^ 40 * 857900 * 2
def baseEnd_857900 : Nat := 195784468218799420446487

theorem tailTrace_857900 : CollatzResearch.WordTrace tailWord_857900 prefixEnd_857900 195784468218799420446487 := by
  unfold tailWord_857900
  simp only [CollatzResearch.WordTrace]
  refine ⟨15645091795991146250121577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20860122394654861666828769 15645091795991146250121577)
  ·
    refine ⟨11733818846993359687591183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15645091795991146250121577 11733818846993359687591183)
    ·
      refine ⟨17600728270490039531386775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11733818846993359687591183 17600728270490039531386775)
      ·
        refine ⟨26401092405735059297080163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17600728270490039531386775 26401092405735059297080163)
        ·
          refine ⟨39601638608602588945620245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26401092405735059297080163 39601638608602588945620245)
          ·
            refine ⟨1856326809778246356825949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 39601638608602588945620245 1856326809778246356825949)
            ·
              refine ⟨696122553666842383809731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1856326809778246356825949 696122553666842383809731)
              ·
                refine ⟨1044183830500263575714597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 696122553666842383809731 1044183830500263575714597)
                ·
                  refine ⟨195784468218799420446487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1044183830500263575714597 195784468218799420446487)
                  ·
                    rfl

theorem cell21_857900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 4].length) (baseStart_857900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_857900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_857900 prefixEnd_857900 := by exact prefixLift 857900
  have htrace : WordTrace (prefixWord ++ tailWord_857900) baseStart_857900 baseEnd_857900 := by
    simpa [prefixWord, tailWord_857900, baseEnd_857900] using wordTrace_append hprefix tailTrace_857900
  have hstable : (prefixWord ++ tailWord_857900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857900).length < 2 ^ (prefixWord ++ tailWord_857900).sum := by decide
  have hdescent : baseEnd_857900 < baseStart_857900 := by decide
  rcases family_descends (prefixWord ++ tailWord_857900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857911 : List Nat := [1, 1, 3, 1, 2, 1, 2, 3, 7]
def baseStart_857911 : Nat := 118140960795 + 857911 * 2 ^ 59
def prefixEnd_857911 : Nat := 4983230072969 + 3 ^ 40 * 857911 * 2
def baseEnd_857911 : Nat := 195786978568665845763131

theorem tailTrace_857911 : CollatzResearch.WordTrace tailWord_857911 prefixEnd_857911 195786978568665845763131 := by
  unfold tailWord_857911
  simp only [CollatzResearch.WordTrace]
  refine ⟨31290584794942441378893587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20860389863294960919262391 31290584794942441378893587)
  ·
    refine ⟨46935877192413662068340381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31290584794942441378893587 46935877192413662068340381)
    ·
      refine ⟨17600953947155123275627643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46935877192413662068340381 17600953947155123275627643)
      ·
        refine ⟨26401430920732684913441465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17600953947155123275627643 26401430920732684913441465)
        ·
          refine ⟨19801073190549513685081099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26401430920732684913441465 19801073190549513685081099)
          ·
            refine ⟨29701609785824270527621649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19801073190549513685081099 29701609785824270527621649)
            ·
              refine ⟨22276207339368202895716237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29701609785824270527621649 22276207339368202895716237)
              ·
                refine ⟨8353577752263076085893589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22276207339368202895716237 8353577752263076085893589)
                ·
                  refine ⟨195786978568665845763131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8353577752263076085893589 195786978568665845763131)
                  ·
                    rfl

theorem cell21_857911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 7].length) (baseStart_857911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_857911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_857911 prefixEnd_857911 := by exact prefixLift 857911
  have htrace : WordTrace (prefixWord ++ tailWord_857911) baseStart_857911 baseEnd_857911 := by
    simpa [prefixWord, tailWord_857911, baseEnd_857911] using wordTrace_append hprefix tailTrace_857911
  have hstable : (prefixWord ++ tailWord_857911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857911).length < 2 ^ (prefixWord ++ tailWord_857911).sum := by decide
  have hdescent : baseEnd_857911 < baseStart_857911 := by decide
  rcases family_descends (prefixWord ++ tailWord_857911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857914 : List Nat := [3, 1, 1, 1, 5, 1, 4, 5]
def baseStart_857914 : Nat := 118140960795 + 857914 * 2 ^ 59
def prefixEnd_857914 : Nat := 4983230072969 + 3 ^ 40 * 857914 * 2
def baseEnd_857914 : Nat := 65262554403179502404375

theorem tailTrace_857914 : CollatzResearch.WordTrace tailWord_857914 prefixEnd_857914 65262554403179502404375 := by
  unfold tailWord_857914
  simp only [CollatzResearch.WordTrace]
  refine ⟨7822673553482893222813199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20860462809287715260835197 7822673553482893222813199)
  ·
    refine ⟨11734010330224339834219799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7822673553482893222813199 11734010330224339834219799)
    ·
      refine ⟨17601015495336509751329699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11734010330224339834219799 17601015495336509751329699)
      ·
        refine ⟨26401523243004764626994549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17601015495336509751329699 26401523243004764626994549)
        ·
          refine ⟨2475142804031696683780739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26401523243004764626994549 2475142804031696683780739)
          ·
            refine ⟨3712714206047545025671109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2475142804031696683780739 3712714206047545025671109)
            ·
              refine ⟨696133913633914692313333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3712714206047545025671109 696133913633914692313333)
              ·
                refine ⟨65262554403179502404375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 696133913633914692313333 65262554403179502404375)
                ·
                  rfl

theorem cell21_857914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 5].length) (baseStart_857914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_857914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_857914 prefixEnd_857914 := by exact prefixLift 857914
  have htrace : WordTrace (prefixWord ++ tailWord_857914) baseStart_857914 baseEnd_857914 := by
    simpa [prefixWord, tailWord_857914, baseEnd_857914] using wordTrace_append hprefix tailTrace_857914
  have hstable : (prefixWord ++ tailWord_857914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857914).length < 2 ^ (prefixWord ++ tailWord_857914).sum := by decide
  have hdescent : baseEnd_857914 < baseStart_857914 := by decide
  rcases family_descends (prefixWord ++ tailWord_857914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857959 : List Nat := [1, 1, 5, 1, 2, 1, 3, 3, 4]
def baseStart_857959 : Nat := 118140960795 + 857959 * 2 ^ 59
def prefixEnd_857959 : Nat := 4983230072969 + 3 ^ 40 * 857959 * 2
def baseEnd_857959 : Nat := 195797932822628428963033

theorem tailTrace_857959 : CollatzResearch.WordTrace tailWord_857959 prefixEnd_857959 195797932822628428963033 := by
  unfold tailWord_857959
  simp only [CollatzResearch.WordTrace]
  refine ⟨31292335498768545576640931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20861556999179030384427287 31292335498768545576640931)
  ·
    refine ⟨46938503248152818364961397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31292335498768545576640931 46938503248152818364961397)
    ·
      refine ⟨4400484679514326721715131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46938503248152818364961397 4400484679514326721715131)
      ·
        refine ⟨6600727019271490082572697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4400484679514326721715131 6600727019271490082572697)
        ·
          refine ⟨4950545264453617561929523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6600727019271490082572697 4950545264453617561929523)
          ·
            refine ⟨7425817896680426342894285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4950545264453617561929523 7425817896680426342894285)
            ·
              refine ⟨2784681711255159878585357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7425817896680426342894285 2784681711255159878585357)
              ·
                refine ⟨1044255641720684954469509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2784681711255159878585357 1044255641720684954469509)
                ·
                  refine ⟨195797932822628428963033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1044255641720684954469509 195797932822628428963033)
                  ·
                    rfl

theorem cell21_857959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 4].length) (baseStart_857959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_857959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_857959 prefixEnd_857959 := by exact prefixLift 857959
  have htrace : WordTrace (prefixWord ++ tailWord_857959) baseStart_857959 baseEnd_857959 := by
    simpa [prefixWord, tailWord_857959, baseEnd_857959] using wordTrace_append hprefix tailTrace_857959
  have hstable : (prefixWord ++ tailWord_857959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857959).length < 2 ^ (prefixWord ++ tailWord_857959).sum := by decide
  have hdescent : baseEnd_857959 < baseStart_857959 := by decide
  rcases family_descends (prefixWord ++ tailWord_857959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857973 : List Nat := [1, 3, 4, 1, 1, 1, 1, 9]
def baseStart_857973 : Nat := 118140960795 + 857973 * 2 ^ 59
def prefixEnd_857973 : Nat := 4983230072969 + 3 ^ 40 * 857973 * 2
def baseEnd_857973 : Nat := 65267042604455838576557

theorem tailTrace_857973 : CollatzResearch.WordTrace tailWord_857973 prefixEnd_857973 65267042604455838576557 := by
  unfold tailWord_857973
  simp only [CollatzResearch.WordTrace]
  refine ⟨31292846120717825967650573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20861897413811883978433715 31292846120717825967650573)
  ·
    refine ⟨11734817295269184737868965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31292846120717825967650573 11734817295269184737868965)
    ·
      refine ⟨2200278242862972138350431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11734817295269184737868965 2200278242862972138350431)
      ·
        refine ⟨3300417364294458207525647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2200278242862972138350431 3300417364294458207525647)
        ·
          refine ⟨4950626046441687311288471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3300417364294458207525647 4950626046441687311288471)
          ·
            refine ⟨7425939069662530966932707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4950626046441687311288471 7425939069662530966932707)
            ·
              refine ⟨11138908604493796450399061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7425939069662530966932707 11138908604493796450399061)
              ·
                refine ⟨65267042604455838576557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11138908604493796450399061 65267042604455838576557)
                ·
                  rfl

theorem cell21_857973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 9].length) (baseStart_857973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_857973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_857973 prefixEnd_857973 := by exact prefixLift 857973
  have htrace : WordTrace (prefixWord ++ tailWord_857973) baseStart_857973 baseEnd_857973 := by
    simpa [prefixWord, tailWord_857973, baseEnd_857973] using wordTrace_append hprefix tailTrace_857973
  have hstable : (prefixWord ++ tailWord_857973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857973).length < 2 ^ (prefixWord ++ tailWord_857973).sum := by decide
  have hdescent : baseEnd_857973 < baseStart_857973 := by decide
  rcases family_descends (prefixWord ++ tailWord_857973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858024 : List Nat := [2, 1, 6, 2, 1, 1, 3, 5]
def baseStart_858024 : Nat := 118140960795 + 858024 * 2 ^ 59
def prefixEnd_858024 : Nat := 4983230072969 + 3 ^ 40 * 858024 * 2
def baseEnd_858024 : Nat := 65270922236067586793189

theorem tailTrace_858024 : CollatzResearch.WordTrace tailWord_858024 prefixEnd_858024 65270922236067586793189 := by
  unfold tailWord_858024
  simp only [CollatzResearch.WordTrace]
  refine ⟨15647353121766530838878563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20863137495688707785171417 15647353121766530838878563)
  ·
    refine ⟨23471029682649796258317845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15647353121766530838878563 23471029682649796258317845)
    ·
      refine ⟨1100204516374209199608649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23471029682649796258317845 1100204516374209199608649)
      ·
        refine ⟨825153387280656899706487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1100204516374209199608649 825153387280656899706487)
        ·
          refine ⟨1237730080920985349559731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 825153387280656899706487 1237730080920985349559731)
          ·
            refine ⟨1856595121381478024339597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1237730080920985349559731 1856595121381478024339597)
            ·
              refine ⟨696223170518054259127349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1856595121381478024339597 696223170518054259127349)
              ·
                refine ⟨65270922236067586793189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 696223170518054259127349 65270922236067586793189)
                ·
                  rfl

theorem cell21_858024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 5].length) (baseStart_858024 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_858024 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_858024 prefixEnd_858024 := by exact prefixLift 858024
  have htrace : WordTrace (prefixWord ++ tailWord_858024) baseStart_858024 baseEnd_858024 := by
    simpa [prefixWord, tailWord_858024, baseEnd_858024] using wordTrace_append hprefix tailTrace_858024
  have hstable : (prefixWord ++ tailWord_858024).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858024).length < 2 ^ (prefixWord ++ tailWord_858024).sum := by decide
  have hdescent : baseEnd_858024 < baseStart_858024 := by decide
  rcases family_descends (prefixWord ++ tailWord_858024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858173 : List Nat := [1, 4, 1, 3, 1, 1, 3, 4, 3]
def baseStart_858173 : Nat := 118140960795 + 858173 * 2 ^ 59
def prefixEnd_858173 : Nat := 4983230072969 + 3 ^ 40 * 858173 * 2
def baseEnd_858173 : Nat := 195846770538211612395929

theorem tailTrace_858173 : CollatzResearch.WordTrace tailWord_858173 prefixEnd_858173 195846770538211612395929 := by
  unfold tailWord_858173
  simp only [CollatzResearch.WordTrace]
  refine ⟨31300140719993260124931173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20866760479995506749954115 31300140719993260124931173)
  ·
    refine ⟨5868776384998736273424595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31300140719993260124931173 5868776384998736273424595)
    ·
      refine ⟨8803164577498104410136893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5868776384998736273424595 8803164577498104410136893)
      ·
        refine ⟨3301186716561789153801335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8803164577498104410136893 3301186716561789153801335)
        ·
          refine ⟨4951780074842683730702003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3301186716561789153801335 4951780074842683730702003)
          ·
            refine ⟨7427670112264025596053005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4951780074842683730702003 7427670112264025596053005)
            ·
              refine ⟨2785376292099009598519877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7427670112264025596053005 2785376292099009598519877)
              ·
                refine ⟨522258054768564299722477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2785376292099009598519877 522258054768564299722477)
                ·
                  refine ⟨195846770538211612395929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 522258054768564299722477 195846770538211612395929)
                  ·
                    rfl

theorem cell21_858173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_858173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_858173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_858173 prefixEnd_858173 := by exact prefixLift 858173
  have htrace : WordTrace (prefixWord ++ tailWord_858173) baseStart_858173 baseEnd_858173 := by
    simpa [prefixWord, tailWord_858173, baseEnd_858173] using wordTrace_append hprefix tailTrace_858173
  have hstable : (prefixWord ++ tailWord_858173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858173).length < 2 ^ (prefixWord ++ tailWord_858173).sum := by decide
  have hdescent : baseEnd_858173 < baseStart_858173 := by decide
  rcases family_descends (prefixWord ++ tailWord_858173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858184 : List Nat := [2, 1, 3, 1, 1, 1, 2, 10]
def baseStart_858184 : Nat := 118140960795 + 858184 * 2 ^ 59
def prefixEnd_858184 : Nat := 4983230072969 + 3 ^ 40 * 858184 * 2
def baseEnd_858184 : Nat := 65283093629359345904191

theorem tailTrace_858184 : CollatzResearch.WordTrace tailWord_858184 prefixEnd_858184 65283093629359345904191 := by
  unfold tailWord_858184
  simp only [CollatzResearch.WordTrace]
  refine ⟨15650270961476704501790803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20867027948635606002387737 15650270961476704501790803)
  ·
    refine ⟨23475406442215056752686205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15650270961476704501790803 23475406442215056752686205)
    ·
      refine ⟨8803277415830646282257327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23475406442215056752686205 8803277415830646282257327)
      ·
        refine ⟨13204916123745969423385991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8803277415830646282257327 13204916123745969423385991)
        ·
          refine ⟨19807374185618954135078987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13204916123745969423385991 19807374185618954135078987)
          ·
            refine ⟨29711061278428431202618481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19807374185618954135078987 29711061278428431202618481)
            ·
              refine ⟨22283295958821323401963861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29711061278428431202618481 22283295958821323401963861)
              ·
                refine ⟨65283093629359345904191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 22283295958821323401963861 65283093629359345904191)
                ·
                  rfl

theorem cell21_858184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 10].length) (baseStart_858184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_858184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_858184 prefixEnd_858184 := by exact prefixLift 858184
  have htrace : WordTrace (prefixWord ++ tailWord_858184) baseStart_858184 baseEnd_858184 := by
    simpa [prefixWord, tailWord_858184, baseEnd_858184] using wordTrace_append hprefix tailTrace_858184
  have hstable : (prefixWord ++ tailWord_858184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858184).length < 2 ^ (prefixWord ++ tailWord_858184).sum := by decide
  have hdescent : baseEnd_858184 < baseStart_858184 := by decide
  rcases family_descends (prefixWord ++ tailWord_858184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858201 : List Nat := [1, 2, 1, 2, 2, 1, 7, 5]
def baseStart_858201 : Nat := 118140960795 + 858201 * 2 ^ 59
def prefixEnd_858201 : Nat := 4983230072969 + 3 ^ 40 * 858201 * 2
def baseEnd_858201 : Nat := 65284386839896595309735

theorem tailTrace_858201 : CollatzResearch.WordTrace tailWord_858201 prefixEnd_858201 65284386839896595309735 := by
  unfold tailWord_858201
  simp only [CollatzResearch.WordTrace]
  refine ⟨31301161963891820906950457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20867441309261213937966971 31301161963891820906950457)
  ·
    refine ⟨23475871472918865680212843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31301161963891820906950457 23475871472918865680212843)
    ·
      refine ⟨35213807209378298520319265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23475871472918865680212843 35213807209378298520319265)
      ·
        refine ⟨26410355407033723890239449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35213807209378298520319265 26410355407033723890239449)
        ·
          refine ⟨19807766555275292917679587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26410355407033723890239449 19807766555275292917679587)
          ·
            refine ⟨29711649832912939376519381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19807766555275292917679587 29711649832912939376519381)
            ·
              refine ⟨696366792958897016637173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 29711649832912939376519381 696366792958897016637173)
              ·
                refine ⟨65284386839896595309735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 696366792958897016637173 65284386839896595309735)
                ·
                  rfl

theorem cell21_858201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 5].length) (baseStart_858201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_858201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_858201 prefixEnd_858201 := by exact prefixLift 858201
  have htrace : WordTrace (prefixWord ++ tailWord_858201) baseStart_858201 baseEnd_858201 := by
    simpa [prefixWord, tailWord_858201, baseEnd_858201] using wordTrace_append hprefix tailTrace_858201
  have hstable : (prefixWord ++ tailWord_858201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858201).length < 2 ^ (prefixWord ++ tailWord_858201).sum := by decide
  have hdescent : baseEnd_858201 < baseStart_858201 := by decide
  rcases family_descends (prefixWord ++ tailWord_858201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858215 : List Nat := [1, 1, 5, 1, 1, 2, 1, 2, 7]
def baseStart_858215 : Nat := 118140960795 + 858215 * 2 ^ 59
def prefixEnd_858215 : Nat := 4983230072969 + 3 ^ 40 * 858215 * 2
def baseEnd_858215 : Nat := 195856355510428872695843

theorem tailTrace_858215 : CollatzResearch.WordTrace tailWord_858215 prefixEnd_858215 195856355510428872695843 := by
  unfold tailWord_858215
  simp only [CollatzResearch.WordTrace]
  refine ⟨31301672585841101297960099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20867781723894067531973399 31301672585841101297960099)
  ·
    refine ⟨46952508878761651946940149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31301672585841101297960099 46952508878761651946940149)
    ·
      refine ⟨4401797707383904870025639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46952508878761651946940149 4401797707383904870025639)
      ·
        refine ⟨6602696561075857305038459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4401797707383904870025639 6602696561075857305038459)
        ·
          refine ⟨9904044841613785957557689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6602696561075857305038459 9904044841613785957557689)
          ·
            refine ⟨7428033631210339468168267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9904044841613785957557689 7428033631210339468168267)
            ·
              refine ⟨11142050446815509202252401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7428033631210339468168267 11142050446815509202252401)
              ·
                refine ⟨8356537835111631901689301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11142050446815509202252401 8356537835111631901689301)
                ·
                  refine ⟨195856355510428872695843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8356537835111631901689301 195856355510428872695843)
                  ·
                    rfl

theorem cell21_858215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 7].length) (baseStart_858215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_858215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_858215 prefixEnd_858215 := by exact prefixLift 858215
  have htrace : WordTrace (prefixWord ++ tailWord_858215) baseStart_858215 baseEnd_858215 := by
    simpa [prefixWord, tailWord_858215, baseEnd_858215] using wordTrace_append hprefix tailTrace_858215
  have hstable : (prefixWord ++ tailWord_858215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858215).length < 2 ^ (prefixWord ++ tailWord_858215).sum := by decide
  have hdescent : baseEnd_858215 < baseStart_858215 := by decide
  rcases family_descends (prefixWord ++ tailWord_858215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858367 : List Nat := [1, 1, 2, 2, 1, 4, 3, 2, 5]
def baseStart_858367 : Nat := 118140960795 + 858367 * 2 ^ 59
def prefixEnd_858367 : Nat := 4983230072969 + 3 ^ 40 * 858367 * 2
def baseEnd_858367 : Nat := 195891043981310386162199

theorem tailTrace_858367 : CollatzResearch.WordTrace tailWord_858367 prefixEnd_858367 195891043981310386162199 := by
  unfold tailWord_858367
  simp only [CollatzResearch.WordTrace]
  refine ⟨31307216481290431257493355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20871477654193620838328903 31307216481290431257493355)
  ·
    refine ⟨46960824721935646886240033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31307216481290431257493355 46960824721935646886240033)
    ·
      refine ⟨35220618541451735164680025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46960824721935646886240033 35220618541451735164680025)
      ·
        refine ⟨26415463906088801373510019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35220618541451735164680025 26415463906088801373510019)
        ·
          refine ⟨39623195859133202060265029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26415463906088801373510019 39623195859133202060265029)
          ·
            refine ⟨7429349223587475386299693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39623195859133202060265029 7429349223587475386299693)
            ·
              refine ⟨2786005958845303269862385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7429349223587475386299693 2786005958845303269862385)
              ·
                refine ⟨2089504469133977452396789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2786005958845303269862385 2089504469133977452396789)
                ·
                  refine ⟨195891043981310386162199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2089504469133977452396789 195891043981310386162199)
                  ·
                    rfl

theorem cell21_858367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 5].length) (baseStart_858367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_858367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_858367 prefixEnd_858367 := by exact prefixLift 858367
  have htrace : WordTrace (prefixWord ++ tailWord_858367) baseStart_858367 baseEnd_858367 := by
    simpa [prefixWord, tailWord_858367, baseEnd_858367] using wordTrace_append hprefix tailTrace_858367
  have hstable : (prefixWord ++ tailWord_858367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858367).length < 2 ^ (prefixWord ++ tailWord_858367).sum := by decide
  have hdescent : baseEnd_858367 < baseStart_858367 := by decide
  rcases family_descends (prefixWord ++ tailWord_858367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858536 : List Nat := [2, 1, 6, 1, 1, 1, 1, 1, 7]
def baseStart_858536 : Nat := 118140960795 + 858536 * 2 ^ 59
def prefixEnd_858536 : Nat := 4983230072969 + 3 ^ 40 * 858536 * 2
def baseEnd_858536 : Nat := 195929612083803647845187

theorem tailTrace_858536 : CollatzResearch.WordTrace tailWord_858536 prefixEnd_858536 195929612083803647845187 := by
  unfold tailWord_858536
  simp only [CollatzResearch.WordTrace]
  refine ⟨15656690208839086560197731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20875586945118782080263641 15656690208839086560197731)
  ·
    refine ⟨23485035313258629840296597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15656690208839086560197731 23485035313258629840296597)
    ·
      refine ⟨1100861030308998273763903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23485035313258629840296597 1100861030308998273763903)
      ·
        refine ⟨1651291545463497410645855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1100861030308998273763903 1651291545463497410645855)
        ·
          refine ⟨2476937318195246115968783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1651291545463497410645855 2476937318195246115968783)
          ·
            refine ⟨3715405977292869173953175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2476937318195246115968783 3715405977292869173953175)
            ·
              refine ⟨5573108965939303760929763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3715405977292869173953175 5573108965939303760929763)
              ·
                refine ⟨8359663448908955641394645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5573108965939303760929763 8359663448908955641394645)
                ·
                  refine ⟨195929612083803647845187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8359663448908955641394645 195929612083803647845187)
                  ·
                    rfl

theorem cell21_858536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 7].length) (baseStart_858536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_858536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_858536 prefixEnd_858536 := by exact prefixLift 858536
  have htrace : WordTrace (prefixWord ++ tailWord_858536) baseStart_858536 baseEnd_858536 := by
    simpa [prefixWord, tailWord_858536, baseEnd_858536] using wordTrace_append hprefix tailTrace_858536
  have hstable : (prefixWord ++ tailWord_858536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858536).length < 2 ^ (prefixWord ++ tailWord_858536).sum := by decide
  have hdescent : baseEnd_858536 < baseStart_858536 := by decide
  rcases family_descends (prefixWord ++ tailWord_858536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858553 : List Nat := [1, 2, 1, 4, 3, 2, 2, 3, 3]
def baseStart_858553 : Nat := 118140960795 + 858553 * 2 ^ 59
def prefixEnd_858553 : Nat := 4983230072969 + 3 ^ 40 * 858553 * 2
def baseEnd_858553 : Nat := 195933491715415396061819

theorem tailTrace_858553 : CollatzResearch.WordTrace tailWord_858553 prefixEnd_858553 195933491715415396061819 := by
  unfold tailWord_858553
  simp only [CollatzResearch.WordTrace]
  refine ⟨31314000458616585023764313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20876000305744390015842875 31314000458616585023764313)
  ·
    refine ⟨23485500343962438767823235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31314000458616585023764313 23485500343962438767823235)
    ·
      refine ⟨35228250515943658151734853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23485500343962438767823235 35228250515943658151734853)
      ·
        refine ⟨6605296971739435903450285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35228250515943658151734853 6605296971739435903450285)
        ·
          refine ⟨2476986364402288463793857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6605296971739435903450285 2476986364402288463793857)
          ·
            refine ⟨1857739773301716347845393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2476986364402288463793857 1857739773301716347845393)
            ·
              refine ⟨1393304829976287260884045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1857739773301716347845393 1393304829976287260884045)
              ·
                refine ⟨522489311241107722831517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1393304829976287260884045 522489311241107722831517)
                ·
                  refine ⟨195933491715415396061819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 522489311241107722831517 195933491715415396061819)
                  ·
                    rfl

theorem cell21_858553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 3, 3].length) (baseStart_858553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_858553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_858553 prefixEnd_858553 := by exact prefixLift 858553
  have htrace : WordTrace (prefixWord ++ tailWord_858553) baseStart_858553 baseEnd_858553 := by
    simpa [prefixWord, tailWord_858553, baseEnd_858553] using wordTrace_append hprefix tailTrace_858553
  have hstable : (prefixWord ++ tailWord_858553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858553).length < 2 ^ (prefixWord ++ tailWord_858553).sum := by decide
  have hdescent : baseEnd_858553 < baseStart_858553 := by decide
  rcases family_descends (prefixWord ++ tailWord_858553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858567 : List Nat := [1, 1, 4, 1, 1, 6, 1, 2, 4]
def baseStart_858567 : Nat := 118140960795 + 858567 * 2 ^ 59
def prefixEnd_858567 : Nat := 4983230072969 + 3 ^ 40 * 858567 * 2
def baseEnd_858567 : Nat := 195936686706154482828457

theorem tailTrace_858567 : CollatzResearch.WordTrace tailWord_858567 prefixEnd_858567 195936686706154482828457 := by
  unfold tailWord_858567
  simp only [CollatzResearch.WordTrace]
  refine ⟨31314511080565865414773955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20876340720377243609849303 31314511080565865414773955)
  ·
    refine ⟨46971766620848798122160933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31314511080565865414773955 46971766620848798122160933)
    ·
      refine ⟨8807206241409149647905175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46971766620848798122160933 8807206241409149647905175)
      ·
        refine ⟨13210809362113724471857763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8807206241409149647905175 13210809362113724471857763)
        ·
          refine ⟨19816214043170586707786645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13210809362113724471857763 19816214043170586707786645)
          ·
            refine ⟨928885033273621251927499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19816214043170586707786645 928885033273621251927499)
            ·
              refine ⟨1393327549910431877891249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 928885033273621251927499 1393327549910431877891249)
              ·
                refine ⟨1044995662432823908418437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1393327549910431877891249 1044995662432823908418437)
                ·
                  refine ⟨195936686706154482828457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1044995662432823908418437 195936686706154482828457)
                  ·
                    rfl

theorem cell21_858567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 4].length) (baseStart_858567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_858567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_858567 prefixEnd_858567 := by exact prefixLift 858567
  have htrace : WordTrace (prefixWord ++ tailWord_858567) baseStart_858567 baseEnd_858567 := by
    simpa [prefixWord, tailWord_858567, baseEnd_858567] using wordTrace_append hprefix tailTrace_858567
  have hstable : (prefixWord ++ tailWord_858567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858567).length < 2 ^ (prefixWord ++ tailWord_858567).sum := by decide
  have hdescent : baseEnd_858567 < baseStart_858567 := by decide
  rcases family_descends (prefixWord ++ tailWord_858567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858609 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 8]
def baseStart_858609 : Nat := 118140960795 + 858609 * 2 ^ 59
def prefixEnd_858609 : Nat := 4983230072969 + 3 ^ 40 * 858609 * 2
def baseEnd_858609 : Nat := 195946271678371743128371

theorem tailTrace_858609 : CollatzResearch.WordTrace tailWord_858609 prefixEnd_858609 195946271678371743128371 := by
  unfold tailWord_858609
  simp only [CollatzResearch.WordTrace]
  refine ⟨31316042946413706587802881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20877361964275804391868587 31316042946413706587802881)
  ·
    refine ⟨23487032209810279940852161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31316042946413706587802881 23487032209810279940852161)
    ·
      refine ⟨17615274157357709955639121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23487032209810279940852161 17615274157357709955639121)
      ·
        refine ⟨13211455618018282466729341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17615274157357709955639121 13211455618018282466729341)
        ·
          refine ⟨4954295856756855925023503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13211455618018282466729341 4954295856756855925023503)
          ·
            refine ⟨7431443785135283887535255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4954295856756855925023503 7431443785135283887535255)
            ·
              refine ⟨11147165677702925831302883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7431443785135283887535255 11147165677702925831302883)
              ·
                refine ⟨16720748516554388746954325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11147165677702925831302883 16720748516554388746954325)
                ·
                  refine ⟨195946271678371743128371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16720748516554388746954325 195946271678371743128371)
                  ·
                    rfl

theorem cell21_858609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 8].length) (baseStart_858609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_858609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_858609 prefixEnd_858609 := by exact prefixLift 858609
  have htrace : WordTrace (prefixWord ++ tailWord_858609) baseStart_858609 baseEnd_858609 := by
    simpa [prefixWord, tailWord_858609, baseEnd_858609] using wordTrace_append hprefix tailTrace_858609
  have hstable : (prefixWord ++ tailWord_858609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858609).length < 2 ^ (prefixWord ++ tailWord_858609).sum := by decide
  have hdescent : baseEnd_858609 < baseStart_858609 := by decide
  rcases family_descends (prefixWord ++ tailWord_858609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858702 : List Nat := [4, 1, 1, 1, 1, 2, 4, 3, 4]
def baseStart_858702 : Nat := 118140960795 + 858702 * 2 ^ 59
def prefixEnd_858702 : Nat := 4983230072969 + 3 ^ 40 * 858702 * 2
def baseEnd_858702 : Nat := 195967495545424248078181

theorem tailTrace_858702 : CollatzResearch.WordTrace tailWord_858702 prefixEnd_858702 195967495545424248078181 := by
  unfold tailWord_858702
  simp only [CollatzResearch.WordTrace]
  refine ⟨3914929366884597933867295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20879623290051188980625573 3914929366884597933867295)
  ·
    refine ⟨5872394050326896900800943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3914929366884597933867295 5872394050326896900800943)
    ·
      refine ⟨8808591075490345351201415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5872394050326896900800943 8808591075490345351201415)
      ·
        refine ⟨13212886613235518026802123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8808591075490345351201415 13212886613235518026802123)
        ·
          refine ⟨19819329919853277040203185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13212886613235518026802123 19819329919853277040203185)
          ·
            refine ⟨14864497439889957780152389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19819329919853277040203185 14864497439889957780152389)
            ·
              refine ⟨2787093269979367083778573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14864497439889957780152389 2787093269979367083778573)
              ·
                refine ⟨1045159976242262656416965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2787093269979367083778573 1045159976242262656416965)
                ·
                  refine ⟨195967495545424248078181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1045159976242262656416965 195967495545424248078181)
                  ·
                    rfl

theorem cell21_858702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_858702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_858702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_858702 prefixEnd_858702 := by exact prefixLift 858702
  have htrace : WordTrace (prefixWord ++ tailWord_858702) baseStart_858702 baseEnd_858702 := by
    simpa [prefixWord, tailWord_858702, baseEnd_858702] using wordTrace_append hprefix tailTrace_858702
  have hstable : (prefixWord ++ tailWord_858702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858702).length < 2 ^ (prefixWord ++ tailWord_858702).sum := by decide
  have hdescent : baseEnd_858702 < baseStart_858702 := by decide
  rcases family_descends (prefixWord ++ tailWord_858702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858736 : List Nat := [2, 1, 1, 1, 8, 1, 1, 2, 4]
def baseStart_858736 : Nat := 118140960795 + 858736 * 2 ^ 59
def prefixEnd_858736 : Nat := 4983230072969 + 3 ^ 40 * 858736 * 2
def baseEnd_858736 : Nat := 195975254808647744511445

theorem tailTrace_858736 : CollatzResearch.WordTrace tailWord_858736 prefixEnd_858736 195975254808647744511445 := by
  unfold tailWord_858736
  simp only [CollatzResearch.WordTrace]
  refine ⟨15660337508476803638838031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20880450011302404851784041 15660337508476803638838031)
  ·
    refine ⟨23490506262715205458257047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15660337508476803638838031 23490506262715205458257047)
    ·
      refine ⟨35235759394072808187385571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23490506262715205458257047 35235759394072808187385571)
      ·
        refine ⟨52853639091109212281078357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35235759394072808187385571 52853639091109212281078357)
        ·
          refine ⟨619378583098936081418887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 52853639091109212281078357 619378583098936081418887)
          ·
            refine ⟨929067874648404122128331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619378583098936081418887 929067874648404122128331)
            ·
              refine ⟨1393601811972606183192497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 929067874648404122128331 1393601811972606183192497)
              ·
                refine ⟨1045201358979454637394373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1393601811972606183192497 1045201358979454637394373)
                ·
                  refine ⟨195975254808647744511445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1045201358979454637394373 195975254808647744511445)
                  ·
                    rfl

theorem cell21_858736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 4].length) (baseStart_858736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_858736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_858736 prefixEnd_858736 := by exact prefixLift 858736
  have htrace : WordTrace (prefixWord ++ tailWord_858736) baseStart_858736 baseEnd_858736 := by
    simpa [prefixWord, tailWord_858736, baseEnd_858736] using wordTrace_append hprefix tailTrace_858736
  have hstable : (prefixWord ++ tailWord_858736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858736).length < 2 ^ (prefixWord ++ tailWord_858736).sum := by decide
  have hdescent : baseEnd_858736 < baseStart_858736 := by decide
  rcases family_descends (prefixWord ++ tailWord_858736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858913 : List Nat := [1, 2, 3, 2, 1, 2, 3, 1, 6]
def baseStart_858913 : Nat := 118140960795 + 858913 * 2 ^ 59
def prefixEnd_858913 : Nat := 4983230072969 + 3 ^ 40 * 858913 * 2
def baseEnd_858913 : Nat := 196015648620134770061083

theorem tailTrace_858913 : CollatzResearch.WordTrace tailWord_858913 prefixEnd_858913 196015648620134770061083 := by
  unfold tailWord_858913
  simp only [CollatzResearch.WordTrace]
  refine ⟨31327130737312366506869393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20884753824874911004579595 31327130737312366506869393)
  ·
    refine ⟨23495348052984274880152045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31327130737312366506869393 23495348052984274880152045)
    ·
      refine ⟨8810755519869103080057017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23495348052984274880152045 8810755519869103080057017)
      ·
        refine ⟨6608066639901827310042763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8810755519869103080057017 6608066639901827310042763)
        ·
          refine ⟨9912099959852740965064145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6608066639901827310042763 9912099959852740965064145)
          ·
            refine ⟨7434074969889555723798109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9912099959852740965064145 7434074969889555723798109)
            ·
              refine ⟨2787778113708583396424291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7434074969889555723798109 2787778113708583396424291)
              ·
                refine ⟨4181667170562875094636437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2787778113708583396424291 4181667170562875094636437)
                ·
                  refine ⟨196015648620134770061083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4181667170562875094636437 196015648620134770061083)
                  ·
                    rfl

theorem cell21_858913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 6].length) (baseStart_858913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_858913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_858913 prefixEnd_858913 := by exact prefixLift 858913
  have htrace : WordTrace (prefixWord ++ tailWord_858913) baseStart_858913 baseEnd_858913 := by
    simpa [prefixWord, tailWord_858913, baseEnd_858913] using wordTrace_append hprefix tailTrace_858913
  have hstable : (prefixWord ++ tailWord_858913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858913).length < 2 ^ (prefixWord ++ tailWord_858913).sum := by decide
  have hdescent : baseEnd_858913 < baseStart_858913 := by decide
  rcases family_descends (prefixWord ++ tailWord_858913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858916 : List Nat := [2, 3, 1, 3, 3, 1, 2, 1, 5]
def baseStart_858916 : Nat := 118140960795 + 858916 * 2 ^ 59
def prefixEnd_858916 : Nat := 4983230072969 + 3 ^ 40 * 858916 * 2
def baseEnd_858916 : Nat := 196016333261007431511077

theorem tailTrace_858916 : CollatzResearch.WordTrace tailWord_858916 prefixEnd_858916 196016333261007431511077 := by
  unfold tailWord_858916
  simp only [CollatzResearch.WordTrace]
  refine ⟨15663620078150749009614301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20884826770867665346152401 15663620078150749009614301)
  ·
    refine ⟨5873857529306530878605363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15663620078150749009614301 5873857529306530878605363)
    ·
      refine ⟨8810786293959796317908045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5873857529306530878605363 8810786293959796317908045)
      ·
        refine ⟨3304044860234923619215517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8810786293959796317908045 3304044860234923619215517)
        ·
          refine ⟨1239016822588096357205819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3304044860234923619215517 1239016822588096357205819)
          ·
            refine ⟨1858525233882144535808729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1239016822588096357205819 1858525233882144535808729)
            ·
              refine ⟨1393893925411608401856547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1858525233882144535808729 1393893925411608401856547)
              ·
                refine ⟨2090840888117412602784821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1393893925411608401856547 2090840888117412602784821)
                ·
                  refine ⟨196016333261007431511077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2090840888117412602784821 196016333261007431511077)
                  ·
                    rfl

theorem cell21_858916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_858916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_858916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_858916 prefixEnd_858916 := by exact prefixLift 858916
  have htrace : WordTrace (prefixWord ++ tailWord_858916) baseStart_858916 baseEnd_858916 := by
    simpa [prefixWord, tailWord_858916, baseEnd_858916] using wordTrace_append hprefix tailTrace_858916
  have hstable : (prefixWord ++ tailWord_858916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858916).length < 2 ^ (prefixWord ++ tailWord_858916).sum := by decide
  have hdescent : baseEnd_858916 < baseStart_858916 := by decide
  rcases family_descends (prefixWord ++ tailWord_858916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858958 : List Nat := [4, 1, 1, 1, 1, 1, 1, 4, 7]
def baseStart_858958 : Nat := 118140960795 + 858958 * 2 ^ 59
def prefixEnd_858958 : Nat := 4983230072969 + 3 ^ 40 * 858958 * 2
def baseEnd_858958 : Nat := 196025918233224691810991

theorem tailTrace_858958 : CollatzResearch.WordTrace tailWord_858958 prefixEnd_858958 196025918233224691810991 := by
  unfold tailWord_858958
  simp only [CollatzResearch.WordTrace]
  refine ⟨3916096502768667399032191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20885848014766226128171685 3916096502768667399032191)
  ·
    refine ⟨5874144754153001098548287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3916096502768667399032191 5874144754153001098548287)
    ·
      refine ⟨8811217131229501647822431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5874144754153001098548287 8811217131229501647822431)
      ·
        refine ⟨13216825696844252471733647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8811217131229501647822431 13216825696844252471733647)
        ·
          refine ⟨19825238545266378707600471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13216825696844252471733647 19825238545266378707600471)
          ·
            refine ⟨29737857817899568061400707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19825238545266378707600471 29737857817899568061400707)
            ·
              refine ⟨44606786726849352092101061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29737857817899568061400707 44606786726849352092101061)
              ·
                refine ⟨8363772511284253517268949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44606786726849352092101061 8363772511284253517268949)
                ·
                  refine ⟨196025918233224691810991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8363772511284253517268949 196025918233224691810991)
                  ·
                    rfl

theorem cell21_858958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_858958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_858958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_858958 prefixEnd_858958 := by exact prefixLift 858958
  have htrace : WordTrace (prefixWord ++ tailWord_858958) baseStart_858958 baseEnd_858958 := by
    simpa [prefixWord, tailWord_858958, baseEnd_858958] using wordTrace_append hprefix tailTrace_858958
  have hstable : (prefixWord ++ tailWord_858958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858958).length < 2 ^ (prefixWord ++ tailWord_858958).sum := by decide
  have hdescent : baseEnd_858958 < baseStart_858958 := by decide
  rcases family_descends (prefixWord ++ tailWord_858958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858961 : List Nat := [1, 2, 2, 1, 7, 1, 7]
def baseStart_858961 : Nat := 118140960795 + 858961 * 2 ^ 59
def prefixEnd_858961 : Nat := 4983230072969 + 3 ^ 40 * 858961 * 2
def baseEnd_858961 : Nat := 21780733652677483695665

theorem tailTrace_858961 : CollatzResearch.WordTrace tailWord_858961 prefixEnd_858961 21780733652677483695665 := by
  unfold tailWord_858961
  simp only [CollatzResearch.WordTrace]
  refine ⟨31328881441138470704616737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20885920960758980469744491 31328881441138470704616737)
  ·
    refine ⟨23496661080853853028462553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31328881441138470704616737 23496661080853853028462553)
    ·
      refine ⟨17622495810640389771346915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23496661080853853028462553 17622495810640389771346915)
      ·
        refine ⟨26433743715960584657020373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17622495810640389771346915 26433743715960584657020373)
        ·
          refine ⟨619540868342826202898915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 26433743715960584657020373 619540868342826202898915)
          ·
            refine ⟨929311302514239304348373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619540868342826202898915 929311302514239304348373)
            ·
              refine ⟨21780733652677483695665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 929311302514239304348373 21780733652677483695665)
              ·
                rfl

theorem cell21_858961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 7].length) (baseStart_858961 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_858961 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_858961 prefixEnd_858961 := by exact prefixLift 858961
  have htrace : WordTrace (prefixWord ++ tailWord_858961) baseStart_858961 baseEnd_858961 := by
    simpa [prefixWord, tailWord_858961, baseEnd_858961] using wordTrace_append hprefix tailTrace_858961
  have hstable : (prefixWord ++ tailWord_858961).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858961).length < 2 ^ (prefixWord ++ tailWord_858961).sum := by decide
  have hdescent : baseEnd_858961 < baseStart_858961 := by decide
  rcases family_descends (prefixWord ++ tailWord_858961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859003 : List Nat := [1, 1, 1, 1, 1, 5, 4, 7]
def baseStart_859003 : Nat := 118140960795 + 859003 * 2 ^ 59
def prefixEnd_859003 : Nat := 4983230072969 + 3 ^ 40 * 859003 * 2
def baseEnd_859003 : Nat := 65345395948771537853633

theorem tailTrace_859003 : CollatzResearch.WordTrace tailWord_859003 prefixEnd_859003 65345395948771537853633 := by
  unfold tailWord_859003
  simp only [CollatzResearch.WordTrace]
  refine ⟨31330413306986311877645663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20886942204657541251763775 31330413306986311877645663)
  ·
    refine ⟨46995619960479467816468495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31330413306986311877645663 46995619960479467816468495)
    ·
      refine ⟨70493429940719201724702743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46995619960479467816468495 70493429940719201724702743)
      ·
        refine ⟨105740144911078802587054115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70493429940719201724702743 105740144911078802587054115)
        ·
          refine ⟨158610217366618203880581173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105740144911078802587054115 158610217366618203880581173)
          ·
            refine ⟨14869707878120456613804485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 158610217366618203880581173 14869707878120456613804485)
            ·
              refine ⟨2788070227147585615088341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14869707878120456613804485 2788070227147585615088341)
              ·
                refine ⟨65345395948771537853633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2788070227147585615088341 65345395948771537853633)
                ·
                  rfl

theorem cell21_859003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 7].length) (baseStart_859003 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_859003 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_859003 prefixEnd_859003 := by exact prefixLift 859003
  have htrace : WordTrace (prefixWord ++ tailWord_859003) baseStart_859003 baseEnd_859003 := by
    simpa [prefixWord, tailWord_859003, baseEnd_859003] using wordTrace_append hprefix tailTrace_859003
  have hstable : (prefixWord ++ tailWord_859003).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859003).length < 2 ^ (prefixWord ++ tailWord_859003).sum := by decide
  have hdescent : baseEnd_859003 < baseStart_859003 := by decide
  rcases family_descends (prefixWord ++ tailWord_859003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859141 : List Nat := [1, 3, 1, 1, 2, 3, 2, 4, 4]
def baseStart_859141 : Nat := 118140960795 + 859141 * 2 ^ 59
def prefixEnd_859141 : Nat := 4983230072969 + 3 ^ 40 * 859141 * 2
def baseEnd_859141 : Nat := 196067681326457040260617

theorem tailTrace_859141 : CollatzResearch.WordTrace tailWord_859141 prefixEnd_859141 196067681326457040260617 := by
  unfold tailWord_859141
  simp only [CollatzResearch.WordTrace]
  refine ⟨31335446580486361446169277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20890297720324240964112851 31335446580486361446169277)
  ·
    refine ⟨11750792467682385542313479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31335446580486361446169277 11750792467682385542313479)
    ·
      refine ⟨17626188701523578313470219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11750792467682385542313479 17626188701523578313470219)
      ·
        refine ⟨26439283052285367470205329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17626188701523578313470219 26439283052285367470205329)
        ·
          refine ⟨19829462289214025602653997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26439283052285367470205329 19829462289214025602653997)
          ·
            refine ⟨7436048358455259600995249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19829462289214025602653997 7436048358455259600995249)
            ·
              refine ⟨5577036268841444700746437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7436048358455259600995249 5577036268841444700746437)
              ·
                refine ⟨1045694300407770881389957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5577036268841444700746437 1045694300407770881389957)
                ·
                  refine ⟨196067681326457040260617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1045694300407770881389957 196067681326457040260617)
                  ·
                    rfl

theorem cell21_859141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_859141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_859141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_859141 prefixEnd_859141 := by exact prefixLift 859141
  have htrace : WordTrace (prefixWord ++ tailWord_859141) baseStart_859141 baseEnd_859141 := by
    simpa [prefixWord, tailWord_859141, baseEnd_859141] using wordTrace_append hprefix tailTrace_859141
  have hstable : (prefixWord ++ tailWord_859141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859141).length < 2 ^ (prefixWord ++ tailWord_859141).sum := by decide
  have hdescent : baseEnd_859141 < baseStart_859141 := by decide
  rcases family_descends (prefixWord ++ tailWord_859141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859172 : List Nat := [2, 3, 1, 4, 1, 1, 2, 7]
def baseStart_859172 : Nat := 118140960795 + 859172 * 2 ^ 59
def prefixEnd_859172 : Nat := 4983230072969 + 3 ^ 40 * 859172 * 2
def baseEnd_859172 : Nat := 65358251982935958414629

theorem tailTrace_859172 : CollatzResearch.WordTrace tailWord_859172 prefixEnd_859172 65358251982935958414629 := by
  unfold tailWord_859172
  simp only [CollatzResearch.WordTrace]
  refine ⟨15668288621687026870273885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20891051495582702493698513 15668288621687026870273885)
  ·
    refine ⟨5875608233132635076352707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15668288621687026870273885 5875608233132635076352707)
    ·
      refine ⟨8813412349698952614529061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5875608233132635076352707 8813412349698952614529061)
      ·
        refine ⟨1652514815568553615224199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8813412349698952614529061 1652514815568553615224199)
        ·
          refine ⟨2478772223352830422836299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1652514815568553615224199 2478772223352830422836299)
          ·
            refine ⟨3718158335029245634254449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2478772223352830422836299 3718158335029245634254449)
            ·
              refine ⟨2788618751271934225690837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3718158335029245634254449 2788618751271934225690837)
              ·
                refine ⟨65358251982935958414629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2788618751271934225690837 65358251982935958414629)
                ·
                  rfl

theorem cell21_859172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 7].length) (baseStart_859172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_859172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_859172 prefixEnd_859172 := by exact prefixLift 859172
  have htrace : WordTrace (prefixWord ++ tailWord_859172) baseStart_859172 baseEnd_859172 := by
    simpa [prefixWord, tailWord_859172, baseEnd_859172] using wordTrace_append hprefix tailTrace_859172
  have hstable : (prefixWord ++ tailWord_859172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859172).length < 2 ^ (prefixWord ++ tailWord_859172).sum := by decide
  have hdescent : baseEnd_859172 < baseStart_859172 := by decide
  rcases family_descends (prefixWord ++ tailWord_859172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859203 : List Nat := [1, 1, 1, 3, 1, 2, 5, 4, 3]
def baseStart_859203 : Nat := 118140960795 + 859203 * 2 ^ 59
def prefixEnd_859203 : Nat := 4983230072969 + 3 ^ 40 * 859203 * 2
def baseEnd_859203 : Nat := 196081830571158710227157

theorem tailTrace_859203 : CollatzResearch.WordTrace tailWord_859203 prefixEnd_859203 196081830571158710227157 := by
  unfold tailWord_859203
  simp only [CollatzResearch.WordTrace]
  refine ⟨31337707906261746034926263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20891805270841164023284175 31337707906261746034926263)
  ·
    refine ⟨47006561859392619052389395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31337707906261746034926263 47006561859392619052389395)
    ·
      refine ⟨70509842789088928578584093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47006561859392619052389395 70509842789088928578584093)
      ·
        refine ⟨26441191045908348216969035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70509842789088928578584093 26441191045908348216969035)
        ·
          refine ⟨39661786568862522325453553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26441191045908348216969035 39661786568862522325453553)
          ·
            refine ⟨29746339926646891744090165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39661786568862522325453553 29746339926646891744090165)
            ·
              refine ⟨2788719368123146101008453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29746339926646891744090165 2788719368123146101008453)
              ·
                refine ⟨522884881523089893939085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2788719368123146101008453 522884881523089893939085)
                ·
                  refine ⟨196081830571158710227157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 522884881523089893939085 196081830571158710227157)
                  ·
                    rfl

theorem cell21_859203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 4, 3].length) (baseStart_859203 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_859203 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_859203 prefixEnd_859203 := by exact prefixLift 859203
  have htrace : WordTrace (prefixWord ++ tailWord_859203) baseStart_859203 baseEnd_859203 := by
    simpa [prefixWord, tailWord_859203, baseEnd_859203] using wordTrace_append hprefix tailTrace_859203
  have hstable : (prefixWord ++ tailWord_859203).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859203).length < 2 ^ (prefixWord ++ tailWord_859203).sum := by decide
  have hdescent : baseEnd_859203 < baseStart_859203 := by decide
  rcases family_descends (prefixWord ++ tailWord_859203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859206 : List Nat := [6, 1, 1, 1, 1, 4, 1, 6]
def baseStart_859206 : Nat := 118140960795 + 859206 * 2 ^ 59
def prefixEnd_859206 : Nat := 4983230072969 + 3 ^ 40 * 859206 * 2
def baseEnd_859206 : Nat := 65360838404010457225717

theorem tailTrace_859206 : CollatzResearch.WordTrace tailWord_859206 prefixEnd_859206 65360838404010457225717 := by
  unfold tailWord_859206
  simp only [CollatzResearch.WordTrace]
  refine ⟨979306791414089923352671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20891878216833918364856981 979306791414089923352671)
  ·
    refine ⟨1468960187121134885029007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 979306791414089923352671 1468960187121134885029007)
    ·
      refine ⟨2203440280681702327543511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1468960187121134885029007 2203440280681702327543511)
      ·
        refine ⟨3305160421022553491315267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2203440280681702327543511 3305160421022553491315267)
        ·
          refine ⟨4957740631533830236972901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3305160421022553491315267 4957740631533830236972901)
          ·
            refine ⟨929576368412593169432419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4957740631533830236972901 929576368412593169432419)
            ·
              refine ⟨1394364552618889754148629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 929576368412593169432419 1394364552618889754148629)
              ·
                refine ⟨65360838404010457225717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1394364552618889754148629 65360838404010457225717)
                ·
                  rfl

theorem cell21_859206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_859206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_859206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_859206 prefixEnd_859206 := by exact prefixLift 859206
  have htrace : WordTrace (prefixWord ++ tailWord_859206) baseStart_859206 baseEnd_859206 := by
    simpa [prefixWord, tailWord_859206, baseEnd_859206] using wordTrace_append hprefix tailTrace_859206
  have hstable : (prefixWord ++ tailWord_859206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859206).length < 2 ^ (prefixWord ++ tailWord_859206).sum := by decide
  have hdescent : baseEnd_859206 < baseStart_859206 := by decide
  rcases family_descends (prefixWord ++ tailWord_859206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859217 : List Nat := [1, 2, 2, 1, 3, 1, 4, 3, 4]
def baseStart_859217 : Nat := 118140960795 + 859217 * 2 ^ 59
def prefixEnd_859217 : Nat := 4983230072969 + 3 ^ 40 * 859217 * 2
def baseEnd_859217 : Nat := 196085025561897796993795

theorem tailTrace_859217 : CollatzResearch.WordTrace tailWord_859217 prefixEnd_859217 196085025561897796993795 := by
  unfold tailWord_859217
  simp only [CollatzResearch.WordTrace]
  refine ⟨31338218528211026425935905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20892145685474017617290603 31338218528211026425935905)
  ·
    refine ⟨23503663896158269819451929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31338218528211026425935905 23503663896158269819451929)
    ·
      refine ⟨17627747922118702364588947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23503663896158269819451929 17627747922118702364588947)
      ·
        refine ⟨26441621883178053546883421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17627747922118702364588947 26441621883178053546883421)
        ·
          refine ⟨9915608206191770080081283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26441621883178053546883421 9915608206191770080081283)
          ·
            refine ⟨14873412309287655120121925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9915608206191770080081283 14873412309287655120121925)
            ·
              refine ⟨2788764807991435335022861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14873412309287655120121925 2788764807991435335022861)
              ·
                refine ⟨1045786802996788250633573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2788764807991435335022861 1045786802996788250633573)
                ·
                  refine ⟨196085025561897796993795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1045786802996788250633573 196085025561897796993795)
                  ·
                    rfl

theorem cell21_859217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 4].length) (baseStart_859217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_859217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_859217 prefixEnd_859217 := by exact prefixLift 859217
  have htrace : WordTrace (prefixWord ++ tailWord_859217) baseStart_859217 baseEnd_859217 := by
    simpa [prefixWord, tailWord_859217, baseEnd_859217] using wordTrace_append hprefix tailTrace_859217
  have hstable : (prefixWord ++ tailWord_859217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859217).length < 2 ^ (prefixWord ++ tailWord_859217).sum := by decide
  have hdescent : baseEnd_859217 < baseStart_859217 := by decide
  rcases family_descends (prefixWord ++ tailWord_859217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859313 : List Nat := [1, 2, 2, 5, 1, 2, 3, 2, 3]
def baseStart_859313 : Nat := 118140960795 + 859313 * 2 ^ 59
def prefixEnd_859313 : Nat := 4983230072969 + 3 ^ 40 * 859313 * 2
def baseEnd_859313 : Nat := 196106934069822963393599

theorem tailTrace_859313 : CollatzResearch.WordTrace tailWord_859313 prefixEnd_859313 196106934069822963393599 := by
  unfold tailWord_859313
  simp only [CollatzResearch.WordTrace]
  refine ⟨31341719935863234821430593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20894479957242156547620395 31341719935863234821430593)
  ·
    refine ⟨23506289951897426116072945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31341719935863234821430593 23506289951897426116072945)
    ·
      refine ⟨17629717463923069587054709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23506289951897426116072945 17629717463923069587054709)
      ·
        refine ⟨1652786012242787773786379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17629717463923069587054709 1652786012242787773786379)
        ·
          refine ⟨2479179018364181660679569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1652786012242787773786379 2479179018364181660679569)
          ·
            refine ⟨1859384263773136245509677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2479179018364181660679569 1859384263773136245509677)
            ·
              refine ⟨697269098914926092066129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1859384263773136245509677 697269098914926092066129)
              ·
                refine ⟨522951824186194569049597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 697269098914926092066129 522951824186194569049597)
                ·
                  refine ⟨196106934069822963393599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 522951824186194569049597 196106934069822963393599)
                  ·
                    rfl

theorem cell21_859313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 2, 3].length) (baseStart_859313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_859313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_859313 prefixEnd_859313 := by exact prefixLift 859313
  have htrace : WordTrace (prefixWord ++ tailWord_859313) baseStart_859313 baseEnd_859313 := by
    simpa [prefixWord, tailWord_859313, baseEnd_859313] using wordTrace_append hprefix tailTrace_859313
  have hstable : (prefixWord ++ tailWord_859313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859313).length < 2 ^ (prefixWord ++ tailWord_859313).sum := by decide
  have hdescent : baseEnd_859313 < baseStart_859313 := by decide
  rcases family_descends (prefixWord ++ tailWord_859313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859324 : List Nat := [2, 2, 2, 3, 2, 2, 2, 6]
def baseStart_859324 : Nat := 118140960795 + 859324 * 2 ^ 59
def prefixEnd_859324 : Nat := 4983230072969 + 3 ^ 40 * 859324 * 2
def baseEnd_859324 : Nat := 65369814806563129570081

theorem tailTrace_859324 : CollatzResearch.WordTrace tailWord_859324 prefixEnd_859324 65369814806563129570081 := by
  unfold tailWord_859324
  simp only [CollatzResearch.WordTrace]
  refine ⟨15671060569411691850040513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20894747425882255800054017 15671060569411691850040513)
  ·
    refine ⟨11753295427058768887530385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15671060569411691850040513 11753295427058768887530385)
    ·
      refine ⟨8814971570294076665647789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11753295427058768887530385 8814971570294076665647789)
      ·
        refine ⟨3305614338860278749617921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8814971570294076665647789 3305614338860278749617921)
        ·
          refine ⟨2479210754145209062213441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3305614338860278749617921 2479210754145209062213441)
          ·
            refine ⟨1859408065608906796660081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2479210754145209062213441 1859408065608906796660081)
            ·
              refine ⟨1394556049206680097495061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1859408065608906796660081 1394556049206680097495061)
              ·
                refine ⟨65369814806563129570081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1394556049206680097495061 65369814806563129570081)
                ·
                  rfl

theorem cell21_859324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 6].length) (baseStart_859324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_859324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_859324 prefixEnd_859324 := by exact prefixLift 859324
  have htrace : WordTrace (prefixWord ++ tailWord_859324) baseStart_859324 baseEnd_859324 := by
    simpa [prefixWord, tailWord_859324, baseEnd_859324] using wordTrace_append hprefix tailTrace_859324
  have hstable : (prefixWord ++ tailWord_859324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859324).length < 2 ^ (prefixWord ++ tailWord_859324).sum := by decide
  have hdescent : baseEnd_859324 < baseStart_859324 := by decide
  rcases family_descends (prefixWord ++ tailWord_859324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859372 : List Nat := [2, 2, 1, 1, 2, 4, 4, 2, 3]
def baseStart_859372 : Nat := 118140960795 + 859372 * 2 ^ 59
def prefixEnd_859372 : Nat := 4983230072969 + 3 ^ 40 * 859372 * 2
def baseEnd_859372 : Nat := 196120398673651971910145

theorem tailTrace_859372 : CollatzResearch.WordTrace tailWord_859372 prefixEnd_859372 196120398673651971910145 := by
  unfold tailWord_859372
  simp only [CollatzResearch.WordTrace]
  refine ⟨15671935921324743948914185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20895914561766325265218913 15671935921324743948914185)
  ·
    refine ⟨11753951940993557961685639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15671935921324743948914185 11753951940993557961685639)
    ·
      refine ⟨17630927911490336942528459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11753951940993557961685639 17630927911490336942528459)
      ·
        refine ⟨26446391867235505413792689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17630927911490336942528459 26446391867235505413792689)
        ·
          refine ⟨19834793900426629060344517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26446391867235505413792689 19834793900426629060344517)
          ·
            refine ⟨3719023856329992948814597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19834793900426629060344517 3719023856329992948814597)
            ·
              refine ⟨697316973061873677902737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3719023856329992948814597 697316973061873677902737)
              ·
                refine ⟨522987729796405258427053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 697316973061873677902737 522987729796405258427053)
                ·
                  refine ⟨196120398673651971910145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 522987729796405258427053 196120398673651971910145)
                  ·
                    rfl

theorem cell21_859372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 2, 3].length) (baseStart_859372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_859372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_859372 prefixEnd_859372 := by exact prefixLift 859372
  have htrace : WordTrace (prefixWord ++ tailWord_859372) baseStart_859372 baseEnd_859372 := by
    simpa [prefixWord, tailWord_859372, baseEnd_859372] using wordTrace_append hprefix tailTrace_859372
  have hstable : (prefixWord ++ tailWord_859372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859372).length < 2 ^ (prefixWord ++ tailWord_859372).sum := by decide
  have hdescent : baseEnd_859372 < baseStart_859372 := by decide
  rcases family_descends (prefixWord ++ tailWord_859372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859496 : List Nat := [2, 1, 4, 2, 4, 1, 2, 1, 4]
def baseStart_859496 : Nat := 118140960795 + 859496 * 2 ^ 59
def prefixEnd_859496 : Nat := 4983230072969 + 3 ^ 40 * 859496 * 2
def baseEnd_859496 : Nat := 196148697163055311843225

theorem tailTrace_859496 : CollatzResearch.WordTrace tailWord_859496 prefixEnd_859496 196148697163055311843225 := by
  unfold tailWord_859496
  simp only [CollatzResearch.WordTrace]
  refine ⟨15674197247100128537671171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20898929662800171383561561 15674197247100128537671171)
  ·
    refine ⟨23511295870650192806506757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15674197247100128537671171 23511295870650192806506757)
    ·
      refine ⟨4408367975746911151220017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23511295870650192806506757 4408367975746911151220017)
      ·
        refine ⟨3306275981810183363415013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4408367975746911151220017 3306275981810183363415013)
        ·
          refine ⟨619926746589409380640315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3306275981810183363415013 619926746589409380640315)
          ·
            refine ⟨929890119884114070960473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619926746589409380640315 929890119884114070960473)
            ·
              refine ⟨697417589913085553220355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 929890119884114070960473 697417589913085553220355)
              ·
                refine ⟨1046126384869628329830533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 697417589913085553220355 1046126384869628329830533)
                ·
                  refine ⟨196148697163055311843225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1046126384869628329830533 196148697163055311843225)
                  ·
                    rfl

theorem cell21_859496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 4].length) (baseStart_859496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_859496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_859496 prefixEnd_859496 := by exact prefixLift 859496
  have htrace : WordTrace (prefixWord ++ tailWord_859496) baseStart_859496 baseEnd_859496 := by
    simpa [prefixWord, tailWord_859496, baseEnd_859496] using wordTrace_append hprefix tailTrace_859496
  have hstable : (prefixWord ++ tailWord_859496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859496).length < 2 ^ (prefixWord ++ tailWord_859496).sum := by decide
  have hdescent : baseEnd_859496 < baseStart_859496 := by decide
  rcases family_descends (prefixWord ++ tailWord_859496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859656 : List Nat := [2, 1, 3, 2, 1, 1, 4, 1, 6]
def baseStart_859656 : Nat := 118140960795 + 859656 * 2 ^ 59
def prefixEnd_859656 : Nat := 4983230072969 + 3 ^ 40 * 859656 * 2
def baseEnd_859656 : Nat := 196185211342930589176231

theorem tailTrace_859656 : CollatzResearch.WordTrace tailWord_859656 prefixEnd_859656 196185211342930589176231 := by
  unfold tailWord_859656
  simp only [CollatzResearch.WordTrace]
  refine ⟨15677115086810302200583411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20902820115747069600777881 15677115086810302200583411)
  ·
    refine ⟨23515672630215453300875117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15677115086810302200583411 23515672630215453300875117)
    ·
      refine ⟨8818377236330794987828169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23515672630215453300875117 8818377236330794987828169)
      ·
        refine ⟨6613782927248096240871127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8818377236330794987828169 6613782927248096240871127)
        ·
          refine ⟨9920674390872144361306691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6613782927248096240871127 9920674390872144361306691)
          ·
            refine ⟨14881011586308216541960037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9920674390872144361306691 14881011586308216541960037)
            ·
              refine ⟨2790189672432790601617507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14881011586308216541960037 2790189672432790601617507)
              ·
                refine ⟨4185284508649185902426261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2790189672432790601617507 4185284508649185902426261)
                ·
                  refine ⟨196185211342930589176231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4185284508649185902426261 196185211342930589176231)
                  ·
                    rfl

theorem cell21_859656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 6].length) (baseStart_859656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_859656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_859656 prefixEnd_859656 := by exact prefixLift 859656
  have htrace : WordTrace (prefixWord ++ tailWord_859656) baseStart_859656 baseEnd_859656 := by
    simpa [prefixWord, tailWord_859656, baseEnd_859656] using wordTrace_append hprefix tailTrace_859656
  have hstable : (prefixWord ++ tailWord_859656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859656).length < 2 ^ (prefixWord ++ tailWord_859656).sum := by decide
  have hdescent : baseEnd_859656 < baseStart_859656 := by decide
  rcases family_descends (prefixWord ++ tailWord_859656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859659 : List Nat := [1, 1, 1, 1, 8, 2, 1, 1, 5]
def baseStart_859659 : Nat := 118140960795 + 859659 * 2 ^ 59
def prefixEnd_859659 : Nat := 4983230072969 + 3 ^ 40 * 859659 * 2
def baseEnd_859659 : Nat := 196185895983803250626225

theorem tailTrace_859659 : CollatzResearch.WordTrace tailWord_859659 prefixEnd_859659 196185895983803250626225 := by
  unfold tailWord_859659
  simp only [CollatzResearch.WordTrace]
  refine ⟨31354339592609735913526031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20902893061739823942350687 31354339592609735913526031)
  ·
    refine ⟨47031509388914603870289047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31354339592609735913526031 47031509388914603870289047)
    ·
      refine ⟨70547264083371905805433571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47031509388914603870289047 70547264083371905805433571)
      ·
        refine ⟨105820896125057858708150357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70547264083371905805433571 105820896125057858708150357)
        ·
          refine ⟨1240088626465521781736137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 105820896125057858708150357 1240088626465521781736137)
          ·
            refine ⟨930066469849141336302103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1240088626465521781736137 930066469849141336302103)
            ·
              refine ⟨1395099704773712004453155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 930066469849141336302103 1395099704773712004453155)
              ·
                refine ⟨2092649557160568006679733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1395099704773712004453155 2092649557160568006679733)
                ·
                  refine ⟨196185895983803250626225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2092649557160568006679733 196185895983803250626225)
                  ·
                    rfl

theorem cell21_859659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 5].length) (baseStart_859659 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_859659 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_859659 prefixEnd_859659 := by exact prefixLift 859659
  have htrace : WordTrace (prefixWord ++ tailWord_859659) baseStart_859659 baseEnd_859659 := by
    simpa [prefixWord, tailWord_859659, baseEnd_859659] using wordTrace_append hprefix tailTrace_859659
  have hstable : (prefixWord ++ tailWord_859659).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859659).length < 2 ^ (prefixWord ++ tailWord_859659).sum := by decide
  have hdescent : baseEnd_859659 < baseStart_859659 := by decide
  rcases family_descends (prefixWord ++ tailWord_859659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859752 : List Nat := [2, 1, 4, 3, 1, 2, 2, 3, 3]
def baseStart_859752 : Nat := 118140960795 + 859752 * 2 ^ 59
def prefixEnd_859752 : Nat := 4983230072969 + 3 ^ 40 * 859752 * 2
def baseEnd_859752 : Nat := 196207119850855755576035

theorem tailTrace_859752 : CollatzResearch.WordTrace tailWord_859752 prefixEnd_859752 196207119850855755576035 := by
  unfold tailWord_859752
  simp only [CollatzResearch.WordTrace]
  refine ⟨15678865790636406398330755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20905154387515208531107673 15678865790636406398330755)
  ·
    refine ⟨23518298685954609597496133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15678865790636406398330755 23518298685954609597496133)
    ·
      refine ⟨4409681003616489299530525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23518298685954609597496133 4409681003616489299530525)
      ·
        refine ⟨1653630376356183487323947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4409681003616489299530525 1653630376356183487323947)
        ·
          refine ⟨2480445564534275230985921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1653630376356183487323947 2480445564534275230985921)
          ·
            refine ⟨1860334173400706423239441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2480445564534275230985921 1860334173400706423239441)
            ·
              refine ⟨1395250630050529817429581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1860334173400706423239441 1395250630050529817429581)
              ·
                refine ⟨523218986268948681536093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1395250630050529817429581 523218986268948681536093)
                ·
                  refine ⟨196207119850855755576035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 523218986268948681536093 196207119850855755576035)
                  ·
                    rfl

theorem cell21_859752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 3, 3].length) (baseStart_859752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_859752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_859752 prefixEnd_859752 := by exact prefixLift 859752
  have htrace : WordTrace (prefixWord ++ tailWord_859752) baseStart_859752 baseEnd_859752 := by
    simpa [prefixWord, tailWord_859752, baseEnd_859752] using wordTrace_append hprefix tailTrace_859752
  have hstable : (prefixWord ++ tailWord_859752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859752).length < 2 ^ (prefixWord ++ tailWord_859752).sum := by decide
  have hdescent : baseEnd_859752 < baseStart_859752 := by decide
  rcases family_descends (prefixWord ++ tailWord_859752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
