import V185TrunkScan22Chunk207

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1855066 : List Nat := [3, 1, 1, 2, 1, 1, 1, 6, 1, 5]
def baseStart_1855066 : Nat := 118140960795 + 1855066 * 2 ^ 59
def prefixEnd_1855066 : Nat := 4983230072969 + 3 ^ 40 * 1855066 * 2
def baseEnd_1855066 : Nat := 635027002542362852962475

theorem tailTrace_1855066 : CollatzResearch.WordTrace tailWord_1855066 prefixEnd_1855066 635027002542362852962475 := by
  unfold tailWord_1855066
  simp only [CollatzResearch.WordTrace]
  refine ⟨16914953874355044223644263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45106543664946784596384701 16914953874355044223644263)
  ·
    refine ⟨25372430811532566335466395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16914953874355044223644263 25372430811532566335466395)
    ·
      refine ⟨38058646217298849503199593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25372430811532566335466395 38058646217298849503199593)
      ·
        refine ⟨28543984662974137127399695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38058646217298849503199593 28543984662974137127399695)
        ·
          refine ⟨42815976994461205691099543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28543984662974137127399695 42815976994461205691099543)
          ·
            refine ⟨64223965491691808536649315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42815976994461205691099543 64223965491691808536649315)
            ·
              refine ⟨96335948237537712804973973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64223965491691808536649315 96335948237537712804973973)
              ·
                refine ⟨4515747573634580287733155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96335948237537712804973973 4515747573634580287733155)
                ·
                  refine ⟨6773621360451870431599733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4515747573634580287733155 6773621360451870431599733)
                  ·
                    refine ⟨635027002542362852962475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6773621360451870431599733 635027002542362852962475)
                    ·
                      rfl

theorem cell22_1855066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_1855066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1855066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1855066 prefixEnd_1855066 := by exact prefixLift 1855066
  have htrace : WordTrace (prefixWord ++ tailWord_1855066) baseStart_1855066 baseEnd_1855066 := by
    simpa [prefixWord, tailWord_1855066, baseEnd_1855066] using wordTrace_append hprefix tailTrace_1855066
  have hstable : (prefixWord ++ tailWord_1855066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855066).length < 2 ^ (prefixWord ++ tailWord_1855066).sum := by decide
  have hdescent : baseEnd_1855066 < baseStart_1855066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855081 : List Nat := [1, 2, 1, 1, 1, 4, 3, 1, 4, 4]
def baseStart_1855081 : Nat := 118140960795 + 1855081 * 2 ^ 59
def prefixEnd_1855081 : Nat := 4983230072969 + 3 ^ 40 * 1855081 * 2
def baseEnd_1855081 : Nat := 635032137348907813837429

theorem tailTrace_1855081 : CollatzResearch.WordTrace tailWord_1855081 prefixEnd_1855081 635032137348907813837429 := by
  unfold tailWord_1855081
  simp only [CollatzResearch.WordTrace]
  refine ⟨67660362592365834456373097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45106908394910556304248731 67660362592365834456373097)
  ·
    refine ⟨50745271944274375842279823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67660362592365834456373097 50745271944274375842279823)
    ·
      refine ⟨76117907916411563763419735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50745271944274375842279823 76117907916411563763419735)
      ·
        refine ⟨114176861874617345645129603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76117907916411563763419735 114176861874617345645129603)
        ·
          refine ⟨171265292811926018467694405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114176861874617345645129603 171265292811926018467694405)
          ·
            refine ⟨32112242402236128462692701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171265292811926018467694405 32112242402236128462692701)
            ·
              refine ⟨12042090900838548173509763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32112242402236128462692701 12042090900838548173509763)
              ·
                refine ⟨18063136351257822260264645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12042090900838548173509763 18063136351257822260264645)
                ·
                  refine ⟨3386838065860841673799621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18063136351257822260264645 3386838065860841673799621)
                  ·
                    refine ⟨635032137348907813837429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3386838065860841673799621 635032137348907813837429)
                    ·
                      rfl

theorem cell22_1855081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 4].length) (baseStart_1855081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1855081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1855081 prefixEnd_1855081 := by exact prefixLift 1855081
  have htrace : WordTrace (prefixWord ++ tailWord_1855081) baseStart_1855081 baseEnd_1855081 := by
    simpa [prefixWord, tailWord_1855081, baseEnd_1855081] using wordTrace_append hprefix tailTrace_1855081
  have hstable : (prefixWord ++ tailWord_1855081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855081).length < 2 ^ (prefixWord ++ tailWord_1855081).sum := by decide
  have hdescent : baseEnd_1855081 < baseStart_1855081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855085 : List Nat := [1, 5, 1, 1, 4, 2, 1, 1, 6]
def baseStart_1855085 : Nat := 118140960795 + 1855085 * 2 ^ 59
def prefixEnd_1855085 : Nat := 4983230072969 + 3 ^ 40 * 1855085 * 2
def baseEnd_1855085 : Nat := 211677835543551045579139

theorem tailTrace_1855085 : CollatzResearch.WordTrace tailWord_1855085 prefixEnd_1855085 211677835543551045579139 := by
  unfold tailWord_1855085
  simp only [CollatzResearch.WordTrace]
  refine ⟨67660508484351343139518709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45107005656234228759679139 67660508484351343139518709)
  ·
    refine ⟨6343172670407938419329879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67660508484351343139518709 6343172670407938419329879)
    ·
      refine ⟨9514759005611907628994819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6343172670407938419329879 9514759005611907628994819)
      ·
        refine ⟨14272138508417861443492229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9514759005611907628994819 14272138508417861443492229)
        ·
          refine ⟨2676025970328349020654793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14272138508417861443492229 2676025970328349020654793)
          ·
            refine ⟨2007019477746261765491095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2676025970328349020654793 2007019477746261765491095)
            ·
              refine ⟨3010529216619392648236643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2007019477746261765491095 3010529216619392648236643)
              ·
                refine ⟨4515793824929088972354965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3010529216619392648236643 4515793824929088972354965)
                ·
                  refine ⟨211677835543551045579139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4515793824929088972354965 211677835543551045579139)
                  ·
                    rfl

theorem cell22_1855085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_1855085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1855085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1855085 prefixEnd_1855085 := by exact prefixLift 1855085
  have htrace : WordTrace (prefixWord ++ tailWord_1855085) baseStart_1855085 baseEnd_1855085 := by
    simpa [prefixWord, tailWord_1855085, baseEnd_1855085] using wordTrace_append hprefix tailTrace_1855085
  have hstable : (prefixWord ++ tailWord_1855085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855085).length < 2 ^ (prefixWord ++ tailWord_1855085).sum := by decide
  have hdescent : baseEnd_1855085 < baseStart_1855085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855141 : List Nat := [1, 3, 1, 2, 1, 2, 2, 3, 7]
def baseStart_1855141 : Nat := 118140960795 + 1855141 * 2 ^ 59
def prefixEnd_1855141 : Nat := 4983230072969 + 3 ^ 40 * 1855141 * 2
def baseEnd_1855141 : Nat := 211684225525029219112415

theorem tailTrace_1855141 : CollatzResearch.WordTrace tailWord_1855141 prefixEnd_1855141 211684225525029219112415 := by
  unfold tailWord_1855141
  simp only [CollatzResearch.WordTrace]
  refine ⟨67662550972148464703557277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45108367314765643135704851 67662550972148464703557277)
  ·
    refine ⟨25373456614555674263833979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67662550972148464703557277 25373456614555674263833979)
    ·
      refine ⟨38060184921833511395750969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25373456614555674263833979 38060184921833511395750969)
      ·
        refine ⟨28545138691375133546813227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38060184921833511395750969 28545138691375133546813227)
        ·
          refine ⟨42817708037062700320219841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28545138691375133546813227 42817708037062700320219841)
          ·
            refine ⟨32113281027797025240164881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42817708037062700320219841 32113281027797025240164881)
            ·
              refine ⟨24084960770847768930123661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32113281027797025240164881 24084960770847768930123661)
              ·
                refine ⟨9031860289067913348796373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24084960770847768930123661 9031860289067913348796373)
                ·
                  refine ⟨211684225525029219112415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9031860289067913348796373 211684225525029219112415)
                  ·
                    rfl

theorem cell22_1855141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 7].length) (baseStart_1855141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1855141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1855141 prefixEnd_1855141 := by exact prefixLift 1855141
  have htrace : WordTrace (prefixWord ++ tailWord_1855141) baseStart_1855141 baseEnd_1855141 := by
    simpa [prefixWord, tailWord_1855141, baseEnd_1855141] using wordTrace_append hprefix tailTrace_1855141
  have hstable : (prefixWord ++ tailWord_1855141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855141).length < 2 ^ (prefixWord ++ tailWord_1855141).sum := by decide
  have hdescent : baseEnd_1855141 < baseStart_1855141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855222 : List Nat := [5, 1, 1, 1, 1, 4, 2, 2, 1, 4]
def baseStart_1855222 : Nat := 118140960795 + 1855222 * 2 ^ 59
def prefixEnd_1855222 : Nat := 4983230072969 + 3 ^ 40 * 1855222 * 2
def baseEnd_1855222 : Nat := 635080404530430446061997

theorem tailTrace_1855222 : CollatzResearch.WordTrace tailWord_1855222 prefixEnd_1855222 635080404530430446061997 := by
  unfold tailWord_1855222
  simp only [CollatzResearch.WordTrace]
  refine ⟨4229094080303438471078495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45110336856570010358170613 4229094080303438471078495)
  ·
    refine ⟨6343641120455157706617743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4229094080303438471078495 6343641120455157706617743)
    ·
      refine ⟨9515461680682736559926615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6343641120455157706617743 9515461680682736559926615)
      ·
        refine ⟨14273192521024104839889923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9515461680682736559926615 14273192521024104839889923)
        ·
          refine ⟨21409788781536157259834885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14273192521024104839889923 21409788781536157259834885)
          ·
            refine ⟨4014335396538029486219041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21409788781536157259834885 4014335396538029486219041)
            ·
              refine ⟨3010751547403522114664281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4014335396538029486219041 3010751547403522114664281)
              ·
                refine ⟨2258063660552641585998211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3010751547403522114664281 2258063660552641585998211)
                ·
                  refine ⟨3387095490828962378997317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2258063660552641585998211 3387095490828962378997317)
                  ·
                    refine ⟨635080404530430446061997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3387095490828962378997317 635080404530430446061997)
                    ·
                      rfl

theorem cell22_1855222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_1855222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1855222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1855222 prefixEnd_1855222 := by exact prefixLift 1855222
  have htrace : WordTrace (prefixWord ++ tailWord_1855222) baseStart_1855222 baseEnd_1855222 := by
    simpa [prefixWord, tailWord_1855222, baseEnd_1855222] using wordTrace_append hprefix tailTrace_1855222
  have hstable : (prefixWord ++ tailWord_1855222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855222).length < 2 ^ (prefixWord ++ tailWord_1855222).sum := by decide
  have hdescent : baseEnd_1855222 < baseStart_1855222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855233 : List Nat := [1, 2, 4, 1, 1, 1, 4, 1, 1, 6]
def baseStart_1855233 : Nat := 118140960795 + 1855233 * 2 ^ 59
def prefixEnd_1855233 : Nat := 4983230072969 + 3 ^ 40 * 1855233 * 2
def baseEnd_1855233 : Nat := 635084170055230084036963

theorem tailTrace_1855233 : CollatzResearch.WordTrace tailWord_1855233 prefixEnd_1855233 635084170055230084036963 := by
  unfold tailWord_1855233
  simp only [CollatzResearch.WordTrace]
  refine ⟨67665906487815164415906353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45110604325210109610604235 67665906487815164415906353)
  ·
    refine ⟨50749429865861373311929765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67665906487815164415906353 50749429865861373311929765)
    ·
      refine ⟨9515518099849007495986831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50749429865861373311929765 9515518099849007495986831)
      ·
        refine ⟨14273277149773511243980247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9515518099849007495986831 14273277149773511243980247)
        ·
          refine ⟨21409915724660266865970371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14273277149773511243980247 21409915724660266865970371)
          ·
            refine ⟨32114873586990400298955557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21409915724660266865970371 32114873586990400298955557)
            ·
              refine ⟨6021538797560700056054167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32114873586990400298955557 6021538797560700056054167)
              ·
                refine ⟨9032308196341050084081251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6021538797560700056054167 9032308196341050084081251)
                ·
                  refine ⟨13548462294511575126121877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9032308196341050084081251 13548462294511575126121877)
                  ·
                    refine ⟨635084170055230084036963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13548462294511575126121877 635084170055230084036963)
                    ·
                      rfl

theorem cell22_1855233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_1855233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1855233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1855233 prefixEnd_1855233 := by exact prefixLift 1855233
  have htrace : WordTrace (prefixWord ++ tailWord_1855233) baseStart_1855233 baseEnd_1855233 := by
    simpa [prefixWord, tailWord_1855233, baseEnd_1855233] using wordTrace_append hprefix tailTrace_1855233
  have hstable : (prefixWord ++ tailWord_1855233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855233).length < 2 ^ (prefixWord ++ tailWord_1855233).sum := by decide
  have hdescent : baseEnd_1855233 < baseStart_1855233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855269 : List Nat := [1, 3, 1, 2, 3, 4, 2, 1, 2, 3]
def baseStart_1855269 : Nat := 118140960795 + 1855269 * 2 ^ 59
def prefixEnd_1855269 : Nat := 4983230072969 + 3 ^ 40 * 1855269 * 2
def baseEnd_1855269 : Nat := 635096493590937990136853

theorem tailTrace_1855269 : CollatzResearch.WordTrace tailWord_1855269 prefixEnd_1855269 635096493590937990136853 := by
  unfold tailWord_1855269
  simp only [CollatzResearch.WordTrace]
  refine ⟨67667219515684742564216861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45111479677123161709477907 67667219515684742564216861)
  ·
    refine ⟨25375207318381778461581323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67667219515684742564216861 25375207318381778461581323)
    ·
      refine ⟨38062810977572667692371985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25375207318381778461581323 38062810977572667692371985)
      ·
        refine ⟨28547108233179500769278989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38062810977572667692371985 28547108233179500769278989)
        ·
          refine ⟨10705165587442312788479621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28547108233179500769278989 10705165587442312788479621)
          ·
            refine ⟨2007218547645433647839929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10705165587442312788479621 2007218547645433647839929)
            ·
              refine ⟨1505413910734075235879947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2007218547645433647839929 1505413910734075235879947)
              ·
                refine ⟨2258120866101112853819921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1505413910734075235879947 2258120866101112853819921)
                ·
                  refine ⟨1693590649575834640364941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2258120866101112853819921 1693590649575834640364941)
                  ·
                    refine ⟨635096493590937990136853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1693590649575834640364941 635096493590937990136853)
                    ·
                      rfl

theorem cell22_1855269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 2, 3].length) (baseStart_1855269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1855269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1855269 prefixEnd_1855269 := by exact prefixLift 1855269
  have htrace : WordTrace (prefixWord ++ tailWord_1855269) baseStart_1855269 baseEnd_1855269 := by
    simpa [prefixWord, tailWord_1855269, baseEnd_1855269] using wordTrace_append hprefix tailTrace_1855269
  have hstable : (prefixWord ++ tailWord_1855269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855269).length < 2 ^ (prefixWord ++ tailWord_1855269).sum := by decide
  have hdescent : baseEnd_1855269 < baseStart_1855269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855314 : List Nat := [3, 2, 2, 1, 1, 4, 1, 4, 1, 3]
def baseStart_1855314 : Nat := 118140960795 + 1855314 * 2 ^ 59
def prefixEnd_1855314 : Nat := 4983230072969 + 3 ^ 40 * 1855314 * 2
def baseEnd_1855314 : Nat := 635111898010572872761715

theorem tailTrace_1855314 : CollatzResearch.WordTrace tailWord_1855314 prefixEnd_1855314 635111898010572872761715 := by
  unfold tailWord_1855314
  simp only [CollatzResearch.WordTrace]
  refine ⟨16917215200130428812401249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45112573867014476833069997 16917215200130428812401249)
  ·
    refine ⟨12687911400097821609300937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16917215200130428812401249 12687911400097821609300937)
    ·
      refine ⟨9515933550073366206975703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12687911400097821609300937 9515933550073366206975703)
      ·
        refine ⟨14273900325110049310463555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9515933550073366206975703 14273900325110049310463555)
        ·
          refine ⟨21410850487665073965695333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14273900325110049310463555 21410850487665073965695333)
          ·
            refine ⟨4014534466437201368567875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21410850487665073965695333 4014534466437201368567875)
            ·
              refine ⟨6021801699655802052851813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4014534466437201368567875 6021801699655802052851813)
              ·
                refine ⟨1129087818685462884909715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6021801699655802052851813 1129087818685462884909715)
                ·
                  refine ⟨1693631728028194327364573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1129087818685462884909715 1693631728028194327364573)
                  ·
                    refine ⟨635111898010572872761715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1693631728028194327364573 635111898010572872761715)
                    ·
                      rfl

theorem cell22_1855314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_1855314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1855314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1855314 prefixEnd_1855314 := by exact prefixLift 1855314
  have htrace : WordTrace (prefixWord ++ tailWord_1855314) baseStart_1855314 baseEnd_1855314 := by
    simpa [prefixWord, tailWord_1855314, baseEnd_1855314] using wordTrace_append hprefix tailTrace_1855314
  have hstable : (prefixWord ++ tailWord_1855314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855314).length < 2 ^ (prefixWord ++ tailWord_1855314).sum := by decide
  have hdescent : baseEnd_1855314 < baseStart_1855314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855340 : List Nat := [2, 2, 1, 1, 4, 2, 2, 1, 3, 4]
def baseStart_1855340 : Nat := 118140960795 + 1855340 * 2 ^ 59
def prefixEnd_1855340 : Nat := 4983230072969 + 3 ^ 40 * 1855340 * 2
def baseEnd_1855340 : Nat := 635120798341917471611635

theorem tailTrace_1855340 : CollatzResearch.WordTrace tailWord_1855340 prefixEnd_1855340 635120798341917471611635 := by
  unfold tailWord_1855340
  simp only [CollatzResearch.WordTrace]
  refine ⟨33834904549213760845025737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45113206065618347793367649 33834904549213760845025737)
  ·
    refine ⟨25376178411910320633769303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33834904549213760845025737 25376178411910320633769303)
    ·
      refine ⟨38064267617865480950653955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25376178411910320633769303 38064267617865480950653955)
      ·
        refine ⟨57096401426798221425980933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38064267617865480950653955 57096401426798221425980933)
        ·
          refine ⟨10705575267524666517371425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57096401426798221425980933 10705575267524666517371425)
          ·
            refine ⟨8029181450643499888028569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10705575267524666517371425 8029181450643499888028569)
            ·
              refine ⟨6021886087982624916021427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8029181450643499888028569 6021886087982624916021427)
              ·
                refine ⟨9032829131973937374032141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6021886087982624916021427 9032829131973937374032141)
                ·
                  refine ⟨3387310924490226515262053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9032829131973937374032141 3387310924490226515262053)
                  ·
                    refine ⟨635120798341917471611635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3387310924490226515262053 635120798341917471611635)
                    ·
                      rfl

theorem cell22_1855340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_1855340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1855340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1855340 prefixEnd_1855340 := by exact prefixLift 1855340
  have htrace : WordTrace (prefixWord ++ tailWord_1855340) baseStart_1855340 baseEnd_1855340 := by
    simpa [prefixWord, tailWord_1855340, baseEnd_1855340] using wordTrace_append hprefix tailTrace_1855340
  have hstable : (prefixWord ++ tailWord_1855340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855340).length < 2 ^ (prefixWord ++ tailWord_1855340).sum := by decide
  have hdescent : baseEnd_1855340 < baseStart_1855340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855361 : List Nat := [1, 2, 4, 4, 2, 1, 1, 2, 5]
def baseStart_1855361 : Nat := 118140960795 + 1855361 * 2 ^ 59
def prefixEnd_1855361 : Nat := 4983230072969 + 3 ^ 40 * 1855361 * 2
def baseEnd_1855361 : Nat := 211709329023693472278857

theorem tailTrace_1855361 : CollatzResearch.WordTrace tailWord_1855361 prefixEnd_1855361 211709329023693472278857 := by
  unfold tailWord_1855361
  simp only [CollatzResearch.WordTrace]
  refine ⟨67670575031351442276565937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45113716687567628184377291 67670575031351442276565937)
  ·
    refine ⟨50752931273513581707424453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67670575031351442276565937 50752931273513581707424453)
    ·
      refine ⟨9516174613783796570142085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50752931273513581707424453 9516174613783796570142085)
      ·
        refine ⟨1784282740084461856901641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9516174613783796570142085 1784282740084461856901641)
        ·
          refine ⟨1338212055063346392676231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1784282740084461856901641 1338212055063346392676231)
          ·
            refine ⟨2007318082595019589014347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1338212055063346392676231 2007318082595019589014347)
            ·
              refine ⟨3010977123892529383521521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2007318082595019589014347 3010977123892529383521521)
              ·
                refine ⟨2258232842919397037641141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3010977123892529383521521 2258232842919397037641141)
                ·
                  refine ⟨211709329023693472278857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2258232842919397037641141 211709329023693472278857)
                  ·
                    rfl

theorem cell22_1855361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 5].length) (baseStart_1855361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1855361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1855361 prefixEnd_1855361 := by exact prefixLift 1855361
  have htrace : WordTrace (prefixWord ++ tailWord_1855361) baseStart_1855361 baseEnd_1855361 := by
    simpa [prefixWord, tailWord_1855361, baseEnd_1855361] using wordTrace_append hprefix tailTrace_1855361
  have hstable : (prefixWord ++ tailWord_1855361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855361).length < 2 ^ (prefixWord ++ tailWord_1855361).sum := by decide
  have hdescent : baseEnd_1855361 < baseStart_1855361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855522 : List Nat := [3, 3, 1, 1, 1, 2, 1, 4, 1, 5]
def baseStart_1855522 : Nat := 118140960795 + 1855522 * 2 ^ 59
def prefixEnd_1855522 : Nat := 4983230072969 + 3 ^ 40 * 1855522 * 2
def baseEnd_1855522 : Nat := 635183100661329663561077

theorem tailTrace_1855522 : CollatzResearch.WordTrace tailWord_1855522 prefixEnd_1855522 635183100661329663561077 := by
  unfold tailWord_1855522
  simp only [CollatzResearch.WordTrace]
  refine ⟨16919111795942041693294205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45117631455845444515451213 16919111795942041693294205)
  ·
    refine ⟨6344666923478265634985327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16919111795942041693294205 6344666923478265634985327)
    ·
      refine ⟨9517000385217398452477991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6344666923478265634985327 9517000385217398452477991)
      ·
        refine ⟨14275500577826097678716987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9517000385217398452477991 14275500577826097678716987)
        ·
          refine ⟨21413250866739146518075481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14275500577826097678716987 21413250866739146518075481)
          ·
            refine ⟨16059938150054359888556611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21413250866739146518075481 16059938150054359888556611)
            ·
              refine ⟨24089907225081539832834917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16059938150054359888556611 24089907225081539832834917)
              ·
                refine ⟨4516857604702788718656547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24089907225081539832834917 4516857604702788718656547)
                ·
                  refine ⟨6775286407054183077984821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4516857604702788718656547 6775286407054183077984821)
                  ·
                    refine ⟨635183100661329663561077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6775286407054183077984821 635183100661329663561077)
                    ·
                      rfl

theorem cell22_1855522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_1855522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1855522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1855522 prefixEnd_1855522 := by exact prefixLift 1855522
  have htrace : WordTrace (prefixWord ++ tailWord_1855522) baseStart_1855522 baseEnd_1855522 := by
    simpa [prefixWord, tailWord_1855522, baseEnd_1855522] using wordTrace_append hprefix tailTrace_1855522
  have hstable : (prefixWord ++ tailWord_1855522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855522).length < 2 ^ (prefixWord ++ tailWord_1855522).sum := by decide
  have hdescent : baseEnd_1855522 < baseStart_1855522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855539 : List Nat := [1, 1, 1, 2, 4, 1, 5, 2, 2, 3]
def baseStart_1855539 : Nat := 118140960795 + 1855539 * 2 ^ 59
def prefixEnd_1855539 : Nat := 4983230072969 + 3 ^ 40 * 1855539 * 2
def baseEnd_1855539 : Nat := 635188920108747285886025

theorem tailTrace_1855539 : CollatzResearch.WordTrace tailWord_1855539 prefixEnd_1855539 635188920108747285886025 := by
  unfold tailWord_1855539
  simp only [CollatzResearch.WordTrace]
  refine ⟨67677067224706578676545671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45118044816471052451030447 67677067224706578676545671)
  ·
    refine ⟨101515600837059868014818507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67677067224706578676545671 101515600837059868014818507)
    ·
      refine ⟨152273401255589802022227761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101515600837059868014818507 152273401255589802022227761)
      ·
        refine ⟨114205050941692351516670821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152273401255589802022227761 114205050941692351516670821)
        ·
          refine ⟨21413447051567315909375779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114205050941692351516670821 21413447051567315909375779)
          ·
            refine ⟨32120170577350973864063669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21413447051567315909375779 32120170577350973864063669)
            ·
              refine ⟨3011265991626653799755969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32120170577350973864063669 3011265991626653799755969)
              ·
                refine ⟨2258449493719990349816977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3011265991626653799755969 2258449493719990349816977)
                ·
                  refine ⟨1693837120289992762362733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2258449493719990349816977 1693837120289992762362733)
                  ·
                    refine ⟨635188920108747285886025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1693837120289992762362733 635188920108747285886025)
                    ·
                      rfl

theorem cell22_1855539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 2, 3].length) (baseStart_1855539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1855539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1855539 prefixEnd_1855539 := by exact prefixLift 1855539
  have htrace : WordTrace (prefixWord ++ tailWord_1855539) baseStart_1855539 baseEnd_1855539 := by
    simpa [prefixWord, tailWord_1855539, baseEnd_1855539] using wordTrace_append hprefix tailTrace_1855539
  have hstable : (prefixWord ++ tailWord_1855539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855539).length < 2 ^ (prefixWord ++ tailWord_1855539).sum := by decide
  have hdescent : baseEnd_1855539 < baseStart_1855539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855586 : List Nat := [3, 3, 2, 2, 3, 1, 8]
def baseStart_1855586 : Nat := 118140960795 + 1855586 * 2 ^ 59
def prefixEnd_1855586 : Nat := 4983230072969 + 3 ^ 40 * 1855586 * 2
def baseEnd_1855586 : Nat := 23526111450713141850403

theorem tailTrace_1855586 : CollatzResearch.WordTrace tailWord_1855586 prefixEnd_1855586 23526111450713141850403 := by
  unfold tailWord_1855586
  simp only [CollatzResearch.WordTrace]
  refine ⟨16919695363884076425876653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45119187637024203802337741 16919695363884076425876653)
  ·
    refine ⟨6344885761456528659703745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16919695363884076425876653 6344885761456528659703745)
    ·
      refine ⟨4758664321092396494777809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6344885761456528659703745 4758664321092396494777809)
      ·
        refine ⟨3568998240819297371083357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4758664321092396494777809 3568998240819297371083357)
        ·
          refine ⟨1338374340307236514156259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3568998240819297371083357 1338374340307236514156259)
          ·
            refine ⟨2007561510460854771234389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1338374340307236514156259 2007561510460854771234389)
            ·
              refine ⟨23526111450713141850403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2007561510460854771234389 23526111450713141850403)
              ·
                rfl

theorem cell22_1855586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 8].length) (baseStart_1855586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1855586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1855586 prefixEnd_1855586 := by exact prefixLift 1855586
  have htrace : WordTrace (prefixWord ++ tailWord_1855586) baseStart_1855586 baseEnd_1855586 := by
    simpa [prefixWord, tailWord_1855586, baseEnd_1855586] using wordTrace_append hprefix tailTrace_1855586
  have hstable : (prefixWord ++ tailWord_1855586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855586).length < 2 ^ (prefixWord ++ tailWord_1855586).sum := by decide
  have hdescent : baseEnd_1855586 < baseStart_1855586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855597 : List Nat := [1, 5, 1, 1, 2, 1, 1, 3, 7]
def baseStart_1855597 : Nat := 118140960795 + 1855597 * 2 ^ 59
def prefixEnd_1855597 : Nat := 4983230072969 + 3 ^ 40 * 1855597 * 2
def baseEnd_1855597 : Nat := 211736258231351489311949

theorem tailTrace_1855597 : CollatzResearch.WordTrace tailWord_1855597 prefixEnd_1855597 211736258231351489311949 := by
  unfold tailWord_1855597
  simp only [CollatzResearch.WordTrace]
  refine ⟨67679182658496454582157045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45119455105664303054771363 67679182658496454582157045)
  ·
    refine ⟨6344923374234042617077223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67679182658496454582157045 6344923374234042617077223)
    ·
      refine ⟨9517385061351063925615835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6344923374234042617077223 9517385061351063925615835)
      ·
        refine ⟨14276077592026595888423753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9517385061351063925615835 14276077592026595888423753)
        ·
          refine ⟨10707058194019946916317815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14276077592026595888423753 10707058194019946916317815)
          ·
            refine ⟨16060587291029920374476723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10707058194019946916317815 16060587291029920374476723)
            ·
              refine ⟨24090880936544880561715085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16060587291029920374476723 24090880936544880561715085)
              ·
                refine ⟨9034080351204330210643157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24090880936544880561715085 9034080351204330210643157)
                ·
                  refine ⟨211736258231351489311949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9034080351204330210643157 211736258231351489311949)
                  ·
                    rfl

theorem cell22_1855597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_1855597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1855597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1855597 prefixEnd_1855597 := by exact prefixLift 1855597
  have htrace : WordTrace (prefixWord ++ tailWord_1855597) baseStart_1855597 baseEnd_1855597 := by
    simpa [prefixWord, tailWord_1855597, baseEnd_1855597] using wordTrace_append hprefix tailTrace_1855597
  have hstable : (prefixWord ++ tailWord_1855597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855597).length < 2 ^ (prefixWord ++ tailWord_1855597).sum := by decide
  have hdescent : baseEnd_1855597 < baseStart_1855597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855652 : List Nat := [2, 3, 1, 2, 5, 1, 2, 2, 1, 3]
def baseStart_1855652 : Nat := 118140960795 + 1855652 * 2 ^ 59
def prefixEnd_1855652 : Nat := 4983230072969 + 3 ^ 40 * 1855652 * 2
def baseEnd_1855652 : Nat := 635227602318052657810679

theorem tailTrace_1855652 : CollatzResearch.WordTrace tailWord_1855652 prefixEnd_1855652 635227602318052657810679 := by
  unfold tailWord_1855652
  simp only [CollatzResearch.WordTrace]
  refine ⟨33840594336648599487704605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45120792448864799316939473 33840594336648599487704605)
  ·
    refine ⟨12690222876243224807889227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33840594336648599487704605 12690222876243224807889227)
    ·
      refine ⟨19035334314364837211833841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12690222876243224807889227 19035334314364837211833841)
      ·
        refine ⟨14276500735773627908875381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19035334314364837211833841 14276500735773627908875381)
        ·
          refine ⟨1338421943978777616457067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14276500735773627908875381 1338421943978777616457067)
          ·
            refine ⟨2007632915968166424685601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1338421943978777616457067 2007632915968166424685601)
            ·
              refine ⟨1505724686976124818514201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2007632915968166424685601 1505724686976124818514201)
              ·
                refine ⟨1129293515232093613885651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1505724686976124818514201 1129293515232093613885651)
                ·
                  refine ⟨1693940272848140420828477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1129293515232093613885651 1693940272848140420828477)
                  ·
                    refine ⟨635227602318052657810679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1693940272848140420828477 635227602318052657810679)
                    ·
                      rfl

theorem cell22_1855652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 2, 1, 3].length) (baseStart_1855652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1855652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1855652 prefixEnd_1855652 := by exact prefixLift 1855652
  have htrace : WordTrace (prefixWord ++ tailWord_1855652) baseStart_1855652 baseEnd_1855652 := by
    simpa [prefixWord, tailWord_1855652, baseEnd_1855652] using wordTrace_append hprefix tailTrace_1855652
  have hstable : (prefixWord ++ tailWord_1855652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855652).length < 2 ^ (prefixWord ++ tailWord_1855652).sum := by decide
  have hdescent : baseEnd_1855652 < baseStart_1855652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855672 : List Nat := [2, 1, 2, 1, 2, 1, 4, 2, 1, 6]
def baseStart_1855672 : Nat := 118140960795 + 1855672 * 2 ^ 59
def prefixEnd_1855672 : Nat := 4983230072969 + 3 ^ 40 * 1855672 * 2
def baseEnd_1855672 : Nat := 635234448726779272310617

theorem tailTrace_1855672 : CollatzResearch.WordTrace tailWord_1855672 prefixEnd_1855672 635234448726779272310617 := by
  unfold tailWord_1855672
  simp only [CollatzResearch.WordTrace]
  refine ⟨33840959066612371195568635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45121278755483161594091513 33840959066612371195568635)
  ·
    refine ⟨50761438599918556793352953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33840959066612371195568635 50761438599918556793352953)
    ·
      refine ⟨38071078949938917595014715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50761438599918556793352953 38071078949938917595014715)
      ·
        refine ⟨57106618424908376392522073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38071078949938917595014715 57106618424908376392522073)
        ·
          refine ⟨42829963818681282294391555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57106618424908376392522073 42829963818681282294391555)
          ·
            refine ⟨64244945728021923441587333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42829963818681282294391555 64244945728021923441587333)
            ·
              refine ⟨12045927324004110645297625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64244945728021923441587333 12045927324004110645297625)
              ·
                refine ⟨9034445493003082983973219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12045927324004110645297625 9034445493003082983973219)
                ·
                  refine ⟨13551668239504624475959829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9034445493003082983973219 13551668239504624475959829)
                  ·
                    refine ⟨635234448726779272310617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13551668239504624475959829 635234448726779272310617)
                    ·
                      rfl

theorem cell22_1855672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_1855672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1855672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1855672 prefixEnd_1855672 := by exact prefixLift 1855672
  have htrace : WordTrace (prefixWord ++ tailWord_1855672) baseStart_1855672 baseEnd_1855672 := by
    simpa [prefixWord, tailWord_1855672, baseEnd_1855672] using wordTrace_append hprefix tailTrace_1855672
  have hstable : (prefixWord ++ tailWord_1855672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855672).length < 2 ^ (prefixWord ++ tailWord_1855672).sum := by decide
  have hdescent : baseEnd_1855672 < baseStart_1855672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855725 : List Nat := [1, 5, 1, 2, 3, 1, 3, 1, 2, 3]
def baseStart_1855725 : Nat := 118140960795 + 1855725 * 2 ^ 59
def prefixEnd_1855725 : Nat := 4983230072969 + 3 ^ 40 * 1855725 * 2
def baseEnd_1855725 : Nat := 635252591709904800735455

theorem tailTrace_1855725 : CollatzResearch.WordTrace tailWord_1855725 prefixEnd_1855725 635252591709904800735455 := by
  unfold tailWord_1855725
  simp only [CollatzResearch.WordTrace]
  refine ⟨67683851202032732442816629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45122567468021821628544419 67683851202032732442816629)
  ·
    refine ⟨6345361050190568666514059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67683851202032732442816629 6345361050190568666514059)
    ·
      refine ⟨9518041575285852999771089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6345361050190568666514059 9518041575285852999771089)
      ·
        refine ⟨7138531181464389749828317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9518041575285852999771089 7138531181464389749828317)
        ·
          refine ⟨2676949193049146156185619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7138531181464389749828317 2676949193049146156185619)
          ·
            refine ⟨4015423789573719234278429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2676949193049146156185619 4015423789573719234278429)
            ·
              refine ⟨1505783921090144712854411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4015423789573719234278429 1505783921090144712854411)
              ·
                refine ⟨2258675881635217069281617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1505783921090144712854411 2258675881635217069281617)
                ·
                  refine ⟨1694006911226412801961213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2258675881635217069281617 1694006911226412801961213)
                  ·
                    refine ⟨635252591709904800735455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1694006911226412801961213 635252591709904800735455)
                    ·
                      rfl

theorem cell22_1855725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_1855725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1855725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1855725 prefixEnd_1855725 := by exact prefixLift 1855725
  have htrace : WordTrace (prefixWord ++ tailWord_1855725) baseStart_1855725 baseEnd_1855725 := by
    simpa [prefixWord, tailWord_1855725, baseEnd_1855725] using wordTrace_append hprefix tailTrace_1855725
  have hstable : (prefixWord ++ tailWord_1855725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855725).length < 2 ^ (prefixWord ++ tailWord_1855725).sum := by decide
  have hdescent : baseEnd_1855725 < baseStart_1855725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855734 : List Nat := [5, 1, 1, 1, 1, 1, 2, 2, 2, 6]
def baseStart_1855734 : Nat := 118140960795 + 1855734 * 2 ^ 59
def prefixEnd_1855734 : Nat := 4983230072969 + 3 ^ 40 * 1855734 * 2
def baseEnd_1855734 : Nat := 635255672593831777260427

theorem tailTrace_1855734 : CollatzResearch.WordTrace tailWord_1855734 prefixEnd_1855734 635255672593831777260427 := by
  unfold tailWord_1855734
  simp only [CollatzResearch.WordTrace]
  refine ⟨4230261216187507936243391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45122786306000084653262837 4230261216187507936243391)
  ·
    refine ⟨6345391824281261904365087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4230261216187507936243391 6345391824281261904365087)
    ·
      refine ⟨9518087736421892856547631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6345391824281261904365087 9518087736421892856547631)
      ·
        refine ⟨14277131604632839284821447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9518087736421892856547631 14277131604632839284821447)
        ·
          refine ⟨21415697406949258927232171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14277131604632839284821447 21415697406949258927232171)
          ·
            refine ⟨32123546110423888390848257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21415697406949258927232171 32123546110423888390848257)
            ·
              refine ⟨24092659582817916293136193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32123546110423888390848257 24092659582817916293136193)
              ·
                refine ⟨18069494687113437219852145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24092659582817916293136193 18069494687113437219852145)
                ·
                  refine ⟨13552121015335077914889109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18069494687113437219852145 13552121015335077914889109)
                  ·
                    refine ⟨635255672593831777260427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13552121015335077914889109 635255672593831777260427)
                    ·
                      rfl

theorem cell22_1855734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_1855734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1855734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1855734 prefixEnd_1855734 := by exact prefixLift 1855734
  have htrace : WordTrace (prefixWord ++ tailWord_1855734) baseStart_1855734 baseEnd_1855734 := by
    simpa [prefixWord, tailWord_1855734, baseEnd_1855734] using wordTrace_append hprefix tailTrace_1855734
  have hstable : (prefixWord ++ tailWord_1855734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855734).length < 2 ^ (prefixWord ++ tailWord_1855734).sum := by decide
  have hdescent : baseEnd_1855734 < baseStart_1855734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855753 : List Nat := [1, 2, 1, 1, 3, 4, 3, 3, 1, 3]
def baseStart_1855753 : Nat := 118140960795 + 1855753 * 2 ^ 59
def prefixEnd_1855753 : Nat := 4983230072969 + 3 ^ 40 * 1855753 * 2
def baseEnd_1855753 : Nat := 635262176682122061035369

theorem tailTrace_1855753 : CollatzResearch.WordTrace tailWord_1855753 prefixEnd_1855753 635262176682122061035369 := by
  unfold tailWord_1855753
  simp only [CollatzResearch.WordTrace]
  refine ⟨67684872445931293224835913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45123248297287528816557275 67684872445931293224835913)
  ·
    refine ⟨50763654334448469918626935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67684872445931293224835913 50763654334448469918626935)
    ·
      refine ⟨76145481501672704877940403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50763654334448469918626935 76145481501672704877940403)
      ·
        refine ⟨114218222252509057316910605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76145481501672704877940403 114218222252509057316910605)
        ·
          refine ⟨42831833344690896493841477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114218222252509057316910605 42831833344690896493841477)
          ·
            refine ⟨8030968752129543092595277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42831833344690896493841477 8030968752129543092595277)
            ·
              refine ⟨3011613282048578659723229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8030968752129543092595277 3011613282048578659723229)
              ·
                refine ⟨1129354980768216997396211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3011613282048578659723229 1129354980768216997396211)
                ·
                  refine ⟨1694032471152325496094317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1129354980768216997396211 1694032471152325496094317)
                  ·
                    refine ⟨635262176682122061035369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1694032471152325496094317 635262176682122061035369)
                    ·
                      rfl

theorem cell22_1855753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 3, 1, 3].length) (baseStart_1855753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1855753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1855753 prefixEnd_1855753 := by exact prefixLift 1855753
  have htrace : WordTrace (prefixWord ++ tailWord_1855753) baseStart_1855753 baseEnd_1855753 := by
    simpa [prefixWord, tailWord_1855753, baseEnd_1855753] using wordTrace_append hprefix tailTrace_1855753
  have hstable : (prefixWord ++ tailWord_1855753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855753).length < 2 ^ (prefixWord ++ tailWord_1855753).sum := by decide
  have hdescent : baseEnd_1855753 < baseStart_1855753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855770 : List Nat := [3, 1, 1, 3, 5, 1, 1, 1, 3, 3]
def baseStart_1855770 : Nat := 118140960795 + 1855770 * 2 ^ 59
def prefixEnd_1855770 : Nat := 4983230072969 + 3 ^ 40 * 1855770 * 2
def baseEnd_1855770 : Nat := 635267996129539683360317

theorem tailTrace_1855770 : CollatzResearch.WordTrace tailWord_1855770 prefixEnd_1855770 635267996129539683360317 := by
  unfold tailWord_1855770
  simp only [CollatzResearch.WordTrace]
  refine ⟨16921373121717426282051191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45123661657913136752136509 16921373121717426282051191)
  ·
    refine ⟨25382059682576139423076787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16921373121717426282051191 25382059682576139423076787)
    ·
      refine ⟨38073089523864209134615181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25382059682576139423076787 38073089523864209134615181)
      ·
        refine ⟨14277408571449078425480693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38073089523864209134615181 14277408571449078425480693)
        ·
          refine ⟨1338507053573351102388815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14277408571449078425480693 1338507053573351102388815)
          ·
            refine ⟨2007760580360026653583223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1338507053573351102388815 2007760580360026653583223)
            ·
              refine ⟨3011640870540039980374835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2007760580360026653583223 3011640870540039980374835)
              ·
                refine ⟨4517461305810059970562253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3011640870540039980374835 4517461305810059970562253)
                ·
                  refine ⟨1694047989678772488960845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4517461305810059970562253 1694047989678772488960845)
                  ·
                    refine ⟨635267996129539683360317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1694047989678772488960845 635267996129539683360317)
                    ·
                      rfl

theorem cell22_1855770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 3, 3].length) (baseStart_1855770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1855770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1855770 prefixEnd_1855770 := by exact prefixLift 1855770
  have htrace : WordTrace (prefixWord ++ tailWord_1855770) baseStart_1855770 baseEnd_1855770 := by
    simpa [prefixWord, tailWord_1855770, baseEnd_1855770] using wordTrace_append hprefix tailTrace_1855770
  have hstable : (prefixWord ++ tailWord_1855770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855770).length < 2 ^ (prefixWord ++ tailWord_1855770).sum := by decide
  have hdescent : baseEnd_1855770 < baseStart_1855770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855779 : List Nat := [1, 1, 1, 4, 2, 2, 2, 2, 3, 4]
def baseStart_1855779 : Nat := 118140960795 + 1855779 * 2 ^ 59
def prefixEnd_1855779 : Nat := 4983230072969 + 3 ^ 40 * 1855779 * 2
def baseEnd_1855779 : Nat := 635271077013466659885289

theorem tailTrace_1855779 : CollatzResearch.WordTrace tailWord_1855779 prefixEnd_1855779 635271077013466659885289 := by
  unfold tailWord_1855779
  simp only [CollatzResearch.WordTrace]
  refine ⟨67685820743837099665282391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45123880495891399776854927 67685820743837099665282391)
  ·
    refine ⟨101528731115755649497923587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67685820743837099665282391 101528731115755649497923587)
    ·
      refine ⟨152293096673633474246885381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101528731115755649497923587 152293096673633474246885381)
      ·
        refine ⟨28554955626306276421291009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152293096673633474246885381 28554955626306276421291009)
        ·
          refine ⟨21416216719729707315968257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28554955626306276421291009 21416216719729707315968257)
          ·
            refine ⟨16062162539797280486976193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21416216719729707315968257 16062162539797280486976193)
            ·
              refine ⟨12046621904847960365232145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16062162539797280486976193 12046621904847960365232145)
              ·
                refine ⟨9034966428635970273924109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12046621904847960365232145 9034966428635970273924109)
                ·
                  refine ⟨3388112410738488852721541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9034966428635970273924109 3388112410738488852721541)
                  ·
                    refine ⟨635271077013466659885289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3388112410738488852721541 635271077013466659885289)
                    ·
                      rfl

theorem cell22_1855779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 4].length) (baseStart_1855779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1855779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1855779 prefixEnd_1855779 := by exact prefixLift 1855779
  have htrace : WordTrace (prefixWord ++ tailWord_1855779) baseStart_1855779 baseEnd_1855779 := by
    simpa [prefixWord, tailWord_1855779, baseEnd_1855779] using wordTrace_append hprefix tailTrace_1855779
  have hstable : (prefixWord ++ tailWord_1855779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855779).length < 2 ^ (prefixWord ++ tailWord_1855779).sum := by decide
  have hdescent : baseEnd_1855779 < baseStart_1855779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855826 : List Nat := [3, 2, 2, 1, 1, 1, 2, 3, 4, 3]
def baseStart_1855826 : Nat := 118140960795 + 1855826 * 2 ^ 59
def prefixEnd_1855826 : Nat := 4983230072969 + 3 ^ 40 * 1855826 * 2
def baseEnd_1855826 : Nat := 635287166073974203960145

theorem tailTrace_1855826 : CollatzResearch.WordTrace tailWord_1855826 prefixEnd_1855826 635287166073974203960145 := by
  unfold tailWord_1855826
  simp only [CollatzResearch.WordTrace]
  refine ⟨16921883743666706673060833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45125023316444551128162221 16921883743666706673060833)
  ·
    refine ⟨12691412807750030004795625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16921883743666706673060833 12691412807750030004795625)
    ·
      refine ⟨9518559605812522503596719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12691412807750030004795625 9518559605812522503596719)
      ·
        refine ⟨14277839408718783755395079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9518559605812522503596719 14277839408718783755395079)
        ·
          refine ⟨21416759113078175633092619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14277839408718783755395079 21416759113078175633092619)
          ·
            refine ⟨32125138669617263449638929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21416759113078175633092619 32125138669617263449638929)
            ·
              refine ⟨24093854002212947587229197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32125138669617263449638929 24093854002212947587229197)
              ·
                refine ⟨9035195250829855345210949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24093854002212947587229197 9035195250829855345210949)
                ·
                  refine ⟨1694099109530597877227053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9035195250829855345210949 1694099109530597877227053)
                  ·
                    refine ⟨635287166073974203960145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1694099109530597877227053 635287166073974203960145)
                    ·
                      rfl

theorem cell22_1855826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_1855826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1855826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1855826 prefixEnd_1855826 := by exact prefixLift 1855826
  have htrace : WordTrace (prefixWord ++ tailWord_1855826) baseStart_1855826 baseEnd_1855826 := by
    simpa [prefixWord, tailWord_1855826, baseEnd_1855826] using wordTrace_append hprefix tailTrace_1855826
  have hstable : (prefixWord ++ tailWord_1855826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855826).length < 2 ^ (prefixWord ++ tailWord_1855826).sum := by decide
  have hdescent : baseEnd_1855826 < baseStart_1855826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855828 : List Nat := [2, 4, 1, 1, 2, 3, 1, 4, 4]
def baseStart_1855828 : Nat := 118140960795 + 1855828 * 2 ^ 59
def prefixEnd_1855828 : Nat := 4983230072969 + 3 ^ 40 * 1855828 * 2
def baseEnd_1855828 : Nat := 211762616904948955136713

theorem tailTrace_1855828 : CollatzResearch.WordTrace tailWord_1855828 prefixEnd_1855828 211762616904948955136713 := by
  unfold tailWord_1855828
  simp only [CollatzResearch.WordTrace]
  refine ⟨33843803960329790516908069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45125071947106387355877425 33843803960329790516908069)
  ·
    refine ⟨6345713242561835721920263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33843803960329790516908069 6345713242561835721920263)
    ·
      refine ⟨9518569863842753582880395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6345713242561835721920263 9518569863842753582880395)
      ·
        refine ⟨14277854795764130374320593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9518569863842753582880395 14277854795764130374320593)
        ·
          refine ⟨10708391096823097780740445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14277854795764130374320593 10708391096823097780740445)
          ·
            refine ⟨4015646661308661667777667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10708391096823097780740445 4015646661308661667777667)
            ·
              refine ⟨6023469991962992501666501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4015646661308661667777667 6023469991962992501666501)
              ·
                refine ⟨1129400623493061094062469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6023469991962992501666501 1129400623493061094062469)
                ·
                  refine ⟨211762616904948955136713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1129400623493061094062469 211762616904948955136713)
                  ·
                    rfl

theorem cell22_1855828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_1855828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1855828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1855828 prefixEnd_1855828 := by exact prefixLift 1855828
  have htrace : WordTrace (prefixWord ++ tailWord_1855828) baseStart_1855828 baseEnd_1855828 := by
    simpa [prefixWord, tailWord_1855828, baseEnd_1855828] using wordTrace_append hprefix tailTrace_1855828
  have hstable : (prefixWord ++ tailWord_1855828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855828).length < 2 ^ (prefixWord ++ tailWord_1855828).sum := by decide
  have hdescent : baseEnd_1855828 < baseStart_1855828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855839 : List Nat := [1, 1, 2, 3, 1, 2, 5, 7]
def baseStart_1855839 : Nat := 118140960795 + 1855839 * 2 ^ 59
def prefixEnd_1855839 : Nat := 4983230072969 + 3 ^ 40 * 1855839 * 2
def baseEnd_1855839 : Nat := 70587957359960722598345

theorem tailTrace_1855839 : CollatzResearch.WordTrace tailWord_1855839 prefixEnd_1855839 70587957359960722598345 := by
  unfold tailWord_1855839
  simp only [CollatzResearch.WordTrace]
  refine ⟨67688009123619729912466571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45125339415746486608311047 67688009123619729912466571)
  ·
    refine ⟨101532013685429594868699857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67688009123619729912466571 101532013685429594868699857)
    ·
      refine ⟨76149010264072196151524893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101532013685429594868699857 76149010264072196151524893)
      ·
        refine ⟨28555878849027073556821835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76149010264072196151524893 28555878849027073556821835)
        ·
          refine ⟨42833818273540610335232753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28555878849027073556821835 42833818273540610335232753)
          ·
            refine ⟨32125363705155457751424565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42833818273540610335232753 32125363705155457751424565)
            ·
              refine ⟨3011752847358324164196053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32125363705155457751424565 3011752847358324164196053)
              ·
                refine ⟨70587957359960722598345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3011752847358324164196053 70587957359960722598345)
                ·
                  rfl

theorem cell22_1855839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 7].length) (baseStart_1855839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1855839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1855839 prefixEnd_1855839 := by exact prefixLift 1855839
  have htrace : WordTrace (prefixWord ++ tailWord_1855839) baseStart_1855839 baseEnd_1855839 := by
    simpa [prefixWord, tailWord_1855839, baseEnd_1855839] using wordTrace_append hprefix tailTrace_1855839
  have hstable : (prefixWord ++ tailWord_1855839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855839).length < 2 ^ (prefixWord ++ tailWord_1855839).sum := by decide
  have hdescent : baseEnd_1855839 < baseStart_1855839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855856 : List Nat := [2, 1, 1, 1, 4, 4, 3, 6]
def baseStart_1855856 : Nat := 118140960795 + 1855856 * 2 ^ 59
def prefixEnd_1855856 : Nat := 4983230072969 + 3 ^ 40 * 1855856 * 2
def baseEnd_1855856 : Nat := 70588603965229347301117

theorem tailTrace_1855856 : CollatzResearch.WordTrace tailWord_1855856 prefixEnd_1855856 70588603965229347301117 := by
  unfold tailWord_1855856
  simp only [CollatzResearch.WordTrace]
  refine ⟨33844314582279070907917711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45125752776372094543890281 33844314582279070907917711)
  ·
    refine ⟨50766471873418606361876567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33844314582279070907917711 50766471873418606361876567)
    ·
      refine ⟨76149707810127909542814851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50766471873418606361876567 76149707810127909542814851)
      ·
        refine ⟨114224561715191864314222277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76149707810127909542814851 114224561715191864314222277)
        ·
          refine ⟨21417105321598474558916677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114224561715191864314222277 21417105321598474558916677)
          ·
            refine ⟨4015707247799713979796877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21417105321598474558916677 4015707247799713979796877)
            ·
              refine ⟨1505890217924892742423829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4015707247799713979796877 1505890217924892742423829)
              ·
                refine ⟨70588603965229347301117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1505890217924892742423829 70588603965229347301117)
                ·
                  rfl

theorem cell22_1855856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 6].length) (baseStart_1855856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1855856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1855856 prefixEnd_1855856 := by exact prefixLift 1855856
  have htrace : WordTrace (prefixWord ++ tailWord_1855856) baseStart_1855856 baseEnd_1855856 := by
    simpa [prefixWord, tailWord_1855856, baseEnd_1855856] using wordTrace_append hprefix tailTrace_1855856
  have hstable : (prefixWord ++ tailWord_1855856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855856).length < 2 ^ (prefixWord ++ tailWord_1855856).sum := by decide
  have hdescent : baseEnd_1855856 < baseStart_1855856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855858 : List Nat := [3, 2, 1, 2, 1, 5, 1, 1, 2, 4]
def baseStart_1855858 : Nat := 118140960795 + 1855858 * 2 ^ 59
def prefixEnd_1855858 : Nat := 4983230072969 + 3 ^ 40 * 1855858 * 2
def baseEnd_1855858 : Nat := 635298120327936787160047

theorem tailTrace_1855858 : CollatzResearch.WordTrace tailWord_1855858 prefixEnd_1855858 635298120327936787160047 := by
  unfold tailWord_1855858
  simp only [CollatzResearch.WordTrace]
  refine ⟨16922175527637724039352057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45125801407033930771605485 16922175527637724039352057)
  ·
    refine ⟨12691631645728293029514043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16922175527637724039352057 12691631645728293029514043)
    ·
      refine ⟨19037447468592439544271065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12691631645728293029514043 19037447468592439544271065)
      ·
        refine ⟨14278085601444329658203299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19037447468592439544271065 14278085601444329658203299)
        ·
          refine ⟨21417128402166494487304949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14278085601444329658203299 21417128402166494487304949)
          ·
            refine ⟨2007855787703108858184839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21417128402166494487304949 2007855787703108858184839)
            ·
              refine ⟨3011783681554663287277259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2007855787703108858184839 3011783681554663287277259)
              ·
                refine ⟨4517675522331994930915889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3011783681554663287277259 4517675522331994930915889)
                ·
                  refine ⟨3388256641748996198186917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4517675522331994930915889 3388256641748996198186917)
                  ·
                    refine ⟨635298120327936787160047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3388256641748996198186917 635298120327936787160047)
                    ·
                      rfl

theorem cell22_1855858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_1855858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1855858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1855858 prefixEnd_1855858 := by exact prefixLift 1855858
  have htrace : WordTrace (prefixWord ++ tailWord_1855858) baseStart_1855858 baseEnd_1855858 := by
    simpa [prefixWord, tailWord_1855858, baseEnd_1855858] using wordTrace_append hprefix tailTrace_1855858
  have hstable : (prefixWord ++ tailWord_1855858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855858).length < 2 ^ (prefixWord ++ tailWord_1855858).sum := by decide
  have hdescent : baseEnd_1855858 < baseStart_1855858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855862 : List Nat := [5, 1, 1, 4, 1, 1, 2, 3, 4]
def baseStart_1855862 : Nat := 118140960795 + 1855862 * 2 ^ 59
def prefixEnd_1855862 : Nat := 4983230072969 + 3 ^ 40 * 1855862 * 2
def baseEnd_1855862 : Nat := 211766496536560703353345

theorem tailTrace_1855862 : CollatzResearch.WordTrace tailWord_1855862 prefixEnd_1855862 211766496536560703353345 := by
  unfold tailWord_1855862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4230553000158525302534615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45125898668357603227035893 4230553000158525302534615)
  ·
    refine ⟨6345829500237787953801923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4230553000158525302534615 6345829500237787953801923)
    ·
      refine ⟨9518744250356681930702885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6345829500237787953801923 9518744250356681930702885)
      ·
        refine ⟨1784764546941877862006791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9518744250356681930702885 1784764546941877862006791)
        ·
          refine ⟨2677146820412816793010187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1784764546941877862006791 2677146820412816793010187)
          ·
            refine ⟨4015720230619225189515281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2677146820412816793010187 4015720230619225189515281)
            ·
              refine ⟨3011790172964418892136461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4015720230619225189515281 3011790172964418892136461)
              ·
                refine ⟨1129421314861657084551173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3011790172964418892136461 1129421314861657084551173)
                ·
                  refine ⟨211766496536560703353345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1129421314861657084551173 211766496536560703353345)
                  ·
                    rfl

theorem cell22_1855862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_1855862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1855862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1855862 prefixEnd_1855862 := by exact prefixLift 1855862
  have htrace : WordTrace (prefixWord ++ tailWord_1855862) baseStart_1855862 baseEnd_1855862 := by
    simpa [prefixWord, tailWord_1855862, baseEnd_1855862] using wordTrace_append hprefix tailTrace_1855862
  have hstable : (prefixWord ++ tailWord_1855862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855862).length < 2 ^ (prefixWord ++ tailWord_1855862).sum := by decide
  have hdescent : baseEnd_1855862 < baseStart_1855862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855894 : List Nat := [5, 3, 1, 2, 1, 2, 1, 1, 1, 5]
def baseStart_1855894 : Nat := 118140960795 + 1855894 * 2 ^ 59
def prefixEnd_1855894 : Nat := 4983230072969 + 3 ^ 40 * 1855894 * 2
def baseEnd_1855894 : Nat := 635310443863644693259937

theorem tailTrace_1855894 : CollatzResearch.WordTrace tailWord_1855894 prefixEnd_1855894 635310443863644693259937 := by
  unfold tailWord_1855894
  simp only [CollatzResearch.WordTrace]
  refine ⟨4230625946151279644107421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45126676758946982870479157 4230625946151279644107421)
  ·
    refine ⟨1586484729806729866540283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4230625946151279644107421 1586484729806729866540283)
    ·
      refine ⟨2379727094710094799810425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1586484729806729866540283 2379727094710094799810425)
      ·
        refine ⟨1784795321032571099857819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2379727094710094799810425 1784795321032571099857819)
        ·
          refine ⟨2677192981548856649786729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1784795321032571099857819 2677192981548856649786729)
          ·
            refine ⟨2007894736161642487340047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2677192981548856649786729 2007894736161642487340047)
            ·
              refine ⟨3011842104242463731010071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2007894736161642487340047 3011842104242463731010071)
              ·
                refine ⟨4517763156363695596515107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3011842104242463731010071 4517763156363695596515107)
                ·
                  refine ⟨6776644734545543394772661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4517763156363695596515107 6776644734545543394772661)
                  ·
                    refine ⟨635310443863644693259937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6776644734545543394772661 635310443863644693259937)
                    ·
                      rfl

theorem cell22_1855894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_1855894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1855894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1855894 prefixEnd_1855894 := by exact prefixLift 1855894
  have htrace : WordTrace (prefixWord ++ tailWord_1855894) baseStart_1855894 baseEnd_1855894 := by
    simpa [prefixWord, tailWord_1855894, baseEnd_1855894] using wordTrace_append hprefix tailTrace_1855894
  have hstable : (prefixWord ++ tailWord_1855894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855894).length < 2 ^ (prefixWord ++ tailWord_1855894).sum := by decide
  have hdescent : baseEnd_1855894 < baseStart_1855894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855961 : List Nat := [1, 2, 1, 2, 4, 1, 2, 3, 1, 5]
def baseStart_1855961 : Nat := 118140960795 + 1855961 * 2 ^ 59
def prefixEnd_1855961 : Nat := 4983230072969 + 3 ^ 40 * 1855961 * 2
def baseEnd_1855961 : Nat := 635333379332878851834731

theorem tailTrace_1855961 : CollatzResearch.WordTrace tailWord_1855961 prefixEnd_1855961 635333379332878851834731 := by
  unfold tailWord_1855961
  simp only [CollatzResearch.WordTrace]
  refine ⟨67692458829177744748407737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45128305886118496498938491 67692458829177744748407737)
  ·
    refine ⟨50769344121883308561305803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67692458829177744748407737 50769344121883308561305803)
    ·
      refine ⟨76154016182824962841958705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50769344121883308561305803 76154016182824962841958705)
      ·
        refine ⟨57115512137118722131469029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76154016182824962841958705 57115512137118722131469029)
        ·
          refine ⟨10709158525709760399650443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57115512137118722131469029 10709158525709760399650443)
          ·
            refine ⟨16063737788564640599475665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10709158525709760399650443 16063737788564640599475665)
            ·
              refine ⟨12047803341423480449606749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16063737788564640599475665 12047803341423480449606749)
              ·
                refine ⟨4517926253033805168602531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12047803341423480449606749 4517926253033805168602531)
                ·
                  refine ⟨6776889379550707752903797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4517926253033805168602531 6776889379550707752903797)
                  ·
                    refine ⟨635333379332878851834731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6776889379550707752903797 635333379332878851834731)
                    ·
                      rfl

theorem cell22_1855961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 5].length) (baseStart_1855961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1855961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1855961 prefixEnd_1855961 := by exact prefixLift 1855961
  have htrace : WordTrace (prefixWord ++ tailWord_1855961) baseStart_1855961 baseEnd_1855961 := by
    simpa [prefixWord, tailWord_1855961, baseEnd_1855961] using wordTrace_append hprefix tailTrace_1855961
  have hstable : (prefixWord ++ tailWord_1855961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855961).length < 2 ^ (prefixWord ++ tailWord_1855961).sum := by decide
  have hdescent : baseEnd_1855961 < baseStart_1855961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855978 : List Nat := [3, 1, 3, 1, 3, 2, 1, 2, 1, 5]
def baseStart_1855978 : Nat := 118140960795 + 1855978 * 2 ^ 59
def prefixEnd_1855978 : Nat := 4983230072969 + 3 ^ 40 * 1855978 * 2
def baseEnd_1855978 : Nat := 635339198780296474159679

theorem tailTrace_1855978 : CollatzResearch.WordTrace tailWord_1855978 prefixEnd_1855978 635339198780296474159679 := by
  unfold tailWord_1855978
  simp only [CollatzResearch.WordTrace]
  refine ⟨16923269717529039162944147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45128719246744104434517725 16923269717529039162944147)
  ·
    refine ⟨25384904576293558744416221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16923269717529039162944147 25384904576293558744416221)
    ·
      refine ⟨9519339216110084529156083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25384904576293558744416221 9519339216110084529156083)
      ·
        refine ⟨14279008824165126793734125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9519339216110084529156083 14279008824165126793734125)
        ·
          refine ⟨5354628309061922547650297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14279008824165126793734125 5354628309061922547650297)
          ·
            refine ⟨4015971231796441910737723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5354628309061922547650297 4015971231796441910737723)
            ·
              refine ⟨6023956847694662866106585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4015971231796441910737723 6023956847694662866106585)
              ·
                refine ⟨4517967635770997149579939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6023956847694662866106585 4517967635770997149579939)
                ·
                  refine ⟨6776951453656495724369909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4517967635770997149579939 6776951453656495724369909)
                  ·
                    refine ⟨635339198780296474159679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6776951453656495724369909 635339198780296474159679)
                    ·
                      rfl

theorem cell22_1855978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_1855978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1855978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1855978 prefixEnd_1855978 := by exact prefixLift 1855978
  have htrace : WordTrace (prefixWord ++ tailWord_1855978) baseStart_1855978 baseEnd_1855978 := by
    simpa [prefixWord, tailWord_1855978, baseEnd_1855978] using wordTrace_append hprefix tailTrace_1855978
  have hstable : (prefixWord ++ tailWord_1855978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855978).length < 2 ^ (prefixWord ++ tailWord_1855978).sum := by decide
  have hdescent : baseEnd_1855978 < baseStart_1855978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856021 : List Nat := [1, 3, 2, 1, 3, 1, 1, 2, 2, 6]
def baseStart_1856021 : Nat := 118140960795 + 1856021 * 2 ^ 59
def prefixEnd_1856021 : Nat := 4983230072969 + 3 ^ 40 * 1856021 * 2
def baseEnd_1856021 : Nat := 635353918559058695334547

theorem tailTrace_1856021 : CollatzResearch.WordTrace tailWord_1856021 prefixEnd_1856021 635353918559058695334547 := by
  unfold tailWord_1856021
  simp only [CollatzResearch.WordTrace]
  refine ⟨67694647208960374995591917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45129764805973583330394611 67694647208960374995591917)
  ·
    refine ⟨25385492703360140623346969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67694647208960374995591917 25385492703360140623346969)
    ·
      refine ⟨19039119527520105467510227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25385492703360140623346969 19039119527520105467510227)
      ·
        refine ⟨28558679291280158201265341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19039119527520105467510227 28558679291280158201265341)
        ·
          refine ⟨10709504734230059325474503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28558679291280158201265341 10709504734230059325474503)
          ·
            refine ⟨16064257101345088988211755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10709504734230059325474503 16064257101345088988211755)
            ·
              refine ⟨24096385652017633482317633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16064257101345088988211755 24096385652017633482317633)
              ·
                refine ⟨18072289239013225111738225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24096385652017633482317633 18072289239013225111738225)
                ·
                  refine ⟨13554216929259918833803669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18072289239013225111738225 13554216929259918833803669)
                  ·
                    refine ⟨635353918559058695334547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13554216929259918833803669 635353918559058695334547)
                    ·
                      rfl

theorem cell22_1856021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_1856021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1856021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1856021 prefixEnd_1856021 := by exact prefixLift 1856021
  have htrace : WordTrace (prefixWord ++ tailWord_1856021) baseStart_1856021 baseEnd_1856021 := by
    simpa [prefixWord, tailWord_1856021, baseEnd_1856021] using wordTrace_append hprefix tailTrace_1856021
  have hstable : (prefixWord ++ tailWord_1856021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856021).length < 2 ^ (prefixWord ++ tailWord_1856021).sum := by decide
  have hdescent : baseEnd_1856021 < baseStart_1856021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856051 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 4, 5]
def baseStart_1856051 : Nat := 118140960795 + 1856051 * 2 ^ 59
def prefixEnd_1856051 : Nat := 4983230072969 + 3 ^ 40 * 1856051 * 2
def baseEnd_1856051 : Nat := 635364188172148617084455

theorem tailTrace_1856051 : CollatzResearch.WordTrace tailWord_1856051 prefixEnd_1856051 635364188172148617084455 := by
  unfold tailWord_1856051
  simp only [CollatzResearch.WordTrace]
  refine ⟨67695741398851690119184007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45130494265901126746122671 67695741398851690119184007)
  ·
    refine ⟨101543612098277535178776011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67695741398851690119184007 101543612098277535178776011)
    ·
      refine ⟨152315418147416302768164017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101543612098277535178776011 152315418147416302768164017)
      ·
        refine ⟨114236563610562227076123013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152315418147416302768164017 114236563610562227076123013)
        ·
          refine ⟨21419355676980417576773065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114236563610562227076123013 21419355676980417576773065)
          ·
            refine ⟨16064516757735313182579799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21419355676980417576773065 16064516757735313182579799)
            ·
              refine ⟨24096775136602969773869699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16064516757735313182579799 24096775136602969773869699)
              ·
                refine ⟨36145162704904454660804549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24096775136602969773869699 36145162704904454660804549)
                ·
                  refine ⟨6777218007169585248900853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36145162704904454660804549 6777218007169585248900853)
                  ·
                    refine ⟨635364188172148617084455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6777218007169585248900853 635364188172148617084455)
                    ·
                      rfl

theorem cell22_1856051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 5].length) (baseStart_1856051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1856051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1856051 prefixEnd_1856051 := by exact prefixLift 1856051
  have htrace : WordTrace (prefixWord ++ tailWord_1856051) baseStart_1856051 baseEnd_1856051 := by
    simpa [prefixWord, tailWord_1856051, baseEnd_1856051] using wordTrace_append hprefix tailTrace_1856051
  have hstable : (prefixWord ++ tailWord_1856051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856051).length < 2 ^ (prefixWord ++ tailWord_1856051).sum := by decide
  have hdescent : baseEnd_1856051 < baseStart_1856051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856177 : List Nat := [1, 2, 2, 6, 1, 2, 1, 7]
def baseStart_1856177 : Nat := 118140960795 + 1856177 * 2 ^ 59
def prefixEnd_1856177 : Nat := 4983230072969 + 3 ^ 40 * 1856177 * 2
def baseEnd_1856177 : Nat := 70600813394125143159341

theorem tailTrace_1856177 : CollatzResearch.WordTrace tailWord_1856177 prefixEnd_1856177 70600813394125143159341 := by
  unfold tailWord_1856177
  simp only [CollatzResearch.WordTrace]
  refine ⟨67700336996395213638270785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45133557997596809092180523 67700336996395213638270785)
  ·
    refine ⟨50775252747296410228703089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67700336996395213638270785 50775252747296410228703089)
    ·
      refine ⟨38081439560472307671527317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50775252747296410228703089 38081439560472307671527317)
      ·
        refine ⟨1785067479397139422102843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38081439560472307671527317 1785067479397139422102843)
        ·
          refine ⟨2677601219095709133154265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1785067479397139422102843 2677601219095709133154265)
          ·
            refine ⟨2008200914321781849865699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2677601219095709133154265 2008200914321781849865699)
            ·
              refine ⟨3012301371482672774798549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2008200914321781849865699 3012301371482672774798549)
              ·
                refine ⟨70600813394125143159341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3012301371482672774798549 70600813394125143159341)
                ·
                  rfl

theorem cell22_1856177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 7].length) (baseStart_1856177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1856177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1856177 prefixEnd_1856177 := by exact prefixLift 1856177
  have htrace : WordTrace (prefixWord ++ tailWord_1856177) baseStart_1856177 baseEnd_1856177 := by
    simpa [prefixWord, tailWord_1856177, baseEnd_1856177] using wordTrace_append hprefix tailTrace_1856177
  have hstable : (prefixWord ++ tailWord_1856177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856177).length < 2 ^ (prefixWord ++ tailWord_1856177).sum := by decide
  have hdescent : baseEnd_1856177 < baseStart_1856177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856233 : List Nat := [1, 2, 1, 1, 1, 2, 5, 3, 6]
def baseStart_1856233 : Nat := 118140960795 + 1856233 * 2 ^ 59
def prefixEnd_1856233 : Nat := 4983230072969 + 3 ^ 40 * 1856233 * 2
def baseEnd_1856233 : Nat := 211808830163853603011299

theorem tailTrace_1856233 : CollatzResearch.WordTrace tailWord_1856233 prefixEnd_1856233 211808830163853603011299 := by
  unfold tailWord_1856233
  simp only [CollatzResearch.WordTrace]
  refine ⟨67702379484192335202309353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45134919656128223468206235 67702379484192335202309353)
  ·
    refine ⟨50776784613144251401732015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67702379484192335202309353 50776784613144251401732015)
    ·
      refine ⟨76165176919716377102598023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50776784613144251401732015 76165176919716377102598023)
      ·
        refine ⟨114247765379574565653897035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76165176919716377102598023 114247765379574565653897035)
        ·
          refine ⟨171371648069361848480845553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114247765379574565653897035 171371648069361848480845553)
          ·
            refine ⟨128528736052021386360634165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171371648069361848480845553 128528736052021386360634165)
            ·
              refine ⟨12049569004877004971309453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128528736052021386360634165 12049569004877004971309453)
              ·
                refine ⟨4518588376828876864241045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12049569004877004971309453 4518588376828876864241045)
                ·
                  refine ⟨211808830163853603011299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4518588376828876864241045 211808830163853603011299)
                  ·
                    rfl

theorem cell22_1856233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 6].length) (baseStart_1856233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1856233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1856233 prefixEnd_1856233 := by exact prefixLift 1856233
  have htrace : WordTrace (prefixWord ++ tailWord_1856233) baseStart_1856233 baseEnd_1856233 := by
    simpa [prefixWord, tailWord_1856233, baseEnd_1856233] using wordTrace_append hprefix tailTrace_1856233
  have hstable : (prefixWord ++ tailWord_1856233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856233).length < 2 ^ (prefixWord ++ tailWord_1856233).sum := by decide
  have hdescent : baseEnd_1856233 < baseStart_1856233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856252 : List Nat := [2, 2, 2, 1, 3, 3, 2, 2, 1, 4]
def baseStart_1856252 : Nat := 118140960795 + 1856252 * 2 ^ 59
def prefixEnd_1856252 : Nat := 4983230072969 + 3 ^ 40 * 1856252 * 2
def baseEnd_1856252 : Nat := 635432994579851092808839

theorem tailTrace_1856252 : CollatzResearch.WordTrace tailWord_1856252 prefixEnd_1856252 635432994579851092808839 := by
  unfold tailWord_1856252
  simp only [CollatzResearch.WordTrace]
  refine ⟨33851536235561750723625505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45135381647415667631500673 33851536235561750723625505)
  ·
    refine ⟨25388652176671313042719129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33851536235561750723625505 25388652176671313042719129)
    ·
      refine ⟨19041489132503484782039347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25388652176671313042719129 19041489132503484782039347)
      ·
        refine ⟨28562233698755227173059021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19041489132503484782039347 28562233698755227173059021)
        ·
          refine ⟨10710837637033210189897133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28562233698755227173059021 10710837637033210189897133)
          ·
            refine ⟨4016564113887453821211425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10710837637033210189897133 4016564113887453821211425)
            ·
              refine ⟨3012423085415590365908569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4016564113887453821211425 3012423085415590365908569)
              ·
                refine ⟨2259317314061692774431427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3012423085415590365908569 2259317314061692774431427)
                ·
                  refine ⟨3388975971092539161647141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2259317314061692774431427 3388975971092539161647141)
                  ·
                    refine ⟨635432994579851092808839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3388975971092539161647141 635432994579851092808839)
                    ·
                      rfl

theorem cell22_1856252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_1856252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1856252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1856252 prefixEnd_1856252 := by exact prefixLift 1856252
  have htrace : WordTrace (prefixWord ++ tailWord_1856252) baseStart_1856252 baseEnd_1856252 := by
    simpa [prefixWord, tailWord_1856252, baseEnd_1856252] using wordTrace_append hprefix tailTrace_1856252
  have hstable : (prefixWord ++ tailWord_1856252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856252).length < 2 ^ (prefixWord ++ tailWord_1856252).sum := by decide
  have hdescent : baseEnd_1856252 < baseStart_1856252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856265 : List Nat := [1, 2, 1, 1, 3, 2, 3, 2, 4, 3]
def baseStart_1856265 : Nat := 118140960795 + 1856265 * 2 ^ 59
def prefixEnd_1856265 : Nat := 4983230072969 + 3 ^ 40 * 1856265 * 2
def baseEnd_1856265 : Nat := 635437444745523392233799

theorem tailTrace_1856265 : CollatzResearch.WordTrace tailWord_1856265 prefixEnd_1856265 635437444745523392233799 := by
  unfold tailWord_1856265
  simp only [CollatzResearch.WordTrace]
  refine ⟨67703546620076404667474249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45135697746717603111649499 67703546620076404667474249)
  ·
    refine ⟨50777659965057303500605687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67703546620076404667474249 50777659965057303500605687)
    ·
      refine ⟨76166489947585955250908531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50777659965057303500605687 76166489947585955250908531)
      ·
        refine ⟨114249734921378932876362797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76166489947585955250908531 114249734921378932876362797)
        ·
          refine ⟨42843650595517099828636049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114249734921378932876362797 42843650595517099828636049)
          ·
            refine ⟨32132737946637824871477037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42843650595517099828636049 32132737946637824871477037)
            ·
              refine ⟨12049776729989184326803889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32132737946637824871477037 12049776729989184326803889)
              ·
                refine ⟨9037332547491888245102917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12049776729989184326803889 9037332547491888245102917)
                ·
                  refine ⟨1694499852654729045956797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9037332547491888245102917 1694499852654729045956797)
                  ·
                    refine ⟨635437444745523392233799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1694499852654729045956797 635437444745523392233799)
                    ·
                      rfl

theorem cell22_1856265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 4, 3].length) (baseStart_1856265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1856265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1856265 prefixEnd_1856265 := by exact prefixLift 1856265
  have htrace : WordTrace (prefixWord ++ tailWord_1856265) baseStart_1856265 baseEnd_1856265 := by
    simpa [prefixWord, tailWord_1856265, baseEnd_1856265] using wordTrace_append hprefix tailTrace_1856265
  have hstable : (prefixWord ++ tailWord_1856265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856265).length < 2 ^ (prefixWord ++ tailWord_1856265).sum := by decide
  have hdescent : baseEnd_1856265 < baseStart_1856265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856282 : List Nat := [3, 1, 1, 3, 2, 1, 2, 4, 2, 3]
def baseStart_1856282 : Nat := 118140960795 + 1856282 * 2 ^ 59
def prefixEnd_1856282 : Nat := 4983230072969 + 3 ^ 40 * 1856282 * 2
def baseEnd_1856282 : Nat := 635443264192941014558747

theorem tailTrace_1856282 : CollatzResearch.WordTrace tailWord_1856282 prefixEnd_1856282 635443264192941014558747 := by
  unfold tailWord_1856282
  simp only [CollatzResearch.WordTrace]
  refine ⟨16926041665253704142710775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45136111107343211047228733 16926041665253704142710775)
  ·
    refine ⟨25389062497880556214066163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16926041665253704142710775 25389062497880556214066163)
    ·
      refine ⟨38083593746820834321099245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25389062497880556214066163 38083593746820834321099245)
      ·
        refine ⟨14281347655057812870412217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38083593746820834321099245 14281347655057812870412217)
        ·
          refine ⟨10711010741293359652809163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14281347655057812870412217 10711010741293359652809163)
          ·
            refine ⟨16066516111940039479213745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10711010741293359652809163 16066516111940039479213745)
            ·
              refine ⟨12049887083955029609410309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16066516111940039479213745 12049887083955029609410309)
              ·
                refine ⟨2259353828241568051764433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12049887083955029609410309 2259353828241568051764433)
                ·
                  refine ⟨1694515371181176038823325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2259353828241568051764433 1694515371181176038823325)
                  ·
                    refine ⟨635443264192941014558747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1694515371181176038823325 635443264192941014558747)
                    ·
                      rfl

theorem cell22_1856282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 2, 3].length) (baseStart_1856282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1856282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1856282 prefixEnd_1856282 := by exact prefixLift 1856282
  have htrace : WordTrace (prefixWord ++ tailWord_1856282) baseStart_1856282 baseEnd_1856282 := by
    simpa [prefixWord, tailWord_1856282, baseEnd_1856282] using wordTrace_append hprefix tailTrace_1856282
  have hstable : (prefixWord ++ tailWord_1856282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856282).length < 2 ^ (prefixWord ++ tailWord_1856282).sum := by decide
  have hdescent : baseEnd_1856282 < baseStart_1856282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856284 : List Nat := [2, 2, 3, 1, 1, 4, 3, 2, 4]
def baseStart_1856284 : Nat := 118140960795 + 1856284 * 2 ^ 59
def prefixEnd_1856284 : Nat := 4983230072969 + 3 ^ 40 * 1856284 * 2
def baseEnd_1856284 : Nat := 211814649611271225336247

theorem tailTrace_1856284 : CollatzResearch.WordTrace tailWord_1856284 prefixEnd_1856284 211814649611271225336247 := by
  unfold tailWord_1856284
  simp only [CollatzResearch.WordTrace]
  refine ⟨33852119803503785456207953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45136159738005047274943937 33852119803503785456207953)
  ·
    refine ⟨25389089852627839092155965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33852119803503785456207953 25389089852627839092155965)
    ·
      refine ⟨9520908694735439659558487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25389089852627839092155965 9520908694735439659558487)
      ·
        refine ⟨14281363042103159489337731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9520908694735439659558487 14281363042103159489337731)
        ·
          refine ⟨21422044563154739234006597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14281363042103159489337731 21422044563154739234006597)
          ·
            refine ⟨4016633355591513606376237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21422044563154739234006597 4016633355591513606376237)
            ·
              refine ⟨1506237508346817602391089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4016633355591513606376237 1506237508346817602391089)
              ·
                refine ⟨1129678131260113201793317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1506237508346817602391089 1129678131260113201793317)
                ·
                  refine ⟨211814649611271225336247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1129678131260113201793317 211814649611271225336247)
                  ·
                    rfl

theorem cell22_1856284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 2, 4].length) (baseStart_1856284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1856284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1856284 prefixEnd_1856284 := by exact prefixLift 1856284
  have htrace : WordTrace (prefixWord ++ tailWord_1856284) baseStart_1856284 baseEnd_1856284 := by
    simpa [prefixWord, tailWord_1856284, baseEnd_1856284] using wordTrace_append hprefix tailTrace_1856284
  have hstable : (prefixWord ++ tailWord_1856284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856284).length < 2 ^ (prefixWord ++ tailWord_1856284).sum := by decide
  have hdescent : baseEnd_1856284 < baseStart_1856284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856355 : List Nat := [1, 1, 1, 5, 3, 1, 1, 1, 1, 7]
def baseStart_1856355 : Nat := 118140960795 + 1856355 * 2 ^ 59
def prefixEnd_1856355 : Nat := 4983230072969 + 3 ^ 40 * 1856355 * 2
def baseEnd_1856355 : Nat := 635468253584793157483523

theorem tailTrace_1856355 : CollatzResearch.WordTrace tailWord_1856355 prefixEnd_1856355 635468253584793157483523 := by
  unfold tailWord_1856355
  simp only [CollatzResearch.WordTrace]
  refine ⟨67706829189750350038250519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45137886126500233358833679 67706829189750350038250519)
  ·
    refine ⟨101560243784625525057375779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67706829189750350038250519 101560243784625525057375779)
    ·
      refine ⟨152340365676938287586063669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101560243784625525057375779 152340365676938287586063669)
      ·
        refine ⟨14281909282212964461193469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152340365676938287586063669 14281909282212964461193469)
        ·
          refine ⟨5355715980829861672947551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14281909282212964461193469 5355715980829861672947551)
          ·
            refine ⟨8033573971244792509421327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5355715980829861672947551 8033573971244792509421327)
            ·
              refine ⟨12050360956867188764131991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8033573971244792509421327 12050360956867188764131991)
              ·
                refine ⟨18075541435300783146197987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12050360956867188764131991 18075541435300783146197987)
                ·
                  refine ⟨27113312152951174719296981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18075541435300783146197987 27113312152951174719296981)
                  ·
                    refine ⟨635468253584793157483523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27113312152951174719296981 635468253584793157483523)
                    ·
                      rfl

theorem cell22_1856355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 7].length) (baseStart_1856355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1856355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1856355 prefixEnd_1856355 := by exact prefixLift 1856355
  have htrace : WordTrace (prefixWord ++ tailWord_1856355) baseStart_1856355 baseEnd_1856355 := by
    simpa [prefixWord, tailWord_1856355, baseEnd_1856355] using wordTrace_append hprefix tailTrace_1856355
  have hstable : (prefixWord ++ tailWord_1856355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856355).length < 2 ^ (prefixWord ++ tailWord_1856355).sum := by decide
  have hdescent : baseEnd_1856355 < baseStart_1856355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856387 : List Nat := [1, 1, 1, 3, 4, 1, 3, 3, 1, 4]
def baseStart_1856387 : Nat := 118140960795 + 1856387 * 2 ^ 59
def prefixEnd_1856387 : Nat := 4983230072969 + 3 ^ 40 * 1856387 * 2
def baseEnd_1856387 : Nat := 635479207838755740683425

theorem tailTrace_1856387 : CollatzResearch.WordTrace tailWord_1856387 prefixEnd_1856387 635479207838755740683425 := by
  unfold tailWord_1856387
  simp only [CollatzResearch.WordTrace]
  refine ⟨67707996325634419503415415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45138664217089613002276943 67707996325634419503415415)
  ·
    refine ⟨101561994488451629255123123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67707996325634419503415415 101561994488451629255123123)
    ·
      refine ⟨152342991732677443882684685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101561994488451629255123123 152342991732677443882684685)
      ·
        refine ⟨57128621899754041456006757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152342991732677443882684685 57128621899754041456006757)
        ·
          refine ⟨10711616606203882773001267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57128621899754041456006757 10711616606203882773001267)
          ·
            refine ⟨16067424909305824159501901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10711616606203882773001267 16067424909305824159501901)
            ·
              refine ⟨6025284340989684059813213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16067424909305824159501901 6025284340989684059813213)
              ·
                refine ⟨2259481627871131522429955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6025284340989684059813213 2259481627871131522429955)
                ·
                  refine ⟨3389222441806697283644933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2259481627871131522429955 3389222441806697283644933)
                  ·
                    refine ⟨635479207838755740683425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3389222441806697283644933 635479207838755740683425)
                    ·
                      rfl

theorem cell22_1856387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 4].length) (baseStart_1856387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1856387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1856387 prefixEnd_1856387 := by exact prefixLift 1856387
  have htrace : WordTrace (prefixWord ++ tailWord_1856387) baseStart_1856387 baseEnd_1856387 := by
    simpa [prefixWord, tailWord_1856387, baseEnd_1856387] using wordTrace_append hprefix tailTrace_1856387
  have hstable : (prefixWord ++ tailWord_1856387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856387).length < 2 ^ (prefixWord ++ tailWord_1856387).sum := by decide
  have hdescent : baseEnd_1856387 < baseStart_1856387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856406 : List Nat := [5, 3, 1, 1, 1, 1, 2, 1, 2, 5]
def baseStart_1856406 : Nat := 118140960795 + 1856406 * 2 ^ 59
def prefixEnd_1856406 : Nat := 4983230072969 + 3 ^ 40 * 1856406 * 2
def baseEnd_1856406 : Nat := 635485711927046024458367

theorem tailTrace_1856406 : CollatzResearch.WordTrace tailWord_1856406 prefixEnd_1856406 635485711927046024458367 := by
  unfold tailWord_1856406
  simp only [CollatzResearch.WordTrace]
  refine ⟨4231793082035349109272317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45139126208377057165571381 4231793082035349109272317)
  ·
    refine ⟨1586922405763255915977119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4231793082035349109272317 1586922405763255915977119)
    ·
      refine ⟨2380383608644883873965679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1586922405763255915977119 2380383608644883873965679)
      ·
        refine ⟨3570575412967325810948519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2380383608644883873965679 3570575412967325810948519)
        ·
          refine ⟨5355863119450988716422779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3570575412967325810948519 5355863119450988716422779)
          ·
            refine ⟨8033794679176483074634169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5355863119450988716422779 8033794679176483074634169)
            ·
              refine ⟨6025346009382362305975627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8033794679176483074634169 6025346009382362305975627)
              ·
                refine ⟨9038019014073543458963441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6025346009382362305975627 9038019014073543458963441)
                ·
                  refine ⟨6778514260555157594222581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9038019014073543458963441 6778514260555157594222581)
                  ·
                    refine ⟨635485711927046024458367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6778514260555157594222581 635485711927046024458367)
                    ·
                      rfl

theorem cell22_1856406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_1856406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1856406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1856406 prefixEnd_1856406 := by exact prefixLift 1856406
  have htrace : WordTrace (prefixWord ++ tailWord_1856406) baseStart_1856406 baseEnd_1856406 := by
    simpa [prefixWord, tailWord_1856406, baseEnd_1856406] using wordTrace_append hprefix tailTrace_1856406
  have hstable : (prefixWord ++ tailWord_1856406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856406).length < 2 ^ (prefixWord ++ tailWord_1856406).sum := by decide
  have hdescent : baseEnd_1856406 < baseStart_1856406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856468 : List Nat := [2, 4, 1, 2, 1, 4, 2, 1, 2, 3]
def baseStart_1856468 : Nat := 118140960795 + 1856468 * 2 ^ 59
def prefixEnd_1856468 : Nat := 4983230072969 + 3 ^ 40 * 1856468 * 2
def baseEnd_1856468 : Nat := 635506935794098529408177

theorem tailTrace_1856468 : CollatzResearch.WordTrace tailWord_1856468 prefixEnd_1856468 635506935794098529408177 := by
  unfold tailWord_1856468
  simp only [CollatzResearch.WordTrace]
  refine ⟨33855475319170485168557029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45140633758893980224742705 33855475319170485168557029)
  ·
    refine ⟨6347901622344465969104443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33855475319170485168557029 6347901622344465969104443)
    ·
      refine ⟨9521852433516698953656665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6347901622344465969104443 9521852433516698953656665)
      ·
        refine ⟨7141389325137524215242499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9521852433516698953656665 7141389325137524215242499)
        ·
          refine ⟨10712083987706286322863749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7141389325137524215242499 10712083987706286322863749)
          ·
            refine ⟨2008515747694928685536953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10712083987706286322863749 2008515747694928685536953)
            ·
              refine ⟨1506386810771196514152715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2008515747694928685536953 1506386810771196514152715)
              ·
                refine ⟨2259580216156794771229073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1506386810771196514152715 2259580216156794771229073)
                ·
                  refine ⟨1694685162117596078421805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2259580216156794771229073 1694685162117596078421805)
                  ·
                    refine ⟨635506935794098529408177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1694685162117596078421805 635506935794098529408177)
                    ·
                      rfl

theorem cell22_1856468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_1856468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1856468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1856468 prefixEnd_1856468 := by exact prefixLift 1856468
  have htrace : WordTrace (prefixWord ++ tailWord_1856468) baseStart_1856468 baseEnd_1856468 := by
    simpa [prefixWord, tailWord_1856468, baseEnd_1856468] using wordTrace_append hprefix tailTrace_1856468
  have hstable : (prefixWord ++ tailWord_1856468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856468).length < 2 ^ (prefixWord ++ tailWord_1856468).sum := by decide
  have hdescent : baseEnd_1856468 < baseStart_1856468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856513 : List Nat := [1, 2, 4, 1, 2, 2, 4, 2, 1, 3]
def baseStart_1856513 : Nat := 118140960795 + 1856513 * 2 ^ 59
def prefixEnd_1856513 : Nat := 4983230072969 + 3 ^ 40 * 1856513 * 2
def baseEnd_1856513 : Nat := 635522340213733412033039

theorem tailTrace_1856513 : CollatzResearch.WordTrace tailWord_1856513 prefixEnd_1856513 635522340213733412033039 := by
  unfold tailWord_1856513
  simp only [CollatzResearch.WordTrace]
  refine ⟨67712591923177943022502193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45141727948785295348334795 67712591923177943022502193)
  ·
    refine ⟨50784443942383457266876645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67712591923177943022502193 50784443942383457266876645)
    ·
      refine ⟨9522083239196898237539371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50784443942383457266876645 9522083239196898237539371)
      ·
        refine ⟨14283124858795347356309057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9522083239196898237539371 14283124858795347356309057)
        ·
          refine ⟨10712343644096510517231793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14283124858795347356309057 10712343644096510517231793)
          ·
            refine ⟨8034257733072382887923845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10712343644096510517231793 8034257733072382887923845)
            ·
              refine ⟨1506423324951071791485721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8034257733072382887923845 1506423324951071791485721)
              ·
                refine ⟨1129817493713303843614291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1506423324951071791485721 1129817493713303843614291)
                ·
                  refine ⟨1694726240569955765421437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1129817493713303843614291 1694726240569955765421437)
                  ·
                    refine ⟨635522340213733412033039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1694726240569955765421437 635522340213733412033039)
                    ·
                      rfl

theorem cell22_1856513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_1856513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1856513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1856513 prefixEnd_1856513 := by exact prefixLift 1856513
  have htrace : WordTrace (prefixWord ++ tailWord_1856513) baseStart_1856513 baseEnd_1856513 := by
    simpa [prefixWord, tailWord_1856513, baseEnd_1856513] using wordTrace_append hprefix tailTrace_1856513
  have hstable : (prefixWord ++ tailWord_1856513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856513).length < 2 ^ (prefixWord ++ tailWord_1856513).sum := by decide
  have hdescent : baseEnd_1856513 < baseStart_1856513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856530 : List Nat := [3, 2, 5, 1, 1, 1, 1, 2, 3, 3]
def baseStart_1856530 : Nat := 118140960795 + 1856530 * 2 ^ 59
def prefixEnd_1856530 : Nat := 4983230072969 + 3 ^ 40 * 1856530 * 2
def baseEnd_1856530 : Nat := 635528159661151034357987

theorem tailTrace_1856530 : CollatzResearch.WordTrace tailWord_1856530 prefixEnd_1856530 635528159661151034357987 := by
  unfold tailWord_1856530
  simp only [CollatzResearch.WordTrace]
  refine ⟨16928302991029088731467761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45142141309410903283914029 16928302991029088731467761)
  ·
    refine ⟨12696227243271816548600821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16928302991029088731467761 12696227243271816548600821)
    ·
      refine ⟨1190271304056732801431327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12696227243271816548600821 1190271304056732801431327)
      ·
        refine ⟨1785406956085099202146991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1190271304056732801431327 1785406956085099202146991)
        ·
          refine ⟨2678110434127648803220487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1785406956085099202146991 2678110434127648803220487)
          ·
            refine ⟨4017165651191473204830731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2678110434127648803220487 4017165651191473204830731)
            ·
              refine ⟨6025748476787209807246097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4017165651191473204830731 6025748476787209807246097)
              ·
                refine ⟨4519311357590407355434573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6025748476787209807246097 4519311357590407355434573)
                ·
                  refine ⟨1694741759096402758287965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4519311357590407355434573 1694741759096402758287965)
                  ·
                    refine ⟨635528159661151034357987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1694741759096402758287965 635528159661151034357987)
                    ·
                      rfl

theorem cell22_1856530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_1856530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1856530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1856530 prefixEnd_1856530 := by exact prefixLift 1856530
  have htrace : WordTrace (prefixWord ++ tailWord_1856530) baseStart_1856530 baseEnd_1856530 := by
    simpa [prefixWord, tailWord_1856530, baseEnd_1856530] using wordTrace_append hprefix tailTrace_1856530
  have hstable : (prefixWord ++ tailWord_1856530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856530).length < 2 ^ (prefixWord ++ tailWord_1856530).sum := by decide
  have hdescent : baseEnd_1856530 < baseStart_1856530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856567 : List Nat := [1, 1, 3, 1, 2, 2, 1, 3, 4, 4]
def baseStart_1856567 : Nat := 118140960795 + 1856567 * 2 ^ 59
def prefixEnd_1856567 : Nat := 4983230072969 + 3 ^ 40 * 1856567 * 2
def baseEnd_1856567 : Nat := 635540825517295271182873

theorem tailTrace_1856567 : CollatzResearch.WordTrace tailWord_1856567 prefixEnd_1856567 635540825517295271182873 := by
  unfold tailWord_1856567
  simp only [CollatzResearch.WordTrace]
  refine ⟨67714561464982310244967955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45143040976654873496645303 67714561464982310244967955)
  ·
    refine ⟨101571842197473465367451933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67714561464982310244967955 101571842197473465367451933)
    ·
      refine ⟨38089440824052549512794475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101571842197473465367451933 38089440824052549512794475)
      ·
        refine ⟨57134161236078824269191713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38089440824052549512794475 57134161236078824269191713)
        ·
          refine ⟨42850620927059118201893785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57134161236078824269191713 42850620927059118201893785)
          ·
            refine ⟨32137965695294338651420339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42850620927059118201893785 32137965695294338651420339)
            ·
              refine ⟨48206948542941507977130509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32137965695294338651420339 48206948542941507977130509)
              ·
                refine ⟨18077605703603065491423941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48206948542941507977130509 18077605703603065491423941)
                ·
                  refine ⟨3389551069425574779641989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18077605703603065491423941 3389551069425574779641989)
                  ·
                    refine ⟨635540825517295271182873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3389551069425574779641989 635540825517295271182873)
                    ·
                      rfl

theorem cell22_1856567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_1856567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1856567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1856567 prefixEnd_1856567 := by exact prefixLift 1856567
  have htrace : WordTrace (prefixWord ++ tailWord_1856567) baseStart_1856567 baseEnd_1856567 := by
    simpa [prefixWord, tailWord_1856567, baseEnd_1856567] using wordTrace_append hprefix tailTrace_1856567
  have hstable : (prefixWord ++ tailWord_1856567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856567).length < 2 ^ (prefixWord ++ tailWord_1856567).sum := by decide
  have hdescent : baseEnd_1856567 < baseStart_1856567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856597 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 2, 7]
def baseStart_1856597 : Nat := 118140960795 + 1856597 * 2 ^ 59
def prefixEnd_1856597 : Nat := 4983230072969 + 3 ^ 40 * 1856597 * 2
def baseEnd_1856597 : Nat := 635551095130385192932781

theorem tailTrace_1856597 : CollatzResearch.WordTrace tailWord_1856597 prefixEnd_1856597 635551095130385192932781 := by
  unfold tailWord_1856597
  simp only [CollatzResearch.WordTrace]
  refine ⟨67715655654873625368560045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45143770436582416912373363 67715655654873625368560045)
  ·
    refine ⟨25393370870577609513210017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67715655654873625368560045 25393370870577609513210017)
    ·
      refine ⟨19045028152933207134907513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25393370870577609513210017 19045028152933207134907513)
      ·
        refine ⟨14283771114699905351180635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19045028152933207134907513 14283771114699905351180635)
        ·
          refine ⟨21425656672049858026770953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14283771114699905351180635 21425656672049858026770953)
          ·
            refine ⟨16069242504037393520078215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21425656672049858026770953 16069242504037393520078215)
            ·
              refine ⟨24103863756056090280117323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16069242504037393520078215 24103863756056090280117323)
              ·
                refine ⟨36155795634084135420175985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24103863756056090280117323 36155795634084135420175985)
                ·
                  refine ⟨27116846725563101565131989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36155795634084135420175985 27116846725563101565131989)
                  ·
                    refine ⟨635551095130385192932781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27116846725563101565131989 635551095130385192932781)
                    ·
                      rfl

theorem cell22_1856597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_1856597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1856597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1856597 prefixEnd_1856597 := by exact prefixLift 1856597
  have htrace : WordTrace (prefixWord ++ tailWord_1856597) baseStart_1856597 baseEnd_1856597 := by
    simpa [prefixWord, tailWord_1856597, baseEnd_1856597] using wordTrace_append hprefix tailTrace_1856597
  have hstable : (prefixWord ++ tailWord_1856597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856597).length < 2 ^ (prefixWord ++ tailWord_1856597).sum := by decide
  have hdescent : baseEnd_1856597 < baseStart_1856597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856605 : List Nat := [1, 4, 4, 1, 2, 2, 1, 3, 4]
def baseStart_1856605 : Nat := 118140960795 + 1856605 * 2 ^ 59
def prefixEnd_1856605 : Nat := 4983230072969 + 3 ^ 40 * 1856605 * 2
def baseEnd_1856605 : Nat := 211851277897958612910919

theorem tailTrace_1856605 : CollatzResearch.WordTrace tailWord_1856605 prefixEnd_1856605 211851277897958612910919 := by
  unfold tailWord_1856605
  simp only [CollatzResearch.WordTrace]
  refine ⟨67715947438844642734851269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45143964959229761823234179 67715947438844642734851269)
  ·
    refine ⟨12696740144783370512784613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67715947438844642734851269 12696740144783370512784613)
    ·
      refine ⟨2380638777146881971147115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12696740144783370512784613 2380638777146881971147115)
      ·
        refine ⟨3570958165720322956720673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2380638777146881971147115 3570958165720322956720673)
        ·
          refine ⟨2678218624290242217540505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3570958165720322956720673 2678218624290242217540505)
          ·
            refine ⟨2008663968217681663155379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2678218624290242217540505 2008663968217681663155379)
            ·
              refine ⟨3012995952326522494733069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2008663968217681663155379 3012995952326522494733069)
              ·
                refine ⟨1129873482122445935524901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3012995952326522494733069 1129873482122445935524901)
                ·
                  refine ⟨211851277897958612910919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1129873482122445935524901 211851277897958612910919)
                  ·
                    rfl

theorem cell22_1856605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_1856605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1856605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1856605 prefixEnd_1856605 := by exact prefixLift 1856605
  have htrace : WordTrace (prefixWord ++ tailWord_1856605) baseStart_1856605 baseEnd_1856605 := by
    simpa [prefixWord, tailWord_1856605, baseEnd_1856605] using wordTrace_append hprefix tailTrace_1856605
  have hstable : (prefixWord ++ tailWord_1856605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856605).length < 2 ^ (prefixWord ++ tailWord_1856605).sum := by decide
  have hdescent : baseEnd_1856605 < baseStart_1856605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856612 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 1, 8]
def baseStart_1856612 : Nat := 118140960795 + 1856612 * 2 ^ 59
def prefixEnd_1856612 : Nat := 4983230072969 + 3 ^ 40 * 1856612 * 2
def baseEnd_1856612 : Nat := 635556229936930153807735

theorem tailTrace_1856612 : CollatzResearch.WordTrace tailWord_1856612 prefixEnd_1856612 635556229936930153807735 := by
  unfold tailWord_1856612
  simp only [CollatzResearch.WordTrace]
  refine ⟨33858101374909641465178045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45144135166546188620237393 33858101374909641465178045)
  ·
    refine ⟨12696788015591115549441767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33858101374909641465178045 12696788015591115549441767)
    ·
      refine ⟨19045182023386673324162651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12696788015591115549441767 19045182023386673324162651)
      ·
        refine ⟨28567773035080009986243977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19045182023386673324162651 28567773035080009986243977)
        ·
          refine ⟨21425829776310007489682983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28567773035080009986243977 21425829776310007489682983)
          ·
            refine ⟨32138744664465011234524475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21425829776310007489682983 32138744664465011234524475)
            ·
              refine ⟨48208116996697516851786713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32138744664465011234524475 48208116996697516851786713)
              ·
                refine ⟨36156087747523137638840035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48208116996697516851786713 36156087747523137638840035)
                ·
                  refine ⟨54234131621284706458260053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36156087747523137638840035 54234131621284706458260053)
                  ·
                    refine ⟨635556229936930153807735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54234131621284706458260053 635556229936930153807735)
                    ·
                      rfl

theorem cell22_1856612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_1856612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1856612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1856612 prefixEnd_1856612 := by exact prefixLift 1856612
  have htrace : WordTrace (prefixWord ++ tailWord_1856612) baseStart_1856612 baseEnd_1856612 := by
    simpa [prefixWord, tailWord_1856612, baseEnd_1856612] using wordTrace_append hprefix tailTrace_1856612
  have hstable : (prefixWord ++ tailWord_1856612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856612).length < 2 ^ (prefixWord ++ tailWord_1856612).sum := by decide
  have hdescent : baseEnd_1856612 < baseStart_1856612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856616 : List Nat := [2, 1, 4, 4, 1, 2, 8]
def baseStart_1856616 : Nat := 118140960795 + 1856616 * 2 ^ 59
def prefixEnd_1856616 : Nat := 4983230072969 + 3 ^ 40 * 1856616 * 2
def baseEnd_1856616 : Nat := 23539170341432425063249

theorem tailTrace_1856616 : CollatzResearch.WordTrace tailWord_1856616 prefixEnd_1856616 23539170341432425063249 := by
  unfold tailWord_1856616
  simp only [CollatzResearch.WordTrace]
  refine ⟨33858174320902395806750851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45144232427869861075667801 33858174320902395806750851)
  ·
    refine ⟨50787261481353593710126277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33858174320902395806750851 50787261481353593710126277)
    ·
      refine ⟨9522611527753798820648677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50787261481353593710126277 9522611527753798820648677)
      ·
        refine ⟨1785489661453837278871627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9522611527753798820648677 1785489661453837278871627)
        ·
          refine ⟨2678234492180755918307441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1785489661453837278871627 2678234492180755918307441)
          ·
            refine ⟨2008675869135566938730581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2678234492180755918307441 2008675869135566938730581)
            ·
              refine ⟨23539170341432425063249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2008675869135566938730581 23539170341432425063249)
              ·
                rfl

theorem cell22_1856616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 8].length) (baseStart_1856616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1856616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1856616 prefixEnd_1856616 := by exact prefixLift 1856616
  have htrace : WordTrace (prefixWord ++ tailWord_1856616) baseStart_1856616 baseEnd_1856616 := by
    simpa [prefixWord, tailWord_1856616, baseEnd_1856616] using wordTrace_append hprefix tailTrace_1856616
  have hstable : (prefixWord ++ tailWord_1856616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856616).length < 2 ^ (prefixWord ++ tailWord_1856616).sum := by decide
  have hdescent : baseEnd_1856616 < baseStart_1856616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856682 : List Nat := [3, 1, 5, 1, 1, 1, 4, 2, 1, 3]
def baseStart_1856682 : Nat := 118140960795 + 1856682 * 2 ^ 59
def prefixEnd_1856682 : Nat := 4983230072969 + 3 ^ 40 * 1856682 * 2
def baseEnd_1856682 : Nat := 635580192367473304557521

theorem tailTrace_1856682 : CollatzResearch.WordTrace tailWord_1856682 prefixEnd_1856682 635580192367473304557521 := by
  unfold tailWord_1856682
  simp only [CollatzResearch.WordTrace]
  refine ⟨16929688964891421221351075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45145837239710456590269533 16929688964891421221351075)
  ·
    refine ⟨25394533447337131832026613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16929688964891421221351075 25394533447337131832026613)
    ·
      refine ⟨2380737510687856109252495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25394533447337131832026613 2380737510687856109252495)
      ·
        refine ⟨3571106266031784163878743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2380737510687856109252495 3571106266031784163878743)
        ·
          refine ⟨5356659399047676245818115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3571106266031784163878743 5356659399047676245818115)
          ·
            refine ⟨8034989098571514368727173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5356659399047676245818115 8034989098571514368727173)
            ·
              refine ⟨1506560455982158944136345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8034989098571514368727173 1506560455982158944136345)
              ·
                refine ⟨1129920341986619208102259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1506560455982158944136345 1129920341986619208102259)
                ·
                  refine ⟨1694880512979928812153389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1129920341986619208102259 1694880512979928812153389)
                  ·
                    refine ⟨635580192367473304557521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1694880512979928812153389 635580192367473304557521)
                    ·
                      rfl

theorem cell22_1856682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_1856682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1856682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1856682 prefixEnd_1856682 := by exact prefixLift 1856682
  have htrace : WordTrace (prefixWord ++ tailWord_1856682) baseStart_1856682 baseEnd_1856682 := by
    simpa [prefixWord, tailWord_1856682, baseEnd_1856682] using wordTrace_append hprefix tailTrace_1856682
  have hstable : (prefixWord ++ tailWord_1856682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856682).length < 2 ^ (prefixWord ++ tailWord_1856682).sum := by decide
  have hdescent : baseEnd_1856682 < baseStart_1856682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856719 : List Nat := [1, 1, 2, 1, 1, 3, 2, 5, 2, 4]
def baseStart_1856719 : Nat := 118140960795 + 1856719 * 2 ^ 59
def prefixEnd_1856719 : Nat := 4983230072969 + 3 ^ 40 * 1856719 * 2
def baseEnd_1856719 : Nat := 635592858223617541382407

theorem tailTrace_1856719 : CollatzResearch.WordTrace tailWord_1856719 prefixEnd_1856719 635592858223617541382407 := by
  unfold tailWord_1856719
  simp only [CollatzResearch.WordTrace]
  refine ⟨67720105360431640204501211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45146736906954426803000807 67720105360431640204501211)
  ·
    refine ⟨101580158040647460306751817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67720105360431640204501211 101580158040647460306751817)
    ·
      refine ⟨76185118530485595230063863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101580158040647460306751817 76185118530485595230063863)
      ·
        refine ⟨114277677795728392845095795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76185118530485595230063863 114277677795728392845095795)
        ·
          refine ⟨171416516693592589267643693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114277677795728392845095795 171416516693592589267643693)
          ·
            refine ⟨64281193760097220975366385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171416516693592589267643693 64281193760097220975366385)
            ·
              refine ⟨48210895320072915731524789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64281193760097220975366385 48210895320072915731524789)
              ·
                refine ⟨4519771436256835849830449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48210895320072915731524789 4519771436256835849830449)
                ·
                  refine ⟨3389828577192626887372837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4519771436256835849830449 3389828577192626887372837)
                  ·
                    refine ⟨635592858223617541382407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3389828577192626887372837 635592858223617541382407)
                    ·
                      rfl

theorem cell22_1856719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 4].length) (baseStart_1856719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1856719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1856719 prefixEnd_1856719 := by exact prefixLift 1856719
  have htrace : WordTrace (prefixWord ++ tailWord_1856719) baseStart_1856719 baseEnd_1856719 := by
    simpa [prefixWord, tailWord_1856719, baseEnd_1856719] using wordTrace_append hprefix tailTrace_1856719
  have hstable : (prefixWord ++ tailWord_1856719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856719).length < 2 ^ (prefixWord ++ tailWord_1856719).sum := by decide
  have hdescent : baseEnd_1856719 < baseStart_1856719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856725 : List Nat := [1, 3, 2, 4, 1, 3, 2, 1, 1, 4]
def baseStart_1856725 : Nat := 118140960795 + 1856725 * 2 ^ 59
def prefixEnd_1856725 : Nat := 4983230072969 + 3 ^ 40 * 1856725 * 2
def baseEnd_1856725 : Nat := 635594912146235525732389

theorem tailTrace_1856725 : CollatzResearch.WordTrace tailWord_1856725 prefixEnd_1856725 635594912146235525732389 := by
  unfold tailWord_1856725
  simp only [CollatzResearch.WordTrace]
  refine ⟨67720324198409903229219629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45146882798939935486146419 67720324198409903229219629)
  ·
    refine ⟨25395121574403713710957361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67720324198409903229219629 25395121574403713710957361)
    ·
      refine ⟨19046341180802785283218021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25395121574403713710957361 19046341180802785283218021)
      ·
        refine ⟨3571188971400522240603379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19046341180802785283218021 3571188971400522240603379)
        ·
          refine ⟨5356783457100783360905069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3571188971400522240603379 5356783457100783360905069)
          ·
            refine ⟨2008793796412793760339401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5356783457100783360905069 2008793796412793760339401)
            ·
              refine ⟨1506595347309595320254551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2008793796412793760339401 1506595347309595320254551)
              ·
                refine ⟨2259893020964392980381827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1506595347309595320254551 2259893020964392980381827)
                ·
                  refine ⟨3389839531446589470572741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2259893020964392980381827 3389839531446589470572741)
                  ·
                    refine ⟨635594912146235525732389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3389839531446589470572741 635594912146235525732389)
                    ·
                      rfl

theorem cell22_1856725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 1, 4].length) (baseStart_1856725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1856725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1856725 prefixEnd_1856725 := by exact prefixLift 1856725
  have htrace : WordTrace (prefixWord ++ tailWord_1856725) baseStart_1856725 baseEnd_1856725 := by
    simpa [prefixWord, tailWord_1856725, baseEnd_1856725] using wordTrace_append hprefix tailTrace_1856725
  have hstable : (prefixWord ++ tailWord_1856725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856725).length < 2 ^ (prefixWord ++ tailWord_1856725).sum := by decide
  have hdescent : baseEnd_1856725 < baseStart_1856725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856779 : List Nat := [1, 1, 1, 1, 5, 3, 1, 2, 7]
def baseStart_1856779 : Nat := 118140960795 + 1856779 * 2 ^ 59
def prefixEnd_1856779 : Nat := 4983230072969 + 3 ^ 40 * 1856779 * 2
def baseEnd_1856779 : Nat := 211871132483265794960741

theorem tailTrace_1856779 : CollatzResearch.WordTrace tailWord_1856779 prefixEnd_1856779 211871132483265794960741 := by
  unfold tailWord_1856779
  simp only [CollatzResearch.WordTrace]
  refine ⟨67722293740214270451685391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45148195826809513634456927 67722293740214270451685391)
  ·
    refine ⟨101583440610321405677528087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67722293740214270451685391 101583440610321405677528087)
    ·
      refine ⟨152375160915482108516292131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101583440610321405677528087 152375160915482108516292131)
      ·
        refine ⟨228562741373223162774438197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152375160915482108516292131 228562741373223162774438197)
        ·
          refine ⟨21427757003739671510103581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 228562741373223162774438197 21427757003739671510103581)
          ·
            refine ⟨8035408876402376816288843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21427757003739671510103581 8035408876402376816288843)
            ·
              refine ⟨12053113314603565224433265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8035408876402376816288843 12053113314603565224433265)
              ·
                refine ⟨9039834985952673918324949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12053113314603565224433265 9039834985952673918324949)
                ·
                  refine ⟨211871132483265794960741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9039834985952673918324949 211871132483265794960741)
                  ·
                    rfl

theorem cell22_1856779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 7].length) (baseStart_1856779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1856779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1856779 prefixEnd_1856779 := by exact prefixLift 1856779
  have htrace : WordTrace (prefixWord ++ tailWord_1856779) baseStart_1856779 baseEnd_1856779 := by
    simpa [prefixWord, tailWord_1856779, baseEnd_1856779] using wordTrace_append hprefix tailTrace_1856779
  have hstable : (prefixWord ++ tailWord_1856779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856779).length < 2 ^ (prefixWord ++ tailWord_1856779).sum := by decide
  have hdescent : baseEnd_1856779 < baseStart_1856779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856800 : List Nat := [2, 1, 1, 5, 3, 2, 1, 1, 3, 3]
def baseStart_1856800 : Nat := 118140960795 + 1856800 * 2 ^ 59
def prefixEnd_1856800 : Nat := 4983230072969 + 3 ^ 40 * 1856800 * 2
def baseEnd_1856800 : Nat := 635620586178960330107159

theorem tailTrace_1856800 : CollatzResearch.WordTrace tailWord_1856800 prefixEnd_1856800 635620586178960330107159 := by
  unfold tailWord_1856800
  simp only [CollatzResearch.WordTrace]
  refine ⟨33861529836569095519099927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45148706448758794025466569 33861529836569095519099927)
  ·
    refine ⟨50792294754853643278649891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33861529836569095519099927 50792294754853643278649891)
    ·
      refine ⟨76188442132280464917974837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50792294754853643278649891 76188442132280464917974837)
      ·
        refine ⟨7142666449901293586060141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76188442132280464917974837 7142666449901293586060141)
        ·
          refine ⟨2678499918712985094772553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7142666449901293586060141 2678499918712985094772553)
          ·
            refine ⟨2008874939034738821079415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2678499918712985094772553 2008874939034738821079415)
            ·
              refine ⟨3013312408552108231619123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2008874939034738821079415 3013312408552108231619123)
              ·
                refine ⟨4519968612828162347428685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3013312408552108231619123 4519968612828162347428685)
                ·
                  refine ⟨1694988229810560880285757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4519968612828162347428685 1694988229810560880285757)
                  ·
                    refine ⟨635620586178960330107159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1694988229810560880285757 635620586178960330107159)
                    ·
                      rfl

theorem cell22_1856800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 3, 3].length) (baseStart_1856800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1856800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1856800 prefixEnd_1856800 := by exact prefixLift 1856800
  have htrace : WordTrace (prefixWord ++ tailWord_1856800) baseStart_1856800 baseEnd_1856800 := by
    simpa [prefixWord, tailWord_1856800, baseEnd_1856800] using wordTrace_append hprefix tailTrace_1856800
  have hstable : (prefixWord ++ tailWord_1856800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856800).length < 2 ^ (prefixWord ++ tailWord_1856800).sum := by decide
  have hdescent : baseEnd_1856800 < baseStart_1856800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856824 : List Nat := [2, 1, 2, 1, 3, 1, 1, 3, 8]
def baseStart_1856824 : Nat := 118140960795 + 1856824 * 2 ^ 59
def prefixEnd_1856824 : Nat := 4983230072969 + 3 ^ 40 * 1856824 * 2
def baseEnd_1856824 : Nat := 211876267289810755835695

theorem tailTrace_1856824 : CollatzResearch.WordTrace tailWord_1856824 prefixEnd_1856824 211876267289810755835695 := by
  unfold tailWord_1856824
  simp only [CollatzResearch.WordTrace]
  refine ⟨33861967512525621568536763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45149290016700828758049017 33861967512525621568536763)
  ·
    refine ⟨50792951268788432352805145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33861967512525621568536763 50792951268788432352805145)
    ·
      refine ⟨38094713451591324264603859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50792951268788432352805145 38094713451591324264603859)
      ·
        refine ⟨57142070177386986396905789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38094713451591324264603859 57142070177386986396905789)
        ·
          refine ⟨21428276316520119898839671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57142070177386986396905789 21428276316520119898839671)
          ·
            refine ⟨32142414474780179848259507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21428276316520119898839671 32142414474780179848259507)
            ·
              refine ⟨48213621712170269772389261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32142414474780179848259507 48213621712170269772389261)
              ·
                refine ⟨18080108142063851164645973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48213621712170269772389261 18080108142063851164645973)
                ·
                  refine ⟨211876267289810755835695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18080108142063851164645973 211876267289810755835695)
                  ·
                    rfl

theorem cell22_1856824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 8].length) (baseStart_1856824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1856824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1856824 prefixEnd_1856824 := by exact prefixLift 1856824
  have htrace : WordTrace (prefixWord ++ tailWord_1856824) baseStart_1856824 baseEnd_1856824 := by
    simpa [prefixWord, tailWord_1856824, baseEnd_1856824] using wordTrace_append hprefix tailTrace_1856824
  have hstable : (prefixWord ++ tailWord_1856824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856824).length < 2 ^ (prefixWord ++ tailWord_1856824).sum := by decide
  have hdescent : baseEnd_1856824 < baseStart_1856824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856826 : List Nat := [3, 1, 1, 1, 4, 1, 3, 1, 3, 4]
def baseStart_1856826 : Nat := 118140960795 + 1856826 * 2 ^ 59
def prefixEnd_1856826 : Nat := 4983230072969 + 3 ^ 40 * 1856826 * 2
def baseEnd_1856826 : Nat := 635629486510304928957079

theorem tailTrace_1856826 : CollatzResearch.WordTrace tailWord_1856826 prefixEnd_1856826 635629486510304928957079 := by
  unfold tailWord_1856826
  simp only [CollatzResearch.WordTrace]
  refine ⟨16931001992760999369661583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45149338647362664985764221 16931001992760999369661583)
  ·
    refine ⟨25396502989141499054492375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16931001992760999369661583 25396502989141499054492375)
    ·
      refine ⟨38094754483712248581738563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25396502989141499054492375 38094754483712248581738563)
      ·
        refine ⟨57142131725568372872607845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38094754483712248581738563 57142131725568372872607845)
        ·
          refine ⟨10714149698544069913613971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57142131725568372872607845 10714149698544069913613971)
          ·
            refine ⟨16071224547816104870420957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10714149698544069913613971 16071224547816104870420957)
            ·
              refine ⟨6026709205431039326407859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16071224547816104870420957 6026709205431039326407859)
              ·
                refine ⟨9040063808146558989611789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6026709205431039326407859 9040063808146558989611789)
                ·
                  refine ⟨3390023928054959621104421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9040063808146558989611789 3390023928054959621104421)
                  ·
                    refine ⟨635629486510304928957079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3390023928054959621104421 635629486510304928957079)
                    ·
                      rfl

theorem cell22_1856826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_1856826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1856826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1856826 prefixEnd_1856826 := by exact prefixLift 1856826
  have htrace : WordTrace (prefixWord ++ tailWord_1856826) baseStart_1856826 baseEnd_1856826 := by
    simpa [prefixWord, tailWord_1856826, baseEnd_1856826] using wordTrace_append hprefix tailTrace_1856826
  have hstable : (prefixWord ++ tailWord_1856826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856826).length < 2 ^ (prefixWord ++ tailWord_1856826).sum := by decide
  have hdescent : baseEnd_1856826 < baseStart_1856826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856924 : List Nat := [2, 2, 3, 4, 1, 1, 3, 1, 2, 3]
def baseStart_1856924 : Nat := 118140960795 + 1856924 * 2 ^ 59
def prefixEnd_1856924 : Nat := 4983230072969 + 3 ^ 40 * 1856924 * 2
def baseEnd_1856924 : Nat := 635663033913065340006779

theorem tailTrace_1856924 : CollatzResearch.WordTrace tailWord_1856924 prefixEnd_1856924 635663033913065340006779 := by
  unfold tailWord_1856924
  simp only [CollatzResearch.WordTrace]
  refine ⟨33863791162344480107856913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45151721549792640143809217 33863791162344480107856913)
  ·
    refine ⟨25397843371758360080892685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33863791162344480107856913 25397843371758360080892685)
    ·
      refine ⟨9524191264409385030334757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25397843371758360080892685 9524191264409385030334757)
      ·
        refine ⟨1785785862076759693187767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9524191264409385030334757 1785785862076759693187767)
        ·
          refine ⟨2678678793115139539781651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1785785862076759693187767 2678678793115139539781651)
          ·
            refine ⟨4018018189672709309672477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2678678793115139539781651 4018018189672709309672477)
            ·
              refine ⟨1506756821127265991127179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4018018189672709309672477 1506756821127265991127179)
              ·
                refine ⟨2260135231690898986690769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1506756821127265991127179 2260135231690898986690769)
                ·
                  refine ⟨1695101423768174240018077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2260135231690898986690769 1695101423768174240018077)
                  ·
                    refine ⟨635663033913065340006779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1695101423768174240018077 635663033913065340006779)
                    ·
                      rfl

theorem cell22_1856924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_1856924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1856924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1856924 prefixEnd_1856924 := by exact prefixLift 1856924
  have htrace : WordTrace (prefixWord ++ tailWord_1856924) baseStart_1856924 baseEnd_1856924 := by
    simpa [prefixWord, tailWord_1856924, baseEnd_1856924] using wordTrace_append hprefix tailTrace_1856924
  have hstable : (prefixWord ++ tailWord_1856924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856924).length < 2 ^ (prefixWord ++ tailWord_1856924).sum := by decide
  have hdescent : baseEnd_1856924 < baseStart_1856924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856946 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 4, 5]
def baseStart_1856946 : Nat := 118140960795 + 1856946 * 2 ^ 59
def prefixEnd_1856946 : Nat := 4983230072969 + 3 ^ 40 * 1856946 * 2
def baseEnd_1856946 : Nat := 635670564962664615956711

theorem tailTrace_1856946 : CollatzResearch.WordTrace tailWord_1856946 prefixEnd_1856946 635670564962664615956711 := by
  unfold tailWord_1856946
  simp only [CollatzResearch.WordTrace]
  refine ⟨16932096182652314493253673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45152256487072838648676461 16932096182652314493253673)
  ·
    refine ⟨12699072136989235869940255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16932096182652314493253673 12699072136989235869940255)
    ·
      refine ⟨19048608205483853804910383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12699072136989235869940255 19048608205483853804910383)
      ·
        refine ⟨28572912308225780707365575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19048608205483853804910383 28572912308225780707365575)
        ·
          refine ⟨42859368462338671061048363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28572912308225780707365575 42859368462338671061048363)
          ·
            refine ⟨64289052693508006591572545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42859368462338671061048363 64289052693508006591572545)
            ·
              refine ⟨48216789520131004943679409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64289052693508006591572545 48216789520131004943679409)
              ·
                refine ⟨36162592140098253707759557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48216789520131004943679409 36162592140098253707759557)
                ·
                  refine ⟨6780486026268422570204917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36162592140098253707759557 6780486026268422570204917)
                  ·
                    refine ⟨635670564962664615956711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6780486026268422570204917 635670564962664615956711)
                    ·
                      rfl

theorem cell22_1856946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_1856946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1856946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1856946 prefixEnd_1856946 := by exact prefixLift 1856946
  have htrace : WordTrace (prefixWord ++ tailWord_1856946) baseStart_1856946 baseEnd_1856946 := by
    simpa [prefixWord, tailWord_1856946, baseEnd_1856946] using wordTrace_append hprefix tailTrace_1856946
  have hstable : (prefixWord ++ tailWord_1856946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856946).length < 2 ^ (prefixWord ++ tailWord_1856946).sum := by decide
  have hdescent : baseEnd_1856946 < baseStart_1856946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856982 : List Nat := [5, 2, 1, 1, 1, 2, 4, 1, 5]
def baseStart_1856982 : Nat := 118140960795 + 1856982 * 2 ^ 59
def prefixEnd_1856982 : Nat := 4983230072969 + 3 ^ 40 * 1856982 * 2
def baseEnd_1856982 : Nat := 211894296166124174018867

theorem tailTrace_1856982 : CollatzResearch.WordTrace tailWord_1856982 prefixEnd_1856982 211894296166124174018867 := by
  unfold tailWord_1856982
  simp only [CollatzResearch.WordTrace]
  refine ⟨4233106109904927257582825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45153131838985890747550133 4233106109904927257582825)
  ·
    refine ⟨3174829582428695443187119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4233106109904927257582825 3174829582428695443187119)
    ·
      refine ⟨4762244373643043164780679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3174829582428695443187119 4762244373643043164780679)
      ·
        refine ⟨7143366560464564747171019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4762244373643043164780679 7143366560464564747171019)
        ·
          refine ⟨10715049840696847120756529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7143366560464564747171019 10715049840696847120756529)
          ·
            refine ⟨8036287380522635340567397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10715049840696847120756529 8036287380522635340567397)
            ·
              refine ⟨1506803883847994126356387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8036287380522635340567397 1506803883847994126356387)
              ·
                refine ⟨2260205825771991189534581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1506803883847994126356387 2260205825771991189534581)
                ·
                  refine ⟨211894296166124174018867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2260205825771991189534581 211894296166124174018867)
                  ·
                    rfl

theorem cell22_1856982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_1856982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1856982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1856982 prefixEnd_1856982 := by exact prefixLift 1856982
  have htrace : WordTrace (prefixWord ++ tailWord_1856982) baseStart_1856982 baseEnd_1856982 := by
    simpa [prefixWord, tailWord_1856982, baseEnd_1856982] using wordTrace_append hprefix tailTrace_1856982
  have hstable : (prefixWord ++ tailWord_1856982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856982).length < 2 ^ (prefixWord ++ tailWord_1856982).sum := by decide
  have hdescent : baseEnd_1856982 < baseStart_1856982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856995 : List Nat := [1, 1, 1, 6, 2, 1, 3, 2, 1, 4]
def baseStart_1856995 : Nat := 118140960795 + 1856995 * 2 ^ 59
def prefixEnd_1856995 : Nat := 4983230072969 + 3 ^ 40 * 1856995 * 2
def baseEnd_1856995 : Nat := 635687338664044821481561

theorem tailTrace_1856995 : CollatzResearch.WordTrace tailWord_1856995 prefixEnd_1856995 635687338664044821481561 := by
  unfold tailWord_1856995
  simp only [CollatzResearch.WordTrace]
  refine ⟨67730171907431739341548439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45153447938287826227698959 67730171907431739341548439)
  ·
    refine ⟨101595257861147609012322659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67730171907431739341548439 101595257861147609012322659)
    ·
      refine ⟨152392886791721413518483989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101595257861147609012322659 152392886791721413518483989)
      ·
        refine ⟨7143416568361941258678937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 152392886791721413518483989 7143416568361941258678937)
        ·
          refine ⟨5357562426271455944009203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7143416568361941258678937 5357562426271455944009203)
          ·
            refine ⟨8036343639407183916013805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5357562426271455944009203 8036343639407183916013805)
            ·
              refine ⟨3013628864777693968505177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8036343639407183916013805 3013628864777693968505177)
              ·
                refine ⟨2260221648583270476378883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3013628864777693968505177 2260221648583270476378883)
                ·
                  refine ⟨3390332472874905714568325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2260221648583270476378883 3390332472874905714568325)
                  ·
                    refine ⟨635687338664044821481561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3390332472874905714568325 635687338664044821481561)
                    ·
                      rfl

theorem cell22_1856995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 4].length) (baseStart_1856995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1856995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1856995 prefixEnd_1856995 := by exact prefixLift 1856995
  have htrace : WordTrace (prefixWord ++ tailWord_1856995) baseStart_1856995 baseEnd_1856995 := by
    simpa [prefixWord, tailWord_1856995, baseEnd_1856995] using wordTrace_append hprefix tailTrace_1856995
  have hstable : (prefixWord ++ tailWord_1856995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856995).length < 2 ^ (prefixWord ++ tailWord_1856995).sum := by decide
  have hdescent : baseEnd_1856995 < baseStart_1856995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857008 : List Nat := [2, 1, 1, 1, 3, 5, 1, 2, 1, 5]
def baseStart_1857008 : Nat := 118140960795 + 1857008 * 2 ^ 59
def prefixEnd_1857008 : Nat := 4983230072969 + 3 ^ 40 * 1857008 * 2
def baseEnd_1857008 : Nat := 635691788829717120906521

theorem tailTrace_1857008 : CollatzResearch.WordTrace tailWord_1857008 prefixEnd_1857008 635691788829717120906521 := by
  unfold tailWord_1857008
  simp only [CollatzResearch.WordTrace]
  refine ⟨33865323028192321280885839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45153764037589761707847785 33865323028192321280885839)
  ·
    refine ⟨50797984542288481921328759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33865323028192321280885839 50797984542288481921328759)
    ·
      refine ⟨76196976813432722881993139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50797984542288481921328759 76196976813432722881993139)
      ·
        refine ⟨114295465220149084322989709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76196976813432722881993139 114295465220149084322989709)
        ·
          refine ⟨42860799457555906621121141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114295465220149084322989709 42860799457555906621121141)
          ·
            refine ⟨4018199949145866245730107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42860799457555906621121141 4018199949145866245730107)
            ·
              refine ⟨6027299923718799368595161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4018199949145866245730107 6027299923718799368595161)
              ·
                refine ⟨4520474942789099526446371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6027299923718799368595161 4520474942789099526446371)
                ·
                  refine ⟨6780712414183649289669557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4520474942789099526446371 6780712414183649289669557)
                  ·
                    refine ⟨635691788829717120906521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6780712414183649289669557 635691788829717120906521)
                    ·
                      rfl

theorem cell22_1857008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 1, 5].length) (baseStart_1857008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1857008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1857008 prefixEnd_1857008 := by exact prefixLift 1857008
  have htrace : WordTrace (prefixWord ++ tailWord_1857008) baseStart_1857008 baseEnd_1857008 := by
    simpa [prefixWord, tailWord_1857008, baseEnd_1857008] using wordTrace_append hprefix tailTrace_1857008
  have hstable : (prefixWord ++ tailWord_1857008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857008).length < 2 ^ (prefixWord ++ tailWord_1857008).sum := by decide
  have hdescent : baseEnd_1857008 < baseStart_1857008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857021 : List Nat := [1, 4, 1, 1, 1, 14]
def baseStart_1857021 : Nat := 118140960795 + 1857021 * 2 ^ 59
def prefixEnd_1857021 : Nat := 4983230072969 + 3 ^ 40 * 1857021 * 2
def baseEnd_1857021 : Nat := 7848101715992461979401

theorem tailTrace_1857021 : CollatzResearch.WordTrace tailWord_1857021 prefixEnd_1857021 7848101715992461979401 := by
  unfold tailWord_1857021
  simp only [CollatzResearch.WordTrace]
  refine ⟨67731120205337545781994917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45154080136891697187996611 67731120205337545781994917)
  ·
    refine ⟨12699585038500789834124047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67731120205337545781994917 12699585038500789834124047)
    ·
      refine ⟨19049377557751184751186071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12699585038500789834124047 19049377557751184751186071)
      ·
        refine ⟨28574066336626777126779107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19049377557751184751186071 28574066336626777126779107)
        ·
          refine ⟨42861099504940165690168661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28574066336626777126779107 42861099504940165690168661)
          ·
            refine ⟨7848101715992461979401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 42861099504940165690168661 7848101715992461979401)
            ·
              rfl

theorem cell22_1857021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 14].length) (baseStart_1857021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1857021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1857021 prefixEnd_1857021 := by exact prefixLift 1857021
  have htrace : WordTrace (prefixWord ++ tailWord_1857021) baseStart_1857021 baseEnd_1857021 := by
    simpa [prefixWord, tailWord_1857021, baseEnd_1857021] using wordTrace_append hprefix tailTrace_1857021
  have hstable : (prefixWord ++ tailWord_1857021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857021).length < 2 ^ (prefixWord ++ tailWord_1857021).sum := by decide
  have hdescent : baseEnd_1857021 < baseStart_1857021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857087 : List Nat := [1, 1, 2, 2, 3, 3, 2, 4, 1, 3]
def baseStart_1857087 : Nat := 118140960795 + 1857087 * 2 ^ 59
def prefixEnd_1857087 : Nat := 4983230072969 + 3 ^ 40 * 1857087 * 2
def baseEnd_1857087 : Nat := 635718832144187248181279

theorem tailTrace_1857087 : CollatzResearch.WordTrace tailWord_1857087 prefixEnd_1857087 635718832144187248181279 := by
  unfold tailWord_1857087
  simp only [CollatzResearch.WordTrace]
  refine ⟨67733527423098439053897515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45155684948732292702598343 67733527423098439053897515)
  ·
    refine ⟨101600291134647658580846273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67733527423098439053897515 101600291134647658580846273)
    ·
      refine ⟨76200218350985743935634705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101600291134647658580846273 76200218350985743935634705)
      ·
        refine ⟨57150163763239307951726029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76200218350985743935634705 57150163763239307951726029)
        ·
          refine ⟨21431311411214740481897261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57150163763239307951726029 21431311411214740481897261)
          ·
            refine ⟨8036741779205527680711473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21431311411214740481897261 8036741779205527680711473)
            ·
              refine ⟨6027556334404145760533605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8036741779205527680711473 6027556334404145760533605)
              ·
                refine ⟨1130166812700777330100051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6027556334404145760533605 1130166812700777330100051)
                ·
                  refine ⟨1695250219051165995150077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1130166812700777330100051 1695250219051165995150077)
                  ·
                    refine ⟨635718832144187248181279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1695250219051165995150077 635718832144187248181279)
                    ·
                      rfl

theorem cell22_1857087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 4, 1, 3].length) (baseStart_1857087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1857087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1857087 prefixEnd_1857087 := by exact prefixLift 1857087
  have htrace : WordTrace (prefixWord ++ tailWord_1857087) baseStart_1857087 baseEnd_1857087 := by
    simpa [prefixWord, tailWord_1857087, baseEnd_1857087] using wordTrace_append hprefix tailTrace_1857087
  have hstable : (prefixWord ++ tailWord_1857087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857087).length < 2 ^ (prefixWord ++ tailWord_1857087).sum := by decide
  have hdescent : baseEnd_1857087 < baseStart_1857087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857098 : List Nat := [3, 1, 2, 1, 1, 3, 1, 3, 2, 5]
def baseStart_1857098 : Nat := 118140960795 + 1857098 * 2 ^ 59
def prefixEnd_1857098 : Nat := 4983230072969 + 3 ^ 40 * 1857098 * 2
def baseEnd_1857098 : Nat := 635722597668986886156245

theorem tailTrace_1857098 : CollatzResearch.WordTrace tailWord_1857098 prefixEnd_1857098 635722597668986886156245 := by
  unfold tailWord_1857098
  simp only [CollatzResearch.WordTrace]
  refine ⟨16933482156514646983136987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45155952417372391955031965 16933482156514646983136987)
  ·
    refine ⟨25400223234771970474705481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16933482156514646983136987 25400223234771970474705481)
    ·
      refine ⟨19050167426078977856029111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25400223234771970474705481 19050167426078977856029111)
      ·
        refine ⟨28575251139118466784043667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19050167426078977856029111 28575251139118466784043667)
        ·
          refine ⟨42862876708677700176065501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28575251139118466784043667 42862876708677700176065501)
          ·
            refine ⟨16073578765754137566024563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42862876708677700176065501 16073578765754137566024563)
            ·
              refine ⟨24110368148631206349036845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16073578765754137566024563 24110368148631206349036845)
              ·
                refine ⟨9041388055736702380888817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24110368148631206349036845 9041388055736702380888817)
                ·
                  refine ⟨6781041041802526785666613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9041388055736702380888817 6781041041802526785666613)
                  ·
                    refine ⟨635722597668986886156245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6781041041802526785666613 635722597668986886156245)
                    ·
                      rfl

theorem cell22_1857098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_1857098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1857098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1857098 prefixEnd_1857098 := by exact prefixLift 1857098
  have htrace : WordTrace (prefixWord ++ tailWord_1857098) baseStart_1857098 baseEnd_1857098 := by
    simpa [prefixWord, tailWord_1857098, baseEnd_1857098] using wordTrace_append hprefix tailTrace_1857098
  have hstable : (prefixWord ++ tailWord_1857098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857098).length < 2 ^ (prefixWord ++ tailWord_1857098).sum := by decide
  have hdescent : baseEnd_1857098 < baseStart_1857098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857113 : List Nat := [1, 2, 1, 2, 2, 1, 1, 5, 3, 4]
def baseStart_1857113 : Nat := 118140960795 + 1857113 * 2 ^ 59
def prefixEnd_1857113 : Nat := 4983230072969 + 3 ^ 40 * 1857113 * 2
def baseEnd_1857113 : Nat := 635727732475531847031199

theorem tailTrace_1857113 : CollatzResearch.WordTrace tailWord_1857113 prefixEnd_1857113 635727732475531847031199 := by
  unfold tailWord_1857113
  simp only [CollatzResearch.WordTrace]
  refine ⟨67734475721004245494343993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45156317147336163662895995 67734475721004245494343993)
  ·
    refine ⟨50800856790753184120757995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67734475721004245494343993 50800856790753184120757995)
    ·
      refine ⟨76201285186129776181136993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50800856790753184120757995 76201285186129776181136993)
      ·
        refine ⟨57150963889597332135852745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76201285186129776181136993 57150963889597332135852745)
        ·
          refine ⟨42863222917197999101889559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57150963889597332135852745 42863222917197999101889559)
          ·
            refine ⟨64294834375796998652834339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42863222917197999101889559 64294834375796998652834339)
            ·
              refine ⟨96442251563695497979251509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64294834375796998652834339 96442251563695497979251509)
              ·
                refine ⟨9041461084096452935554829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96442251563695497979251509 9041461084096452935554829)
                ·
                  refine ⟨3390547906536169850833061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9041461084096452935554829 3390547906536169850833061)
                  ·
                    refine ⟨635727732475531847031199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3390547906536169850833061 635727732475531847031199)
                    ·
                      rfl

theorem cell22_1857113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 4].length) (baseStart_1857113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1857113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1857113 prefixEnd_1857113 := by exact prefixLift 1857113
  have htrace : WordTrace (prefixWord ++ tailWord_1857113) baseStart_1857113 baseEnd_1857113 := by
    simpa [prefixWord, tailWord_1857113, baseEnd_1857113] using wordTrace_append hprefix tailTrace_1857113
  have hstable : (prefixWord ++ tailWord_1857113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857113).length < 2 ^ (prefixWord ++ tailWord_1857113).sum := by decide
  have hdescent : baseEnd_1857113 < baseStart_1857113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857175 : List Nat := [1, 1, 3, 3, 2, 2, 1, 3, 2, 4]
def baseStart_1857175 : Nat := 118140960795 + 1857175 * 2 ^ 59
def prefixEnd_1857175 : Nat := 4983230072969 + 3 ^ 40 * 1857175 * 2
def baseEnd_1857175 : Nat := 635748956342584351981009

theorem tailTrace_1857175 : CollatzResearch.WordTrace tailWord_1857175 prefixEnd_1857175 635748956342584351981009 := by
  unfold tailWord_1857175
  simp only [CollatzResearch.WordTrace]
  refine ⟨67736737046779630083100979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45157824697853086722067319 67736737046779630083100979)
  ·
    refine ⟨101605105570169445124651469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67736737046779630083100979 101605105570169445124651469)
    ·
      refine ⟨38101914588813541921744301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101605105570169445124651469 38101914588813541921744301)
      ·
        refine ⟨14288217970805078220654113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38101914588813541921744301 14288217970805078220654113)
        ·
          refine ⟨10716163478103808665490585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14288217970805078220654113 10716163478103808665490585)
          ·
            refine ⟨8037122608577856499117939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10716163478103808665490585 8037122608577856499117939)
            ·
              refine ⟨12055683912866784748676909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8037122608577856499117939 12055683912866784748676909)
              ·
                refine ⟨4520881467325044280753841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12055683912866784748676909 4520881467325044280753841)
                ·
                  refine ⟨3390661100493783210565381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4520881467325044280753841 3390661100493783210565381)
                  ·
                    refine ⟨635748956342584351981009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3390661100493783210565381 635748956342584351981009)
                    ·
                      rfl

theorem cell22_1857175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_1857175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1857175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1857175 prefixEnd_1857175 := by exact prefixLift 1857175
  have htrace : WordTrace (prefixWord ++ tailWord_1857175) baseStart_1857175 baseEnd_1857175 := by
    simpa [prefixWord, tailWord_1857175, baseEnd_1857175] using wordTrace_append hprefix tailTrace_1857175
  have hstable : (prefixWord ++ tailWord_1857175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857175).length < 2 ^ (prefixWord ++ tailWord_1857175).sum := by decide
  have hdescent : baseEnd_1857175 < baseStart_1857175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857203 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 1, 8]
def baseStart_1857203 : Nat := 118140960795 + 1857203 * 2 ^ 59
def prefixEnd_1857203 : Nat := 4983230072969 + 3 ^ 40 * 1857203 * 2
def baseEnd_1857203 : Nat := 635758541314801612280923

theorem tailTrace_1857203 : CollatzResearch.WordTrace tailWord_1857203 prefixEnd_1857203 635758541314801612280923 := by
  unfold tailWord_1857203
  simp only [CollatzResearch.WordTrace]
  refine ⟨67737758290678190865120263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45158505527118793910080175 67737758290678190865120263)
  ·
    refine ⟨101606637436017286297680395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67737758290678190865120263 101606637436017286297680395)
    ·
      refine ⟨152409956154025929446520593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101606637436017286297680395 152409956154025929446520593)
      ·
        refine ⟨114307467115519447084890445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152409956154025929446520593 114307467115519447084890445)
        ·
          refine ⟨42865300168319792656833917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114307467115519447084890445 42865300168319792656833917)
          ·
            refine ⟨16074487563119922246312719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42865300168319792656833917 16074487563119922246312719)
            ·
              refine ⟨24111731344679883369469079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16074487563119922246312719 24111731344679883369469079)
              ·
                refine ⟨36167597017019825054203619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24111731344679883369469079 36167597017019825054203619)
                ·
                  refine ⟨54251395525529737581305429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36167597017019825054203619 54251395525529737581305429)
                  ·
                    refine ⟨635758541314801612280923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54251395525529737581305429 635758541314801612280923)
                    ·
                      rfl

theorem cell22_1857203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 8].length) (baseStart_1857203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1857203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1857203 prefixEnd_1857203 := by exact prefixLift 1857203
  have htrace : WordTrace (prefixWord ++ tailWord_1857203) baseStart_1857203 baseEnd_1857203 := by
    simpa [prefixWord, tailWord_1857203, baseEnd_1857203] using wordTrace_append hprefix tailTrace_1857203
  have hstable : (prefixWord ++ tailWord_1857203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857203).length < 2 ^ (prefixWord ++ tailWord_1857203).sum := by decide
  have hdescent : baseEnd_1857203 < baseStart_1857203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857220 : List Nat := [2, 3, 3, 1, 1, 1, 1, 2, 2, 6]
def baseStart_1857220 : Nat := 118140960795 + 1857220 * 2 ^ 59
def prefixEnd_1857220 : Nat := 4983230072969 + 3 ^ 40 * 1857220 * 2
def baseEnd_1857220 : Nat := 635764360762219234605871

theorem tailTrace_1857220 : CollatzResearch.WordTrace tailWord_1857220 prefixEnd_1857220 635764360762219234605871 := by
  unfold tailWord_1857220
  simp only [CollatzResearch.WordTrace]
  refine ⟨33869189165808301384244557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45158918887744401845659409 33869189165808301384244557)
  ·
    refine ⟨12700945937178113019091709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33869189165808301384244557 12700945937178113019091709)
    ·
      refine ⟨4762854726441792382159391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12700945937178113019091709 4762854726441792382159391)
      ·
        refine ⟨7144282089662688573239087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4762854726441792382159391 7144282089662688573239087)
        ·
          refine ⟨10716423134494032859858631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7144282089662688573239087 10716423134494032859858631)
          ·
            refine ⟨16074634701741049289787947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10716423134494032859858631 16074634701741049289787947)
            ·
              refine ⟨24111952052611573934681921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16074634701741049289787947 24111952052611573934681921)
              ·
                refine ⟨18083964039458680451011441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24111952052611573934681921 18083964039458680451011441)
                ·
                  refine ⟨13562973029594010338258581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18083964039458680451011441 13562973029594010338258581)
                  ·
                    refine ⟨635764360762219234605871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13562973029594010338258581 635764360762219234605871)
                    ·
                      rfl

theorem cell22_1857220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_1857220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1857220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1857220 prefixEnd_1857220 := by exact prefixLift 1857220
  have htrace : WordTrace (prefixWord ++ tailWord_1857220) baseStart_1857220 baseEnd_1857220 := by
    simpa [prefixWord, tailWord_1857220, baseEnd_1857220] using wordTrace_append hprefix tailTrace_1857220
  have hstable : (prefixWord ++ tailWord_1857220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857220).length < 2 ^ (prefixWord ++ tailWord_1857220).sum := by decide
  have hdescent : baseEnd_1857220 < baseStart_1857220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857239 : List Nat := [1, 1, 3, 2, 1, 3, 4, 3, 1, 3]
def baseStart_1857239 : Nat := 118140960795 + 1857239 * 2 ^ 59
def prefixEnd_1857239 : Nat := 4983230072969 + 3 ^ 40 * 1857239 * 2
def baseEnd_1857239 : Nat := 635770864850509518380813

theorem tailTrace_1857239 : CollatzResearch.WordTrace tailWord_1857239 prefixEnd_1857239 635770864850509518380813 := by
  unfold tailWord_1857239
  simp only [CollatzResearch.WordTrace]
  refine ⟨67739071318547769013430771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45159380879031846008953847 67739071318547769013430771)
  ·
    refine ⟨101608606977821653520146157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67739071318547769013430771 101608606977821653520146157)
    ·
      refine ⟨38103227616683120070054809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101608606977821653520146157 38103227616683120070054809)
      ·
        refine ⟨28577420712512340052541107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38103227616683120070054809 28577420712512340052541107)
        ·
          refine ⟨42866131068768510078811661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28577420712512340052541107 42866131068768510078811661)
          ·
            refine ⟨16074799150788191279554373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42866131068768510078811661 16074799150788191279554373)
            ·
              refine ⟨3014024840772785864916445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16074799150788191279554373 3014024840772785864916445)
              ·
                refine ⟨1130259315289794699343667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3014024840772785864916445 1130259315289794699343667)
                ·
                  refine ⟨1695388972934692049015501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1130259315289794699343667 1695388972934692049015501)
                  ·
                    refine ⟨635770864850509518380813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1695388972934692049015501 635770864850509518380813)
                    ·
                      rfl

theorem cell22_1857239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 3, 1, 3].length) (baseStart_1857239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1857239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1857239 prefixEnd_1857239 := by exact prefixLift 1857239
  have htrace : WordTrace (prefixWord ++ tailWord_1857239) baseStart_1857239 baseEnd_1857239 := by
    simpa [prefixWord, tailWord_1857239, baseEnd_1857239] using wordTrace_append hprefix tailTrace_1857239
  have hstable : (prefixWord ++ tailWord_1857239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857239).length < 2 ^ (prefixWord ++ tailWord_1857239).sum := by decide
  have hdescent : baseEnd_1857239 < baseStart_1857239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857312 : List Nat := [2, 1, 1, 5, 1, 1, 1, 3, 4, 3]
def baseStart_1857312 : Nat := 118140960795 + 1857312 * 2 ^ 59
def prefixEnd_1857312 : Nat := 4983230072969 + 3 ^ 40 * 1857312 * 2
def baseEnd_1857312 : Nat := 635795854242361661305589

theorem tailTrace_1857312 : CollatzResearch.WordTrace tailWord_1857312 prefixEnd_1857312 635795854242361661305589 := by
  unfold tailWord_1857312
  simp only [CollatzResearch.WordTrace]
  refine ⟨33870866923641651240419095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45161155898188868320558793 33870866923641651240419095)
  ·
    refine ⟨50806300385462476860628643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33870866923641651240419095 50806300385462476860628643)
    ·
      refine ⟨76209450578193715290942965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50806300385462476860628643 76209450578193715290942965)
      ·
        refine ⟨7144635991705660808525903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76209450578193715290942965 7144635991705660808525903)
        ·
          refine ⟨10716953987558491212788855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7144635991705660808525903 10716953987558491212788855)
          ·
            refine ⟨16075430981337736819183283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10716953987558491212788855 16075430981337736819183283)
            ·
              refine ⟨24113146472006605228774925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16075430981337736819183283 24113146472006605228774925)
              ·
                refine ⟨9042429927002476960790597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24113146472006605228774925 9042429927002476960790597)
                ·
                  refine ⟨1695455611312964430148237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9042429927002476960790597 1695455611312964430148237)
                  ·
                    refine ⟨635795854242361661305589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1695455611312964430148237 635795854242361661305589)
                    ·
                      rfl

theorem cell22_1857312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 4, 3].length) (baseStart_1857312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1857312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1857312 prefixEnd_1857312 := by exact prefixLift 1857312
  have htrace : WordTrace (prefixWord ++ tailWord_1857312) baseStart_1857312 baseEnd_1857312 := by
    simpa [prefixWord, tailWord_1857312, baseEnd_1857312] using wordTrace_append hprefix tailTrace_1857312
  have hstable : (prefixWord ++ tailWord_1857312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857312).length < 2 ^ (prefixWord ++ tailWord_1857312).sum := by decide
  have hdescent : baseEnd_1857312 < baseStart_1857312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857329 : List Nat := [1, 2, 2, 3, 2, 3, 1, 3, 2, 3]
def baseStart_1857329 : Nat := 118140960795 + 1857329 * 2 ^ 59
def prefixEnd_1857329 : Nat := 4983230072969 + 3 ^ 40 * 1857329 * 2
def baseEnd_1857329 : Nat := 635801673689779283630537

theorem tailTrace_1857329 : CollatzResearch.WordTrace tailWord_1857329 prefixEnd_1857329 635801673689779283630537 := by
  unfold tailWord_1857329
  simp only [CollatzResearch.WordTrace]
  refine ⟨67742353888221714384207041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45161569258814476256138027 67742353888221714384207041)
  ·
    refine ⟨50806765416166285788155281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67742353888221714384207041 50806765416166285788155281)
    ·
      refine ⟨38105074062124714341116461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50806765416166285788155281 38105074062124714341116461)
      ·
        refine ⟨14289402773296767877918673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38105074062124714341116461 14289402773296767877918673)
        ·
          refine ⟨10717052079972575908439005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14289402773296767877918673 10717052079972575908439005)
          ·
            refine ⟨4018894529989715965664627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10717052079972575908439005 4018894529989715965664627)
            ·
              refine ⟨6028341794984573948496941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4018894529989715965664627 6028341794984573948496941)
              ·
                refine ⟨2260628173119215230686353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6028341794984573948496941 2260628173119215230686353)
                ·
                  refine ⟨1695471129839411423014765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2260628173119215230686353 1695471129839411423014765)
                  ·
                    refine ⟨635801673689779283630537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1695471129839411423014765 635801673689779283630537)
                    ·
                      rfl

theorem cell22_1857329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 2, 3].length) (baseStart_1857329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1857329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1857329 prefixEnd_1857329 := by exact prefixLift 1857329
  have htrace : WordTrace (prefixWord ++ tailWord_1857329) baseStart_1857329 baseEnd_1857329 := by
    simpa [prefixWord, tailWord_1857329, baseEnd_1857329] using wordTrace_append hprefix tailTrace_1857329
  have hstable : (prefixWord ++ tailWord_1857329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857329).length < 2 ^ (prefixWord ++ tailWord_1857329).sum := by decide
  have hdescent : baseEnd_1857329 < baseStart_1857329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857340 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 2, 7]
def baseStart_1857340 : Nat := 118140960795 + 1857340 * 2 ^ 59
def prefixEnd_1857340 : Nat := 4983230072969 + 3 ^ 40 * 1857340 * 2
def baseEnd_1857340 : Nat := 635805439214578921605503

theorem tailTrace_1857340 : CollatzResearch.WordTrace tailWord_1857340 prefixEnd_1857340 635805439214578921605503 := by
  unfold tailWord_1857340
  simp only [CollatzResearch.WordTrace]
  refine ⟨33871377545590931631428737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45161836727454575508571649 33871377545590931631428737)
  ·
    refine ⟨25403533159193198723571553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33871377545590931631428737 25403533159193198723571553)
    ·
      refine ⟨19052649869394899042678665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25403533159193198723571553 19052649869394899042678665)
      ·
        refine ⟨14289487402046174282008999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19052649869394899042678665 14289487402046174282008999)
        ·
          refine ⟨21434231103069261423013499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14289487402046174282008999 21434231103069261423013499)
          ·
            refine ⟨32151346654603892134520249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21434231103069261423013499 32151346654603892134520249)
            ·
              refine ⟨24113509990952919100890187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32151346654603892134520249 24113509990952919100890187)
              ·
                refine ⟨36170264986429378651335281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24113509990952919100890187 36170264986429378651335281)
                ·
                  refine ⟨27127698739822033988501461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36170264986429378651335281 27127698739822033988501461)
                  ·
                    refine ⟨635805439214578921605503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27127698739822033988501461 635805439214578921605503)
                    ·
                      rfl

theorem cell22_1857340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_1857340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1857340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1857340 prefixEnd_1857340 := by exact prefixLift 1857340
  have htrace : WordTrace (prefixWord ++ tailWord_1857340) baseStart_1857340 baseEnd_1857340 := by
    simpa [prefixWord, tailWord_1857340, baseEnd_1857340] using wordTrace_append hprefix tailTrace_1857340
  have hstable : (prefixWord ++ tailWord_1857340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857340).length < 2 ^ (prefixWord ++ tailWord_1857340).sum := by decide
  have hdescent : baseEnd_1857340 < baseStart_1857340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857342 : List Nat := [4, 2, 1, 2, 2, 1, 2, 8]
def baseStart_1857342 : Nat := 118140960795 + 1857342 * 2 ^ 59
def prefixEnd_1857342 : Nat := 4983230072969 + 3 ^ 40 * 1857342 * 2
def baseEnd_1857342 : Nat := 70645124872827953672833

theorem tailTrace_1857342 : CollatzResearch.WordTrace tailWord_1857342 prefixEnd_1857342 70645124872827953672833 := by
  unfold tailWord_1857342
  simp only [CollatzResearch.WordTrace]
  refine ⟨8467853504646827200553785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45161885358116411736286853 8467853504646827200553785)
  ·
    refine ⟨6350890128485120400415339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8467853504646827200553785 6350890128485120400415339)
    ·
      refine ⟨9526335192727680600623009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6350890128485120400415339 9526335192727680600623009)
      ·
        refine ⟨7144751394545760450467257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9526335192727680600623009 7144751394545760450467257)
        ·
          refine ⟨5358563545909320337850443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7144751394545760450467257 5358563545909320337850443)
          ·
            refine ⟨8037845318863980506775665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5358563545909320337850443 8037845318863980506775665)
            ·
              refine ⟨6028383989147985380081749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8037845318863980506775665 6028383989147985380081749)
              ·
                refine ⟨70645124872827953672833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6028383989147985380081749 70645124872827953672833)
                ·
                  rfl

theorem cell22_1857342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 8].length) (baseStart_1857342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1857342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1857342 prefixEnd_1857342 := by exact prefixLift 1857342
  have htrace : WordTrace (prefixWord ++ tailWord_1857342) baseStart_1857342 baseEnd_1857342 := by
    simpa [prefixWord, tailWord_1857342, baseEnd_1857342] using wordTrace_append hprefix tailTrace_1857342
  have hstable : (prefixWord ++ tailWord_1857342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857342).length < 2 ^ (prefixWord ++ tailWord_1857342).sum := by decide
  have hdescent : baseEnd_1857342 < baseStart_1857342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857543 : List Nat := [1, 1, 4, 3, 1, 3, 1, 4, 1, 3]
def baseStart_1857543 : Nat := 118140960795 + 1857543 * 2 ^ 59
def prefixEnd_1857543 : Nat := 4983230072969 + 3 ^ 40 * 1857543 * 2
def baseEnd_1857543 : Nat := 635874930263154058779881

theorem tailTrace_1857543 : CollatzResearch.WordTrace tailWord_1857543 prefixEnd_1857543 635874930263154058779881 := by
  unfold tailWord_1857543
  simp only [CollatzResearch.WordTrace]
  refine ⟨67750159109446428932497283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45166772739630952621664855 67750159109446428932497283)
  ·
    refine ⟨101625238664169643398745925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67750159109446428932497283 101625238664169643398745925)
    ·
      refine ⟨19054732249531808137264861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101625238664169643398745925 19054732249531808137264861)
      ·
        refine ⟨7145524593574428051474323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19054732249531808137264861 7145524593574428051474323)
        ·
          refine ⟨10718286890361642077211485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7145524593574428051474323 10718286890361642077211485)
          ·
            refine ⟨4019357583885615778954307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10718286890361642077211485 4019357583885615778954307)
            ·
              refine ⟨6029036375828423668431461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4019357583885615778954307 6029036375828423668431461)
              ·
                refine ⟨1130444320467829437830899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6029036375828423668431461 1130444320467829437830899)
                ·
                  refine ⟨1695666480701744156746349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1130444320467829437830899 1695666480701744156746349)
                  ·
                    refine ⟨635874930263154058779881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1695666480701744156746349 635874930263154058779881)
                    ·
                      rfl

theorem cell22_1857543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 4, 1, 3].length) (baseStart_1857543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1857543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1857543 prefixEnd_1857543 := by exact prefixLift 1857543
  have htrace : WordTrace (prefixWord ++ tailWord_1857543) baseStart_1857543 baseEnd_1857543 := by
    simpa [prefixWord, tailWord_1857543, baseEnd_1857543] using wordTrace_append hprefix tailTrace_1857543
  have hstable : (prefixWord ++ tailWord_1857543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857543).length < 2 ^ (prefixWord ++ tailWord_1857543).sum := by decide
  have hdescent : baseEnd_1857543 < baseStart_1857543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857586 : List Nat := [3, 2, 1, 1, 2, 4, 1, 3, 1, 4]
def baseStart_1857586 : Nat := 118140960795 + 1857586 * 2 ^ 59
def prefixEnd_1857586 : Nat := 4983230072969 + 3 ^ 40 * 1857586 * 2
def baseEnd_1857586 : Nat := 635889650041916279954749

theorem tailTrace_1857586 : CollatzResearch.WordTrace tailWord_1857586 prefixEnd_1857586 635889650041916279954749 := by
  unfold tailWord_1857586
  simp only [CollatzResearch.WordTrace]
  refine ⟨16937931862072661819078153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45167818298860431517541741 16937931862072661819078153)
  ·
    refine ⟨12703448896554496364308615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16937931862072661819078153 12703448896554496364308615)
    ·
      refine ⟨19055173344831744546462923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12703448896554496364308615 19055173344831744546462923)
      ·
        refine ⟨28582760017247616819694385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19055173344831744546462923 28582760017247616819694385)
        ·
          refine ⟨21437070012935712614770789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28582760017247616819694385 21437070012935712614770789)
          ·
            refine ⟨4019450627425446115269523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21437070012935712614770789 4019450627425446115269523)
            ·
              refine ⟨6029175941138169172904285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4019450627425446115269523 6029175941138169172904285)
              ·
                refine ⟨2260940977926813439839107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6029175941138169172904285 2260940977926813439839107)
                ·
                  refine ⟨3391411466890220159758661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2260940977926813439839107 3391411466890220159758661)
                  ·
                    refine ⟨635889650041916279954749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3391411466890220159758661 635889650041916279954749)
                    ·
                      rfl

theorem cell22_1857586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_1857586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1857586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1857586 prefixEnd_1857586 := by exact prefixLift 1857586
  have htrace : WordTrace (prefixWord ++ tailWord_1857586) baseStart_1857586 baseEnd_1857586 := by
    simpa [prefixWord, tailWord_1857586, baseEnd_1857586] using wordTrace_append hprefix tailTrace_1857586
  have hstable : (prefixWord ++ tailWord_1857586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857586).length < 2 ^ (prefixWord ++ tailWord_1857586).sum := by decide
  have hdescent : baseEnd_1857586 < baseStart_1857586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857601 : List Nat := [1, 2, 5, 1, 2, 2, 2, 1, 6]
def baseStart_1857601 : Nat := 118140960795 + 1857601 * 2 ^ 59
def prefixEnd_1857601 : Nat := 4983230072969 + 3 ^ 40 * 1857601 * 2
def baseEnd_1857601 : Nat := 211964928282820413609901

theorem tailTrace_1857601 : CollatzResearch.WordTrace tailWord_1857601 prefixEnd_1857601 211964928282820413609901 := by
  unfold tailWord_1857601
  simp only [CollatzResearch.WordTrace]
  refine ⟨67752274543236304838108657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45168183028824203225405771 67752274543236304838108657)
  ·
    refine ⟨50814205907427228628581493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67752274543236304838108657 50814205907427228628581493)
    ·
      refine ⟨4763831803821302683929515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50814205907427228628581493 4763831803821302683929515)
      ·
        refine ⟨7145747705731954025894273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4763831803821302683929515 7145747705731954025894273)
        ·
          refine ⟨5359310779298965519420705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7145747705731954025894273 5359310779298965519420705)
          ·
            refine ⟨4019483084474224139565529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5359310779298965519420705 4019483084474224139565529)
            ·
              refine ⟨3014612313355668104674147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4019483084474224139565529 3014612313355668104674147)
              ·
                refine ⟨4521918470033502157011221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3014612313355668104674147 4521918470033502157011221)
                ·
                  refine ⟨211964928282820413609901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4521918470033502157011221 211964928282820413609901)
                  ·
                    rfl

theorem cell22_1857601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 6].length) (baseStart_1857601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1857601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1857601 prefixEnd_1857601 := by exact prefixLift 1857601
  have htrace : WordTrace (prefixWord ++ tailWord_1857601) baseStart_1857601 baseEnd_1857601 := by
    simpa [prefixWord, tailWord_1857601, baseEnd_1857601] using wordTrace_append hprefix tailTrace_1857601
  have hstable : (prefixWord ++ tailWord_1857601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857601).length < 2 ^ (prefixWord ++ tailWord_1857601).sum := by decide
  have hdescent : baseEnd_1857601 < baseStart_1857601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857614 : List Nat := [4, 1, 1, 1, 1, 4, 1, 2, 1, 6]
def baseStart_1857614 : Nat := 118140960795 + 1857614 * 2 ^ 59
def prefixEnd_1857614 : Nat := 4983230072969 + 3 ^ 40 * 1857614 * 2
def baseEnd_1857614 : Nat := 635899235014133540254663

theorem tailTrace_1857614 : CollatzResearch.WordTrace tailWord_1857614 prefixEnd_1857614 635899235014133540254663 := by
  unfold tailWord_1857614
  simp only [CollatzResearch.WordTrace]
  refine ⟨8469093586523651007291487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45168499128126138705554597 8469093586523651007291487)
  ·
    refine ⟨12703640379785476510937231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8469093586523651007291487 12703640379785476510937231)
    ·
      refine ⟨19055460569678214766405847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12703640379785476510937231 19055460569678214766405847)
      ·
        refine ⟨28583190854517322149608771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19055460569678214766405847 28583190854517322149608771)
        ·
          refine ⟨42874786281775983224413157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28583190854517322149608771 42874786281775983224413157)
          ·
            refine ⟨8039022427832996854577467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42874786281775983224413157 8039022427832996854577467)
            ·
              refine ⟨12058533641749495281866201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8039022427832996854577467 12058533641749495281866201)
              ·
                refine ⟨9043900231312121461399651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12058533641749495281866201 9043900231312121461399651)
                ·
                  refine ⟨13565850346968182192099477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9043900231312121461399651 13565850346968182192099477)
                  ·
                    refine ⟨635899235014133540254663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13565850346968182192099477 635899235014133540254663)
                    ·
                      rfl

theorem cell22_1857614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_1857614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1857614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1857614 prefixEnd_1857614 := by exact prefixLift 1857614
  have htrace : WordTrace (prefixWord ++ tailWord_1857614) baseStart_1857614 baseEnd_1857614 := by
    simpa [prefixWord, tailWord_1857614, baseEnd_1857614] using wordTrace_append hprefix tailTrace_1857614
  have hstable : (prefixWord ++ tailWord_1857614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857614).length < 2 ^ (prefixWord ++ tailWord_1857614).sum := by decide
  have hdescent : baseEnd_1857614 < baseStart_1857614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857751 : List Nat := [1, 1, 3, 2, 1, 2, 1, 4, 4, 3]
def baseStart_1857751 : Nat := 118140960795 + 1857751 * 2 ^ 59
def prefixEnd_1857751 : Nat := 4983230072969 + 3 ^ 40 * 1857751 * 2
def baseEnd_1857751 : Nat := 635946132913910849579243

theorem tailTrace_1857751 : CollatzResearch.WordTrace tailWord_1857751 prefixEnd_1857751 635946132913910849579243 := by
  unfold tailWord_1857751
  simp only [CollatzResearch.WordTrace]
  refine ⟨67757745492692880456069107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45171830328461920304046071 67757745492692880456069107)
  ·
    refine ⟨101636618239039320684103661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67757745492692880456069107 101636618239039320684103661)
    ·
      refine ⟨38113731839639745256538873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101636618239039320684103661 38113731839639745256538873)
      ·
        refine ⟨28585298879729808942404155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38113731839639745256538873 28585298879729808942404155)
        ·
          refine ⟨42877948319594713413606233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28585298879729808942404155 42877948319594713413606233)
          ·
            refine ⟨32158461239696035060204675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42877948319594713413606233 32158461239696035060204675)
            ·
              refine ⟨48237691859544052590307013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32158461239696035060204675 48237691859544052590307013)
              ·
                refine ⟨9044567223664509860682565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48237691859544052590307013 9044567223664509860682565)
                ·
                  refine ⟨1695856354437095598877981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9044567223664509860682565 1695856354437095598877981)
                  ·
                    refine ⟨635946132913910849579243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1695856354437095598877981 635946132913910849579243)
                    ·
                      rfl

theorem cell22_1857751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 4, 3].length) (baseStart_1857751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1857751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1857751 prefixEnd_1857751 := by exact prefixLift 1857751
  have htrace : WordTrace (prefixWord ++ tailWord_1857751) baseStart_1857751 baseEnd_1857751 := by
    simpa [prefixWord, tailWord_1857751, baseEnd_1857751] using wordTrace_append hprefix tailTrace_1857751
  have hstable : (prefixWord ++ tailWord_1857751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857751).length < 2 ^ (prefixWord ++ tailWord_1857751).sum := by decide
  have hdescent : baseEnd_1857751 < baseStart_1857751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857768 : List Nat := [2, 1, 4, 1, 2, 3, 1, 1, 4, 3]
def baseStart_1857768 : Nat := 118140960795 + 1857768 * 2 ^ 59
def prefixEnd_1857768 : Nat := 4983230072969 + 3 ^ 40 * 1857768 * 2
def baseEnd_1857768 : Nat := 635951952361328471904191

theorem tailTrace_1857768 : CollatzResearch.WordTrace tailWord_1857768 prefixEnd_1857768 635951952361328471904191 := by
  unfold tailWord_1857768
  simp only [CollatzResearch.WordTrace]
  refine ⟨33879182766815646179718979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45172243689087528239625305 33879182766815646179718979)
  ·
    refine ⟨50818774150223469269578469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33879182766815646179718979 50818774150223469269578469)
    ·
      refine ⟨9528520153166900488045963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50818774150223469269578469 9528520153166900488045963)
      ·
        refine ⟨14292780229750350732068945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9528520153166900488045963 14292780229750350732068945)
        ·
          refine ⟨10719585172312763049051709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14292780229750350732068945 10719585172312763049051709)
          ·
            refine ⟨4019844439617286143394391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10719585172312763049051709 4019844439617286143394391)
            ·
              refine ⟨6029766659425929215091587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4019844439617286143394391 6029766659425929215091587)
              ·
                refine ⟨9044649989138893822637381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6029766659425929215091587 9044649989138893822637381)
                ·
                  refine ⟨1695871872963542591744509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9044649989138893822637381 1695871872963542591744509)
                  ·
                    refine ⟨635951952361328471904191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1695871872963542591744509 635951952361328471904191)
                    ·
                      rfl

theorem cell22_1857768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_1857768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1857768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1857768 prefixEnd_1857768 := by exact prefixLift 1857768
  have htrace : WordTrace (prefixWord ++ tailWord_1857768) baseStart_1857768 baseEnd_1857768 := by
    simpa [prefixWord, tailWord_1857768, baseEnd_1857768] using wordTrace_append hprefix tailTrace_1857768
  have hstable : (prefixWord ++ tailWord_1857768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857768).length < 2 ^ (prefixWord ++ tailWord_1857768).sum := by decide
  have hdescent : baseEnd_1857768 < baseStart_1857768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858008 : List Nat := [2, 1, 2, 2, 2, 1, 1, 4, 3, 4]
def baseStart_1858008 : Nat := 118140960795 + 1858008 * 2 ^ 59
def prefixEnd_1858008 : Nat := 4983230072969 + 3 ^ 40 * 1858008 * 2
def baseEnd_1858008 : Nat := 636034109266047845903455

theorem tailTrace_1858008 : CollatzResearch.WordTrace tailWord_1858008 prefixEnd_1858008 636034109266047845903455 := by
  unfold tailWord_1858008
  simp only [CollatzResearch.WordTrace]
  refine ⟨33883559526380906674087339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45178079368507875565449785 33883559526380906674087339)
  ·
    refine ⟨50825339289571360011131009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33883559526380906674087339 50825339289571360011131009)
    ·
      refine ⟨38119004467178520008348257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50825339289571360011131009 38119004467178520008348257)
      ·
        refine ⟨28589253350383890006261193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38119004467178520008348257 28589253350383890006261193)
        ·
          refine ⟨21441940012787917504695895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28589253350383890006261193 21441940012787917504695895)
          ·
            refine ⟨32162910019181876257043843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21441940012787917504695895 32162910019181876257043843)
            ·
              refine ⟨48244365028772814385565765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32162910019181876257043843 48244365028772814385565765)
              ·
                refine ⟨9045818442894902697293581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48244365028772814385565765 9045818442894902697293581)
                ·
                  refine ⟨3392181916085588511485093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9045818442894902697293581 3392181916085588511485093)
                  ·
                    refine ⟨636034109266047845903455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3392181916085588511485093 636034109266047845903455)
                    ·
                      rfl

theorem cell22_1858008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_1858008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858008 prefixEnd_1858008 := by exact prefixLift 1858008
  have htrace : WordTrace (prefixWord ++ tailWord_1858008) baseStart_1858008 baseEnd_1858008 := by
    simpa [prefixWord, tailWord_1858008, baseEnd_1858008] using wordTrace_append hprefix tailTrace_1858008
  have hstable : (prefixWord ++ tailWord_1858008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858008).length < 2 ^ (prefixWord ++ tailWord_1858008).sum := by decide
  have hdescent : baseEnd_1858008 < baseStart_1858008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858023 : List Nat := [1, 1, 5, 2, 1, 1, 2, 1, 8]
def baseStart_1858023 : Nat := 118140960795 + 1858023 * 2 ^ 59
def prefixEnd_1858023 : Nat := 4983230072969 + 3 ^ 40 * 1858023 * 2
def baseEnd_1858023 : Nat := 212013081357530935592803

theorem tailTrace_1858023 : CollatzResearch.WordTrace tailWord_1858023 prefixEnd_1858023 212013081357530935592803 := by
  unfold tailWord_1858023
  simp only [CollatzResearch.WordTrace]
  refine ⟨67767666147707470909970723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45178444098471647273313815 67767666147707470909970723)
  ·
    refine ⟨101651499221561206364956085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67767666147707470909970723 101651499221561206364956085)
    ·
      refine ⟨9529828052021363096714633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101651499221561206364956085 9529828052021363096714633)
      ·
        refine ⟨7147371039016022322535975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9529828052021363096714633 7147371039016022322535975)
        ·
          refine ⟨10721056558524033483803963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7147371039016022322535975 10721056558524033483803963)
          ·
            refine ⟨16081584837786050225705945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10721056558524033483803963 16081584837786050225705945)
            ·
              refine ⟨12061188628339537669279459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16081584837786050225705945 12061188628339537669279459)
              ·
                refine ⟨18091782942509306503919189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12061188628339537669279459 18091782942509306503919189)
                ·
                  refine ⟨212013081357530935592803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18091782942509306503919189 212013081357530935592803)
                  ·
                    rfl

theorem cell22_1858023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 8].length) (baseStart_1858023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858023 prefixEnd_1858023 := by exact prefixLift 1858023
  have htrace : WordTrace (prefixWord ++ tailWord_1858023) baseStart_1858023 baseEnd_1858023 := by
    simpa [prefixWord, tailWord_1858023, baseEnd_1858023] using wordTrace_append hprefix tailTrace_1858023
  have hstable : (prefixWord ++ tailWord_1858023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858023).length < 2 ^ (prefixWord ++ tailWord_1858023).sum := by decide
  have hdescent : baseEnd_1858023 < baseStart_1858023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858040 : List Nat := [2, 1, 2, 1, 1, 4, 2, 5, 4]
def baseStart_1858040 : Nat := 118140960795 + 1858040 * 2 ^ 59
def prefixEnd_1858040 : Nat := 4983230072969 + 3 ^ 40 * 1858040 * 2
def baseEnd_1858040 : Nat := 212015021173336809701119

theorem tailTrace_1858040 : CollatzResearch.WordTrace tailWord_1858040 prefixEnd_1858040 212015021173336809701119 := by
  unfold tailWord_1858040
  simp only [CollatzResearch.WordTrace]
  refine ⟨33884143094322941406669787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45178857459097255208893049 33884143094322941406669787)
  ·
    refine ⟨50826214641484412110004681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33884143094322941406669787 50826214641484412110004681)
    ·
      refine ⟨38119660981113309082503511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50826214641484412110004681 38119660981113309082503511)
      ·
        refine ⟨57179491471669963623755267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38119660981113309082503511 57179491471669963623755267)
        ·
          refine ⟨85769237207504945435632901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57179491471669963623755267 85769237207504945435632901)
          ·
            refine ⟨16081731976407177269181169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85769237207504945435632901 16081731976407177269181169)
            ·
              refine ⟨12061298982305382951885877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16081731976407177269181169 12061298982305382951885877)
              ·
                refine ⟨1130746779591129651739301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12061298982305382951885877 1130746779591129651739301)
                ·
                  refine ⟨212015021173336809701119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1130746779591129651739301 212015021173336809701119)
                  ·
                    rfl

theorem cell22_1858040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 5, 4].length) (baseStart_1858040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858040 prefixEnd_1858040 := by exact prefixLift 1858040
  have htrace : WordTrace (prefixWord ++ tailWord_1858040) baseStart_1858040 baseEnd_1858040 := by
    simpa [prefixWord, tailWord_1858040, baseEnd_1858040] using wordTrace_append hprefix tailTrace_1858040
  have hstable : (prefixWord ++ tailWord_1858040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858040).length < 2 ^ (prefixWord ++ tailWord_1858040).sum := by decide
  have hdescent : baseEnd_1858040 < baseStart_1858040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858050 : List Nat := [3, 4, 1, 2, 3, 1, 2, 2, 1, 3]
def baseStart_1858050 : Nat := 118140960795 + 1858050 * 2 ^ 59
def prefixEnd_1858050 : Nat := 4983230072969 + 3 ^ 40 * 1858050 * 2
def baseEnd_1858050 : Nat := 636048486724373736353327

theorem tailTrace_1858050 : CollatzResearch.WordTrace tailWord_1858050 prefixEnd_1858050 636048486724373736353327 := by
  unfold tailWord_1858050
  simp only [CollatzResearch.WordTrace]
  refine ⟨16942162729652413630300901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45179100612406436347469069 16942162729652413630300901)
  ·
    refine ⟨3176655511809827555681419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16942162729652413630300901 3176655511809827555681419)
    ·
      refine ⟨4764983267714741333522129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3176655511809827555681419 4764983267714741333522129)
      ·
        refine ⟨3573737450786056000141597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4764983267714741333522129 3573737450786056000141597)
        ·
          refine ⟨1340151544044771000053099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3573737450786056000141597 1340151544044771000053099)
          ·
            refine ⟨2010227316067156500079649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1340151544044771000053099 2010227316067156500079649)
            ·
              refine ⟨1507670487050367375059737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2010227316067156500079649 1507670487050367375059737)
              ·
                refine ⟨1130752865287775531294803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1507670487050367375059737 1130752865287775531294803)
                ·
                  refine ⟨1696129297931663296942205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1130752865287775531294803 1696129297931663296942205)
                  ·
                    refine ⟨636048486724373736353327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1696129297931663296942205 636048486724373736353327)
                    ·
                      rfl

theorem cell22_1858050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_1858050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858050 prefixEnd_1858050 := by exact prefixLift 1858050
  have htrace : WordTrace (prefixWord ++ tailWord_1858050) baseStart_1858050 baseEnd_1858050 := by
    simpa [prefixWord, tailWord_1858050, baseEnd_1858050] using wordTrace_append hprefix tailTrace_1858050
  have hstable : (prefixWord ++ tailWord_1858050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858050).length < 2 ^ (prefixWord ++ tailWord_1858050).sum := by decide
  have hdescent : baseEnd_1858050 < baseStart_1858050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858072 : List Nat := [2, 1, 2, 3, 3, 1, 2, 3, 2, 3]
def baseStart_1858072 : Nat := 118140960795 + 1858072 * 2 ^ 59
def prefixEnd_1858072 : Nat := 4983230072969 + 3 ^ 40 * 1858072 * 2
def baseEnd_1858072 : Nat := 636056017773973012303259

theorem tailTrace_1858072 : CollatzResearch.WordTrace tailWord_1858072 prefixEnd_1858072 636056017773973012303259 := by
  unfold tailWord_1858072
  simp only [CollatzResearch.WordTrace]
  refine ⟨33884726662264976139252235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45179635549686634852336313 33884726662264976139252235)
  ·
    refine ⟨50827089993397464208878353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33884726662264976139252235 50827089993397464208878353)
    ·
      refine ⟨38120317495048098156658765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50827089993397464208878353 38120317495048098156658765)
      ·
        refine ⟨14295119060643036808747037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38120317495048098156658765 14295119060643036808747037)
        ·
          refine ⟨5360669647741138803280139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14295119060643036808747037 5360669647741138803280139)
          ·
            refine ⟨8041004471611708204920209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5360669647741138803280139 8041004471611708204920209)
            ·
              refine ⟨6030753353708781153690157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8041004471611708204920209 6030753353708781153690157)
              ·
                refine ⟨2261532507640792932633809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6030753353708781153690157 2261532507640792932633809)
                ·
                  refine ⟨1696149380730594699475357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2261532507640792932633809 1696149380730594699475357)
                  ·
                    refine ⟨636056017773973012303259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1696149380730594699475357 636056017773973012303259)
                    ·
                      rfl

theorem cell22_1858072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 2, 3].length) (baseStart_1858072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858072 prefixEnd_1858072 := by exact prefixLift 1858072
  have htrace : WordTrace (prefixWord ++ tailWord_1858072) baseStart_1858072 baseEnd_1858072 := by
    simpa [prefixWord, tailWord_1858072, baseEnd_1858072] using wordTrace_append hprefix tailTrace_1858072
  have hstable : (prefixWord ++ tailWord_1858072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858072).length < 2 ^ (prefixWord ++ tailWord_1858072).sum := by decide
  have hdescent : baseEnd_1858072 < baseStart_1858072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858117 : List Nat := [1, 3, 1, 1, 1, 6, 2, 1, 3, 3]
def baseStart_1858117 : Nat := 118140960795 + 1858117 * 2 ^ 59
def prefixEnd_1858117 : Nat := 4983230072969 + 3 ^ 40 * 1858117 * 2
def baseEnd_1858117 : Nat := 636071422193607894928121

theorem tailTrace_1858117 : CollatzResearch.WordTrace tailWord_1858117 prefixEnd_1858117 636071422193607894928121 := by
  unfold tailWord_1858117
  simp only [CollatzResearch.WordTrace]
  refine ⟨67771094609366924963892605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45180729739577949975928403 67771094609366924963892605)
  ·
    refine ⟨25414160478512596861459727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67771094609366924963892605 25414160478512596861459727)
    ·
      refine ⟨38121240717768895292189591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25414160478512596861459727 38121240717768895292189591)
      ·
        refine ⟨57181861076653342938284387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38121240717768895292189591 57181861076653342938284387)
        ·
          refine ⟨85772791614980014407426581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57181861076653342938284387 85772791614980014407426581)
          ·
            refine ⟨4020599606952188175348121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 85772791614980014407426581 4020599606952188175348121)
            ·
              refine ⟨3015449705214141131511091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4020599606952188175348121 3015449705214141131511091)
              ·
                refine ⟨4523174557821211697266637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3015449705214141131511091 4523174557821211697266637)
                ·
                  refine ⟨1696190459182954386474989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4523174557821211697266637 1696190459182954386474989)
                  ·
                    refine ⟨636071422193607894928121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1696190459182954386474989 636071422193607894928121)
                    ·
                      rfl

theorem cell22_1858117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 3, 3].length) (baseStart_1858117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858117 prefixEnd_1858117 := by exact prefixLift 1858117
  have htrace : WordTrace (prefixWord ++ tailWord_1858117) baseStart_1858117 baseEnd_1858117 := by
    simpa [prefixWord, tailWord_1858117, baseEnd_1858117] using wordTrace_append hprefix tailTrace_1858117
  have hstable : (prefixWord ++ tailWord_1858117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858117).length < 2 ^ (prefixWord ++ tailWord_1858117).sum := by decide
  have hdescent : baseEnd_1858117 < baseStart_1858117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858128 : List Nat := [2, 1, 1, 1, 1, 3, 2, 3, 1, 7]
def baseStart_1858128 : Nat := 118140960795 + 1858128 * 2 ^ 59
def prefixEnd_1858128 : Nat := 4983230072969 + 3 ^ 40 * 1858128 * 2
def baseEnd_1858128 : Nat := 636075187718407532903087

theorem tailTrace_1858128 : CollatzResearch.WordTrace tailWord_1858128 prefixEnd_1858128 636075187718407532903087 := by
  unfold tailWord_1858128
  simp only [CollatzResearch.WordTrace]
  refine ⟨33885747906163536921271519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45180997208218049228362025 33885747906163536921271519)
  ·
    refine ⟨50828621859245305381907279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33885747906163536921271519 50828621859245305381907279)
    ·
      refine ⟨76242932788867958072860919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50828621859245305381907279 76242932788867958072860919)
      ·
        refine ⟨114364399183301937109291379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76242932788867958072860919 114364399183301937109291379)
        ·
          refine ⟨171546598774952905663937069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114364399183301937109291379 171546598774952905663937069)
          ·
            refine ⟨64329974540607339623976401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171546598774952905663937069 64329974540607339623976401)
            ·
              refine ⟨48247480905455504717982301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64329974540607339623976401 48247480905455504717982301)
              ·
                refine ⟨18092805339545814269243363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48247480905455504717982301 18092805339545814269243363)
                ·
                  refine ⟨27139208009318721403865045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18092805339545814269243363 27139208009318721403865045)
                  ·
                    refine ⟨636075187718407532903087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27139208009318721403865045 636075187718407532903087)
                    ·
                      rfl

theorem cell22_1858128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 1, 7].length) (baseStart_1858128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858128 prefixEnd_1858128 := by exact prefixLift 1858128
  have htrace : WordTrace (prefixWord ++ tailWord_1858128) baseStart_1858128 baseEnd_1858128 := by
    simpa [prefixWord, tailWord_1858128, baseEnd_1858128] using wordTrace_append hprefix tailTrace_1858128
  have hstable : (prefixWord ++ tailWord_1858128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858128).length < 2 ^ (prefixWord ++ tailWord_1858128).sum := by decide
  have hdescent : baseEnd_1858128 < baseStart_1858128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858143 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 2, 8]
def baseStart_1858143 : Nat := 118140960795 + 1858143 * 2 ^ 59
def prefixEnd_1858143 : Nat := 4983230072969 + 3 ^ 40 * 1858143 * 2
def baseEnd_1858143 : Nat := 636080322524952493778041

theorem tailTrace_1858143 : CollatzResearch.WordTrace tailWord_1858143 prefixEnd_1858143 636080322524952493778041 := by
  unfold tailWord_1858143
  simp only [CollatzResearch.WordTrace]
  refine ⟨67772042907272731404339083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45181361938181820936226055 67772042907272731404339083)
  ·
    refine ⟨101658064360909097106508625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67772042907272731404339083 101658064360909097106508625)
    ·
      refine ⟨76243548270681822829881469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101658064360909097106508625 76243548270681822829881469)
      ·
        refine ⟨28591330601505683561205551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76243548270681822829881469 28591330601505683561205551)
        ·
          refine ⟨42886995902258525341808327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28591330601505683561205551 42886995902258525341808327)
          ·
            refine ⟨64330493853387788012712491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42886995902258525341808327 64330493853387788012712491)
            ·
              refine ⟨96495740780081682019068737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64330493853387788012712491 96495740780081682019068737)
              ·
                refine ⟨72371805585061261514301553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96495740780081682019068737 72371805585061261514301553)
                ·
                  refine ⟨54278854188795946135726165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72371805585061261514301553 54278854188795946135726165)
                  ·
                    refine ⟨636080322524952493778041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54278854188795946135726165 636080322524952493778041)
                    ·
                      rfl

theorem cell22_1858143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 8].length) (baseStart_1858143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858143 prefixEnd_1858143 := by exact prefixLift 1858143
  have htrace : WordTrace (prefixWord ++ tailWord_1858143) baseStart_1858143 baseEnd_1858143 := by
    simpa [prefixWord, tailWord_1858143, baseEnd_1858143] using wordTrace_append hprefix tailTrace_1858143
  have hstable : (prefixWord ++ tailWord_1858143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858143).length < 2 ^ (prefixWord ++ tailWord_1858143).sum := by decide
  have hdescent : baseEnd_1858143 < baseStart_1858143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858194 : List Nat := [3, 2, 3, 1, 2, 1, 3, 2, 1, 4]
def baseStart_1858194 : Nat := 118140960795 + 1858194 * 2 ^ 59
def prefixEnd_1858194 : Nat := 4983230072969 + 3 ^ 40 * 1858194 * 2
def baseEnd_1858194 : Nat := 636097780867205360752885

theorem tailTrace_1858194 : CollatzResearch.WordTrace tailWord_1858194 prefixEnd_1858194 636097780867205360752885 := by
  unfold tailWord_1858194
  simp only [CollatzResearch.WordTrace]
  refine ⟨16943475757521991778611409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45182602020058644742963757 16943475757521991778611409)
  ·
    refine ⟨12707606818141493833958557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16943475757521991778611409 12707606818141493833958557)
    ·
      refine ⟨4765352556803060187734459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12707606818141493833958557 4765352556803060187734459)
      ·
        refine ⟨7148028835204590281601689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4765352556803060187734459 7148028835204590281601689)
        ·
          refine ⟨5361021626403442711201267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7148028835204590281601689 5361021626403442711201267)
          ·
            refine ⟨8041532439605164066801901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5361021626403442711201267 8041532439605164066801901)
            ·
              refine ⟨3015574664851936525050713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8041532439605164066801901 3015574664851936525050713)
              ·
                refine ⟨2261680998638952393788035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3015574664851936525050713 2261680998638952393788035)
                ·
                  refine ⟨3392521497958428590682053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2261680998638952393788035 3392521497958428590682053)
                  ·
                    refine ⟨636097780867205360752885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3392521497958428590682053 636097780867205360752885)
                    ·
                      rfl

theorem cell22_1858194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_1858194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858194 prefixEnd_1858194 := by exact prefixLift 1858194
  have htrace : WordTrace (prefixWord ++ tailWord_1858194) baseStart_1858194 baseEnd_1858194 := by
    simpa [prefixWord, tailWord_1858194, baseEnd_1858194] using wordTrace_append hprefix tailTrace_1858194
  have hstable : (prefixWord ++ tailWord_1858194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858194).length < 2 ^ (prefixWord ++ tailWord_1858194).sum := by decide
  have hdescent : baseEnd_1858194 < baseStart_1858194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858205 : List Nat := [1, 4, 2, 1, 1, 1, 2, 3, 1, 6]
def baseStart_1858205 : Nat := 118140960795 + 1858205 * 2 ^ 59
def prefixEnd_1858205 : Nat := 4983230072969 + 3 ^ 40 * 1858205 * 2
def baseEnd_1858205 : Nat := 636101546392004998727851

theorem tailTrace_1858205 : CollatzResearch.WordTrace tailWord_1858205 prefixEnd_1858205 636101546392004998727851 := by
  unfold tailWord_1858205
  simp only [CollatzResearch.WordTrace]
  refine ⟨67774304233048115993096069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45182869488698743995397379 67774304233048115993096069)
  ·
    refine ⟨12707682043696521748705513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67774304233048115993096069 12707682043696521748705513)
    ·
      refine ⟨9530761532772391311529135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12707682043696521748705513 9530761532772391311529135)
      ·
        refine ⟨14296142299158586967293703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9530761532772391311529135 14296142299158586967293703)
        ·
          refine ⟨21444213448737880450940555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14296142299158586967293703 21444213448737880450940555)
          ·
            refine ⟨32166320173106820676410833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21444213448737880450940555 32166320173106820676410833)
            ·
              refine ⟨24124740129830115507308125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32166320173106820676410833 24124740129830115507308125)
              ·
                refine ⟨9046777548686293315240547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24124740129830115507308125 9046777548686293315240547)
                ·
                  refine ⟨13570166323029439972860821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9046777548686293315240547 13570166323029439972860821)
                  ·
                    refine ⟨636101546392004998727851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13570166323029439972860821 636101546392004998727851)
                    ·
                      rfl

theorem cell22_1858205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_1858205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858205 prefixEnd_1858205 := by exact prefixLift 1858205
  have htrace : WordTrace (prefixWord ++ tailWord_1858205) baseStart_1858205 baseEnd_1858205 := by
    simpa [prefixWord, tailWord_1858205, baseEnd_1858205] using wordTrace_append hprefix tailTrace_1858205
  have hstable : (prefixWord ++ tailWord_1858205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858205).length < 2 ^ (prefixWord ++ tailWord_1858205).sum := by decide
  have hdescent : baseEnd_1858205 < baseStart_1858205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858237 : List Nat := [1, 4, 1, 2, 1, 5, 1, 7]
def baseStart_1858237 : Nat := 118140960795 + 1858237 * 2 ^ 59
def prefixEnd_1858237 : Nat := 4983230072969 + 3 ^ 40 * 1858237 * 2
def baseEnd_1858237 : Nat := 70679166738440842436417

theorem tailTrace_1858237 : CollatzResearch.WordTrace tailWord_1858237 prefixEnd_1858237 70679166738440842436417 := by
  unfold tailWord_1858237
  simp only [CollatzResearch.WordTrace]
  refine ⟨67775471368932185458260965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45183647579288123638840643 67775471368932185458260965)
  ·
    refine ⟨12707900881674784773423931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67775471368932185458260965 12707900881674784773423931)
    ·
      refine ⟨19061851322512177160135897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12707900881674784773423931 19061851322512177160135897)
      ·
        refine ⟨14296388491884132870101923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19061851322512177160135897 14296388491884132870101923)
        ·
          refine ⟨21444582737826199305152885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14296388491884132870101923 21444582737826199305152885)
          ·
            refine ⟨2010429631671206184858083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21444582737826199305152885 2010429631671206184858083)
            ·
              refine ⟨3015644447506809277287125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2010429631671206184858083 3015644447506809277287125)
              ·
                refine ⟨70679166738440842436417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3015644447506809277287125 70679166738440842436417)
                ·
                  rfl

theorem cell22_1858237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 7].length) (baseStart_1858237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858237 prefixEnd_1858237 := by exact prefixLift 1858237
  have htrace : WordTrace (prefixWord ++ tailWord_1858237) baseStart_1858237 baseEnd_1858237 := by
    simpa [prefixWord, tailWord_1858237, baseEnd_1858237] using wordTrace_append hprefix tailTrace_1858237
  have hstable : (prefixWord ++ tailWord_1858237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858237).length < 2 ^ (prefixWord ++ tailWord_1858237).sum := by decide
  have hdescent : baseEnd_1858237 < baseStart_1858237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858241 : List Nat := [1, 2, 6, 2, 1, 1, 2, 1, 1, 5]
def baseStart_1858241 : Nat := 118140960795 + 1858241 * 2 ^ 59
def prefixEnd_1858241 : Nat := 4983230072969 + 3 ^ 40 * 1858241 * 2
def baseEnd_1858241 : Nat := 636113869927712904827741

theorem tailTrace_1858241 : CollatzResearch.WordTrace tailWord_1858241 prefixEnd_1858241 636113869927712904827741 := by
  unfold tailWord_1858241
  simp only [CollatzResearch.WordTrace]
  refine ⟨67775617260917694141406577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45183744840611796094271051 67775617260917694141406577)
  ·
    refine ⟨50831712945688270606054933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67775617260917694141406577 50831712945688270606054933)
    ·
      refine ⟨2382736544329137684658825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50831712945688270606054933 2382736544329137684658825)
      ·
        refine ⟨1787052408246853263494119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2382736544329137684658825 1787052408246853263494119)
        ·
          refine ⟨2680578612370279895241179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1787052408246853263494119 2680578612370279895241179)
          ·
            refine ⟨4020867918555419842861769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2680578612370279895241179 4020867918555419842861769)
            ·
              refine ⟨3015650938916564882146327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4020867918555419842861769 3015650938916564882146327)
              ·
                refine ⟨4523476408374847323219491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3015650938916564882146327 4523476408374847323219491)
                ·
                  refine ⟨6785214612562270984829237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4523476408374847323219491 6785214612562270984829237)
                  ·
                    refine ⟨636113869927712904827741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6785214612562270984829237 636113869927712904827741)
                    ·
                      rfl

theorem cell22_1858241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_1858241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858241 prefixEnd_1858241 := by exact prefixLift 1858241
  have htrace : WordTrace (prefixWord ++ tailWord_1858241) baseStart_1858241 baseEnd_1858241 := by
    simpa [prefixWord, tailWord_1858241, baseEnd_1858241] using wordTrace_append hprefix tailTrace_1858241
  have hstable : (prefixWord ++ tailWord_1858241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858241).length < 2 ^ (prefixWord ++ tailWord_1858241).sum := by decide
  have hdescent : baseEnd_1858241 < baseStart_1858241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858265 : List Nat := [1, 2, 1, 2, 3, 2, 2, 2, 7]
def baseStart_1858265 : Nat := 118140960795 + 1858265 * 2 ^ 59
def prefixEnd_1858265 : Nat := 4983230072969 + 3 ^ 40 * 1858265 * 2
def baseEnd_1858265 : Nat := 212040695206061614075889

theorem tailTrace_1858265 : CollatzResearch.WordTrace tailWord_1858265 prefixEnd_1858265 212040695206061614075889 := by
  unfold tailWord_1858265
  simp only [CollatzResearch.WordTrace]
  refine ⟨67776492612830746240280249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45184328408553830826853499 67776492612830746240280249)
  ·
    refine ⟨50832369459623059680210187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67776492612830746240280249 50832369459623059680210187)
    ·
      refine ⟨76248554189434589520315281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50832369459623059680210187 76248554189434589520315281)
      ·
        refine ⟨57186415642075942140236461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76248554189434589520315281 57186415642075942140236461)
        ·
          refine ⟨21444905865778478302588673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57186415642075942140236461 21444905865778478302588673)
          ·
            refine ⟨16083679399333858726941505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21444905865778478302588673 16083679399333858726941505)
            ·
              refine ⟨12062759549500394045206129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16083679399333858726941505 12062759549500394045206129)
              ·
                refine ⟨9047069662125295533904597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12062759549500394045206129 9047069662125295533904597)
                ·
                  refine ⟨212040695206061614075889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9047069662125295533904597 212040695206061614075889)
                  ·
                    rfl

theorem cell22_1858265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 7].length) (baseStart_1858265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858265 prefixEnd_1858265 := by exact prefixLift 1858265
  have htrace : WordTrace (prefixWord ++ tailWord_1858265) baseStart_1858265 baseEnd_1858265 := by
    simpa [prefixWord, tailWord_1858265, baseEnd_1858265] using wordTrace_append hprefix tailTrace_1858265
  have hstable : (prefixWord ++ tailWord_1858265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858265).length < 2 ^ (prefixWord ++ tailWord_1858265).sum := by decide
  have hdescent : baseEnd_1858265 < baseStart_1858265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858286 : List Nat := [4, 1, 2, 1, 1, 3, 2, 4, 1, 3]
def baseStart_1858286 : Nat := 118140960795 + 1858286 * 2 ^ 59
def prefixEnd_1858286 : Nat := 4983230072969 + 3 ^ 40 * 1858286 * 2
def baseEnd_1858286 : Nat := 636129274347347787452603

theorem tailTrace_1858286 : CollatzResearch.WordTrace tailWord_1858286 prefixEnd_1858286 636129274347347787452603 := by
  unfold tailWord_1858286
  simp only [CollatzResearch.WordTrace]
  refine ⟨8472157318219333353349339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45184839030503111217863141 8472157318219333353349339)
  ·
    refine ⟨12708235977329000030024009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8472157318219333353349339 12708235977329000030024009)
    ·
      refine ⟨9531176982996750022518007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12708235977329000030024009 9531176982996750022518007)
      ·
        refine ⟨14296765474495125033777011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9531176982996750022518007 14296765474495125033777011)
        ·
          refine ⟨21445148211742687550665517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14296765474495125033777011 21445148211742687550665517)
          ·
            refine ⟨8041930579403507831499569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21445148211742687550665517 8041930579403507831499569)
            ·
              refine ⟨6031447934552630873624677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8041930579403507831499569 6031447934552630873624677)
              ·
                refine ⟨1130896487728618288804627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6031447934552630873624677 1130896487728618288804627)
                ·
                  refine ⟨1696344731592927433206941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1130896487728618288804627 1696344731592927433206941)
                  ·
                    refine ⟨636129274347347787452603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1696344731592927433206941 636129274347347787452603)
                    ·
                      rfl

theorem cell22_1858286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_1858286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858286 prefixEnd_1858286 := by exact prefixLift 1858286
  have htrace : WordTrace (prefixWord ++ tailWord_1858286) baseStart_1858286 baseEnd_1858286 := by
    simpa [prefixWord, tailWord_1858286, baseEnd_1858286] using wordTrace_append hprefix tailTrace_1858286
  have hstable : (prefixWord ++ tailWord_1858286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858286).length < 2 ^ (prefixWord ++ tailWord_1858286).sum := by decide
  have hdescent : baseEnd_1858286 < baseStart_1858286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858359 : List Nat := [1, 1, 3, 1, 2, 1, 5, 3, 2, 3]
def baseStart_1858359 : Nat := 118140960795 + 1858359 * 2 ^ 59
def prefixEnd_1858359 : Nat := 4983230072969 + 3 ^ 40 * 1858359 * 2
def baseEnd_1858359 : Nat := 636154263739199930377379

theorem tailTrace_1858359 : CollatzResearch.WordTrace tailWord_1858359 prefixEnd_1858359 636154263739199930377379 := by
  unfold tailWord_1858359
  simp only [CollatzResearch.WordTrace]
  refine ⟨67779921074490200294202131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45186614049660133529468087 67779921074490200294202131)
  ·
    refine ⟨101669881611735300441303197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67779921074490200294202131 101669881611735300441303197)
    ·
      refine ⟨38126205604400737665488699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101669881611735300441303197 38126205604400737665488699)
      ·
        refine ⟨57189308406601106498233049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38126205604400737665488699 57189308406601106498233049)
        ·
          refine ⟨42891981304950829873674787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57189308406601106498233049 42891981304950829873674787)
          ·
            refine ⟨64337971957426244810512181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42891981304950829873674787 64337971957426244810512181)
            ·
              refine ⟨6031684871008710450985517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64337971957426244810512181 6031684871008710450985517)
              ·
                refine ⟨2261881826628266419119569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6031684871008710450985517 2261881826628266419119569)
                ·
                  refine ⟨1696411369971199814339677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2261881826628266419119569 1696411369971199814339677)
                  ·
                    refine ⟨636154263739199930377379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1696411369971199814339677 636154263739199930377379)
                    ·
                      rfl

theorem cell22_1858359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 2, 3].length) (baseStart_1858359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858359 prefixEnd_1858359 := by exact prefixLift 1858359
  have htrace : WordTrace (prefixWord ++ tailWord_1858359) baseStart_1858359 baseEnd_1858359 := by
    simpa [prefixWord, tailWord_1858359, baseEnd_1858359] using wordTrace_append hprefix tailTrace_1858359
  have hstable : (prefixWord ++ tailWord_1858359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858359).length < 2 ^ (prefixWord ++ tailWord_1858359).sum := by decide
  have hdescent : baseEnd_1858359 < baseStart_1858359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858421 : List Nat := [1, 3, 4, 1, 1, 3, 1, 2, 3, 3]
def baseStart_1858421 : Nat := 118140960795 + 1858421 * 2 ^ 59
def prefixEnd_1858421 : Nat := 4983230072969 + 3 ^ 40 * 1858421 * 2
def baseEnd_1858421 : Nat := 636175487606252435327189

theorem tailTrace_1858421 : CollatzResearch.WordTrace tailWord_1858421 prefixEnd_1858421 636175487606252435327189 := by
  unfold tailWord_1858421
  simp only [CollatzResearch.WordTrace]
  refine ⟨67782182400265584882959117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45188121600177056588639411 67782182400265584882959117)
  ·
    refine ⟨25418318400099594331109669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67782182400265584882959117 25418318400099594331109669)
    ·
      refine ⟨4765934700018673937083063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25418318400099594331109669 4765934700018673937083063)
      ·
        refine ⟨7148902050028010905624595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4765934700018673937083063 7148902050028010905624595)
        ·
          refine ⟨10723353075042016358436893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7148902050028010905624595 10723353075042016358436893)
          ·
            refine ⟨4021257403140756134413835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10723353075042016358436893 4021257403140756134413835)
            ·
              refine ⟨6031886104711134201620753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4021257403140756134413835 6031886104711134201620753)
              ·
                refine ⟨4523914578533350651215565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6031886104711134201620753 4523914578533350651215565)
                ·
                  refine ⟨1696467966950006494205837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4523914578533350651215565 1696467966950006494205837)
                  ·
                    refine ⟨636175487606252435327189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1696467966950006494205837 636175487606252435327189)
                    ·
                      rfl

theorem cell22_1858421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_1858421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858421 prefixEnd_1858421 := by exact prefixLift 1858421
  have htrace : WordTrace (prefixWord ++ tailWord_1858421) baseStart_1858421 baseEnd_1858421 := by
    simpa [prefixWord, tailWord_1858421, baseEnd_1858421] using wordTrace_append hprefix tailTrace_1858421
  have hstable : (prefixWord ++ tailWord_1858421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858421).length < 2 ^ (prefixWord ++ tailWord_1858421).sum := by decide
  have hdescent : baseEnd_1858421 < baseStart_1858421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858494 : List Nat := [4, 2, 1, 1, 1, 2, 2, 1, 3, 5]
def baseStart_1858494 : Nat := 118140960795 + 1858494 * 2 ^ 59
def prefixEnd_1858494 : Nat := 4983230072969 + 3 ^ 40 * 1858494 * 2
def baseEnd_1858494 : Nat := 636200476998104578251965

theorem tailTrace_1858494 : CollatzResearch.WordTrace tailWord_1858494 prefixEnd_1858494 636200476998104578251965 := by
  unfold tailWord_1858494
  simp only [CollatzResearch.WordTrace]
  refine ⟨8473105616125139793795817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45189896619334078900244357 8473105616125139793795817)
  ·
    refine ⟨6354829212093854845346863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8473105616125139793795817 6354829212093854845346863)
    ·
      refine ⟨9532243818140782268020295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6354829212093854845346863 9532243818140782268020295)
      ·
        refine ⟨14298365727211173402030443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9532243818140782268020295 14298365727211173402030443)
        ·
          refine ⟨21447548590816760103045665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14298365727211173402030443 21447548590816760103045665)
          ·
            refine ⟨16085661443112570077284249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21447548590816760103045665 16085661443112570077284249)
            ·
              refine ⟨12064246082334427557963187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16085661443112570077284249 12064246082334427557963187)
              ·
                refine ⟨18096369123501641336944781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12064246082334427557963187 18096369123501641336944781)
                ·
                  refine ⟨6786138421313115501354293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18096369123501641336944781 6786138421313115501354293)
                  ·
                    refine ⟨636200476998104578251965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6786138421313115501354293 636200476998104578251965)
                    ·
                      rfl

theorem cell22_1858494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_1858494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858494 prefixEnd_1858494 := by exact prefixLift 1858494
  have htrace : WordTrace (prefixWord ++ tailWord_1858494) baseStart_1858494 baseEnd_1858494 := by
    simpa [prefixWord, tailWord_1858494, baseEnd_1858494] using wordTrace_append hprefix tailTrace_1858494
  have hstable : (prefixWord ++ tailWord_1858494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858494).length < 2 ^ (prefixWord ++ tailWord_1858494).sum := by decide
  have hdescent : baseEnd_1858494 < baseStart_1858494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858496 : List Nat := [2, 1, 1, 2, 3, 3, 3, 3, 4]
def baseStart_1858496 : Nat := 118140960795 + 1858496 * 2 ^ 59
def prefixEnd_1858496 : Nat := 4983230072969 + 3 ^ 40 * 1858496 * 2
def baseEnd_1858496 : Nat := 212067053879659079900653

theorem tailTrace_1858496 : CollatzResearch.WordTrace tailWord_1858496 prefixEnd_1858496 212067053879659079900653 := by
  unfold tailWord_1858496
  simp only [CollatzResearch.WordTrace]
  refine ⟨33892458937496936345969671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45189945249995915127959561 33892458937496936345969671)
  ·
    refine ⟨50838688406245404518954507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33892458937496936345969671 50838688406245404518954507)
    ·
      refine ⟨76258032609368106778431761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50838688406245404518954507 76258032609368106778431761)
      ·
        refine ⟨57193524457026080083823821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76258032609368106778431761 57193524457026080083823821)
        ·
          refine ⟨21447571671384780031433933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57193524457026080083823821 21447571671384780031433933)
          ·
            refine ⟨8042839376769292511787725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21447571671384780031433933 8042839376769292511787725)
            ·
              refine ⟨3016064766288484691920397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8042839376769292511787725 3016064766288484691920397)
              ·
                refine ⟨1131024287358181759470149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3016064766288484691920397 1131024287358181759470149)
                ·
                  refine ⟨212067053879659079900653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1131024287358181759470149 212067053879659079900653)
                  ·
                    rfl

theorem cell22_1858496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 3, 4].length) (baseStart_1858496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858496 prefixEnd_1858496 := by exact prefixLift 1858496
  have htrace : WordTrace (prefixWord ++ tailWord_1858496) baseStart_1858496 baseEnd_1858496 := by
    simpa [prefixWord, tailWord_1858496, baseEnd_1858496] using wordTrace_append hprefix tailTrace_1858496
  have hstable : (prefixWord ++ tailWord_1858496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858496).length < 2 ^ (prefixWord ++ tailWord_1858496).sum := by decide
  have hdescent : baseEnd_1858496 < baseStart_1858496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858507 : List Nat := [1, 1, 1, 1, 3, 5, 10]
def baseStart_1858507 : Nat := 118140960795 + 1858507 * 2 ^ 59
def prefixEnd_1858507 : Nat := 4983230072969 + 3 ^ 40 * 1858507 * 2
def baseEnd_1858507 : Nat := 23563145450510254728775

theorem tailTrace_1858507 : CollatzResearch.WordTrace tailWord_1858507 prefixEnd_1858507 23563145450510254728775 := by
  unfold tailWord_1858507
  simp only [CollatzResearch.WordTrace]
  refine ⟨67785319077954021570589775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45190212718636014380393183 67785319077954021570589775)
  ·
    refine ⟨101677978616931032355884663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67785319077954021570589775 101677978616931032355884663)
    ·
      refine ⟨152516967925396548533826995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101677978616931032355884663 152516967925396548533826995)
      ·
        refine ⟨228775451888094822800740493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152516967925396548533826995 228775451888094822800740493)
        ·
          refine ⟨85790794458035558550277685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228775451888094822800740493 85790794458035558550277685)
          ·
            refine ⟨8042886980440833614088533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85790794458035558550277685 8042886980440833614088533)
            ·
              refine ⟨23563145450510254728775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8042886980440833614088533 23563145450510254728775)
              ·
                rfl

theorem cell22_1858507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 10].length) (baseStart_1858507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858507 prefixEnd_1858507 := by exact prefixLift 1858507
  have htrace : WordTrace (prefixWord ++ tailWord_1858507) baseStart_1858507 baseEnd_1858507 := by
    simpa [prefixWord, tailWord_1858507, baseEnd_1858507] using wordTrace_append hprefix tailTrace_1858507
  have hstable : (prefixWord ++ tailWord_1858507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858507).length < 2 ^ (prefixWord ++ tailWord_1858507).sum := by decide
  have hdescent : baseEnd_1858507 < baseStart_1858507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858562 : List Nat := [3, 4, 1, 3, 1, 1, 2, 2, 2, 3]
def baseStart_1858562 : Nat := 118140960795 + 1858562 * 2 ^ 59
def prefixEnd_1858562 : Nat := 4983230072969 + 3 ^ 40 * 1858562 * 2
def baseEnd_1858562 : Nat := 636223754787775067551757

theorem tailTrace_1858562 : CollatzResearch.WordTrace tailWord_1858562 prefixEnd_1858562 636223754787775067551757 := by
  unfold tailWord_1858562
  simp only [CollatzResearch.WordTrace]
  refine ⟨16946831273188691490960485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45191550061836510642561293 16946831273188691490960485)
  ·
    refine ⟨3177530863722879654555091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16946831273188691490960485 3177530863722879654555091)
    ·
      refine ⟨4766296295584319481832637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3177530863722879654555091 4766296295584319481832637)
      ·
        refine ⟨1787361110844119805687239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4766296295584319481832637 1787361110844119805687239)
        ·
          refine ⟨2681041666266179708530859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1787361110844119805687239 2681041666266179708530859)
          ·
            refine ⟨4021562499399269562796289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2681041666266179708530859 4021562499399269562796289)
            ·
              refine ⟨3016171874549452172097217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4021562499399269562796289 3016171874549452172097217)
              ·
                refine ⟨2262128905912089129072913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3016171874549452172097217 2262128905912089129072913)
                ·
                  refine ⟨1696596679434066846804685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2262128905912089129072913 1696596679434066846804685)
                  ·
                    refine ⟨636223754787775067551757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1696596679434066846804685 636223754787775067551757)
                    ·
                      rfl

theorem cell22_1858562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_1858562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858562 prefixEnd_1858562 := by exact prefixLift 1858562
  have htrace : WordTrace (prefixWord ++ tailWord_1858562) baseStart_1858562 baseEnd_1858562 := by
    simpa [prefixWord, tailWord_1858562, baseEnd_1858562] using wordTrace_append hprefix tailTrace_1858562
  have hstable : (prefixWord ++ tailWord_1858562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858562).length < 2 ^ (prefixWord ++ tailWord_1858562).sum := by decide
  have hdescent : baseEnd_1858562 < baseStart_1858562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858584 : List Nat := [2, 1, 2, 3, 2, 2, 1, 1, 1, 7]
def baseStart_1858584 : Nat := 118140960795 + 1858584 * 2 ^ 59
def prefixEnd_1858584 : Nat := 4983230072969 + 3 ^ 40 * 1858584 * 2
def baseEnd_1858584 : Nat := 636231285837374343501689

theorem tailTrace_1858584 : CollatzResearch.WordTrace tailWord_1858584 prefixEnd_1858584 636231285837374343501689 := by
  unfold tailWord_1858584
  simp only [CollatzResearch.WordTrace]
  refine ⟨33894063749337531860571403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45192084999116709147428537 33894063749337531860571403)
  ·
    refine ⟨50841095624006297790857105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33894063749337531860571403 50841095624006297790857105)
    ·
      refine ⟨38130821718004723343142829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50841095624006297790857105 38130821718004723343142829)
      ·
        refine ⟨14299058144251771253678561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38130821718004723343142829 14299058144251771253678561)
        ·
          refine ⟨10724293608188828440258921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14299058144251771253678561 10724293608188828440258921)
          ·
            refine ⟨8043220206141621330194191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10724293608188828440258921 8043220206141621330194191)
            ·
              refine ⟨12064830309212431995291287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8043220206141621330194191 12064830309212431995291287)
              ·
                refine ⟨18097245463818647992936931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12064830309212431995291287 18097245463818647992936931)
                ·
                  refine ⟨27145868195727971989405397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18097245463818647992936931 27145868195727971989405397)
                  ·
                    refine ⟨636231285837374343501689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27145868195727971989405397 636231285837374343501689)
                    ·
                      rfl

theorem cell22_1858584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_1858584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858584 prefixEnd_1858584 := by exact prefixLift 1858584
  have htrace : WordTrace (prefixWord ++ tailWord_1858584) baseStart_1858584 baseEnd_1858584 := by
    simpa [prefixWord, tailWord_1858584, baseEnd_1858584] using wordTrace_append hprefix tailTrace_1858584
  have hstable : (prefixWord ++ tailWord_1858584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858584).length < 2 ^ (prefixWord ++ tailWord_1858584).sum := by decide
  have hdescent : baseEnd_1858584 < baseStart_1858584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858629 : List Nat := [1, 3, 1, 1, 1, 3, 2, 2, 3, 5]
def baseStart_1858629 : Nat := 118140960795 + 1858629 * 2 ^ 59
def prefixEnd_1858629 : Nat := 4983230072969 + 3 ^ 40 * 1858629 * 2
def baseEnd_1858629 : Nat := 636246690257009226126551

theorem tailTrace_1858629 : CollatzResearch.WordTrace tailWord_1858629 prefixEnd_1858629 636246690257009226126551 := by
  unfold tailWord_1858629
  simp only [CollatzResearch.WordTrace]
  refine ⟨67789768783512036406530941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45193179189008024271020627 67789768783512036406530941)
  ·
    refine ⟨25421163293817013652449103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67789768783512036406530941 25421163293817013652449103)
    ·
      refine ⟨38131744940725520478673655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25421163293817013652449103 38131744940725520478673655)
      ·
        refine ⟨57197617411088280718010483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38131744940725520478673655 57197617411088280718010483)
        ·
          refine ⟨85796426116632421077015725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57197617411088280718010483 85796426116632421077015725)
          ·
            refine ⟨32173659793737157903880897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85796426116632421077015725 32173659793737157903880897)
            ·
              refine ⟨24130244845302868427910673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32173659793737157903880897 24130244845302868427910673)
              ·
                refine ⟨18097683633977151320933005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24130244845302868427910673 18097683633977151320933005)
                ·
                  refine ⟨6786631362741431745349877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18097683633977151320933005 6786631362741431745349877)
                  ·
                    refine ⟨636246690257009226126551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6786631362741431745349877 636246690257009226126551)
                    ·
                      rfl

theorem cell22_1858629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_1858629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858629 prefixEnd_1858629 := by exact prefixLift 1858629
  have htrace : WordTrace (prefixWord ++ tailWord_1858629) baseStart_1858629 baseEnd_1858629 := by
    simpa [prefixWord, tailWord_1858629, baseEnd_1858629] using wordTrace_append hprefix tailTrace_1858629
  have hstable : (prefixWord ++ tailWord_1858629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858629).length < 2 ^ (prefixWord ++ tailWord_1858629).sum := by decide
  have hdescent : baseEnd_1858629 < baseStart_1858629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858631 : List Nat := [1, 1, 4, 1, 3, 3, 2, 1, 6]
def baseStart_1858631 : Nat := 118140960795 + 1858631 * 2 ^ 59
def prefixEnd_1858631 : Nat := 4983230072969 + 3 ^ 40 * 1858631 * 2
def baseEnd_1858631 : Nat := 212082458299293962525515

theorem tailTrace_1858631 : CollatzResearch.WordTrace tailWord_1858631 prefixEnd_1858631 212082458299293962525515 := by
  unfold tailWord_1858631
  simp only [CollatzResearch.WordTrace]
  refine ⟨67789841729504790748103747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45193227819669860498735831 67789841729504790748103747)
  ·
    refine ⟨101684762594257186122155621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67789841729504790748103747 101684762594257186122155621)
    ·
      refine ⟨19065892986423222397904179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101684762594257186122155621 19065892986423222397904179)
      ·
        refine ⟨28598839479634833596856269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19065892986423222397904179 28598839479634833596856269)
        ·
          refine ⟨10724564804863062598821101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28598839479634833596856269 10724564804863062598821101)
          ·
            refine ⟨4021711801823648474557913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10724564804863062598821101 4021711801823648474557913)
            ·
              refine ⟨3016283851367736355918435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4021711801823648474557913 3016283851367736355918435)
              ·
                refine ⟨4524425777051604533877653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3016283851367736355918435 4524425777051604533877653)
                ·
                  refine ⟨212082458299293962525515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4524425777051604533877653 212082458299293962525515)
                  ·
                    rfl

theorem cell22_1858631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 6].length) (baseStart_1858631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858631 prefixEnd_1858631 := by exact prefixLift 1858631
  have htrace : WordTrace (prefixWord ++ tailWord_1858631) baseStart_1858631 baseEnd_1858631 := by
    simpa [prefixWord, tailWord_1858631, baseEnd_1858631] using wordTrace_append hprefix tailTrace_1858631
  have hstable : (prefixWord ++ tailWord_1858631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858631).length < 2 ^ (prefixWord ++ tailWord_1858631).sum := by decide
  have hdescent : baseEnd_1858631 < baseStart_1858631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858661 : List Nat := [1, 3, 1, 3, 2, 1, 2, 3, 2, 4]
def baseStart_1858661 : Nat := 118140960795 + 1858661 * 2 ^ 59
def prefixEnd_1858661 : Nat := 4983230072969 + 3 ^ 40 * 1858661 * 2
def baseEnd_1858661 : Nat := 636257644510971809326453

theorem tailTrace_1858661 : CollatzResearch.WordTrace tailWord_1858661 prefixEnd_1858661 636257644510971809326453 := by
  unfold tailWord_1858661
  simp only [CollatzResearch.WordTrace]
  refine ⟨67790935919396105871695837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45193957279597403914463891 67790935919396105871695837)
  ·
    refine ⟨25421600969773539701885939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67790935919396105871695837 25421600969773539701885939)
    ·
      refine ⟨38132401454660309552828909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25421600969773539701885939 38132401454660309552828909)
      ·
        refine ⟨14299650545497616082310841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38132401454660309552828909 14299650545497616082310841)
        ·
          refine ⟨10724737909123212061733131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14299650545497616082310841 10724737909123212061733131)
          ·
            refine ⟨16087106863684818092599697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10724737909123212061733131 16087106863684818092599697)
            ·
              refine ⟨12065330147763613569449773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16087106863684818092599697 12065330147763613569449773)
              ·
                refine ⟨4524498805411355088543665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12065330147763613569449773 4524498805411355088543665)
                ·
                  refine ⟨3393374104058516316407749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4524498805411355088543665 3393374104058516316407749)
                  ·
                    refine ⟨636257644510971809326453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3393374104058516316407749 636257644510971809326453)
                    ·
                      rfl

theorem cell22_1858661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_1858661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858661 prefixEnd_1858661 := by exact prefixLift 1858661
  have htrace : WordTrace (prefixWord ++ tailWord_1858661) baseStart_1858661 baseEnd_1858661 := by
    simpa [prefixWord, tailWord_1858661, baseEnd_1858661] using wordTrace_append hprefix tailTrace_1858661
  have hstable : (prefixWord ++ tailWord_1858661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858661).length < 2 ^ (prefixWord ++ tailWord_1858661).sum := by decide
  have hdescent : baseEnd_1858661 < baseStart_1858661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858678 : List Nat := [5, 1, 1, 2, 1, 1, 3, 2, 2, 4]
def baseStart_1858678 : Nat := 118140960795 + 1858678 * 2 ^ 59
def prefixEnd_1858678 : Nat := 4983230072969 + 3 ^ 40 * 1858678 * 2
def baseEnd_1858678 : Nat := 636263463958389431651401

theorem tailTrace_1858678 : CollatzResearch.WordTrace tailWord_1858678 prefixEnd_1858678 636263463958389431651401 := by
  unfold tailWord_1858678
  simp only [CollatzResearch.WordTrace]
  refine ⟨4236972247520907360941543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45194370640223011850043125 4236972247520907360941543)
  ·
    refine ⟨6355458371281361041412315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4236972247520907360941543 6355458371281361041412315)
    ·
      refine ⟨9533187556922041562118473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6355458371281361041412315 9533187556922041562118473)
      ·
        refine ⟨7149890667691531171588855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9533187556922041562118473 7149890667691531171588855)
        ·
          refine ⟨10724836001537296757383283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7149890667691531171588855 10724836001537296757383283)
          ·
            refine ⟨16087254002305945136074925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10724836001537296757383283 16087254002305945136074925)
            ·
              refine ⟨6032720250864729426028097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16087254002305945136074925 6032720250864729426028097)
              ·
                refine ⟨4524540188148547069521073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6032720250864729426028097 4524540188148547069521073)
                ·
                  refine ⟨3393405141111410302140805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4524540188148547069521073 3393405141111410302140805)
                  ·
                    refine ⟨636263463958389431651401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3393405141111410302140805 636263463958389431651401)
                    ·
                      rfl

theorem cell22_1858678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_1858678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858678 prefixEnd_1858678 := by exact prefixLift 1858678
  have htrace : WordTrace (prefixWord ++ tailWord_1858678) baseStart_1858678 baseEnd_1858678 := by
    simpa [prefixWord, tailWord_1858678, baseEnd_1858678] using wordTrace_append hprefix tailTrace_1858678
  have hstable : (prefixWord ++ tailWord_1858678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858678).length < 2 ^ (prefixWord ++ tailWord_1858678).sum := by decide
  have hdescent : baseEnd_1858678 < baseStart_1858678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858704 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 9]
def baseStart_1858704 : Nat := 118140960795 + 1858704 * 2 ^ 59
def prefixEnd_1858704 : Nat := 4983230072969 + 3 ^ 40 * 1858704 * 2
def baseEnd_1858704 : Nat := 212090788096578010167107

theorem tailTrace_1858704 : CollatzResearch.WordTrace tailWord_1858704 prefixEnd_1858704 212090788096578010167107 := by
  unfold tailWord_1858704
  simp only [CollatzResearch.WordTrace]
  refine ⟨33896252129120162107755583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45195002838826882810340777 33896252129120162107755583)
  ·
    refine ⟨50844378193680243161633375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33896252129120162107755583 50844378193680243161633375)
    ·
      refine ⟨76266567290520364742450063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50844378193680243161633375 76266567290520364742450063)
      ·
        refine ⟨114399850935780547113675095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76266567290520364742450063 114399850935780547113675095)
        ·
          refine ⟨171599776403670820670512643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114399850935780547113675095 171599776403670820670512643)
          ·
            refine ⟨257399664605506231005768965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171599776403670820670512643 257399664605506231005768965)
            ·
              refine ⟨48262437113532418313581681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 257399664605506231005768965 48262437113532418313581681)
              ·
                refine ⟨36196827835149313735186261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48262437113532418313581681 36196827835149313735186261)
                ·
                  refine ⟨212090788096578010167107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 36196827835149313735186261 212090788096578010167107)
                  ·
                    rfl

theorem cell22_1858704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 9].length) (baseStart_1858704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858704 prefixEnd_1858704 := by exact prefixLift 1858704
  have htrace : WordTrace (prefixWord ++ tailWord_1858704) baseStart_1858704 baseEnd_1858704 := by
    simpa [prefixWord, tailWord_1858704, baseEnd_1858704] using wordTrace_append hprefix tailTrace_1858704
  have hstable : (prefixWord ++ tailWord_1858704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858704).length < 2 ^ (prefixWord ++ tailWord_1858704).sum := by decide
  have hdescent : baseEnd_1858704 < baseStart_1858704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858738 : List Nat := [3, 2, 1, 1, 1, 5, 2, 2, 5]
def baseStart_1858738 : Nat := 118140960795 + 1858738 * 2 ^ 59
def prefixEnd_1858738 : Nat := 4983230072969 + 3 ^ 40 * 1858738 * 2
def baseEnd_1858738 : Nat := 212094667728189758383739

theorem tailTrace_1858738 : CollatzResearch.WordTrace tailWord_1858738 prefixEnd_1858738 212094667728189758383739 := by
  unfold tailWord_1858738
  simp only [CollatzResearch.WordTrace]
  refine ⟨16948436085029287005562217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45195829560078098681499245 16948436085029287005562217)
  ·
    refine ⟨12711327063771965254171663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16948436085029287005562217 12711327063771965254171663)
    ·
      refine ⟨19066990595657947881257495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12711327063771965254171663 19066990595657947881257495)
      ·
        refine ⟨28600485893486921821886243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19066990595657947881257495 28600485893486921821886243)
        ·
          refine ⟨42900728840230382732829365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28600485893486921821886243 42900728840230382732829365)
          ·
            refine ⟨4021943328771598381202753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42900728840230382732829365 4021943328771598381202753)
            ·
              refine ⟨3016457496578698785902065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4021943328771598381202753 3016457496578698785902065)
              ·
                refine ⟨2262343122434024089426549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3016457496578698785902065 2262343122434024089426549)
                ·
                  refine ⟨212094667728189758383739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2262343122434024089426549 212094667728189758383739)
                  ·
                    rfl

theorem cell22_1858738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_1858738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858738 prefixEnd_1858738 := by exact prefixLift 1858738
  have htrace : WordTrace (prefixWord ++ tailWord_1858738) baseStart_1858738 baseEnd_1858738 := by
    simpa [prefixWord, tailWord_1858738, baseEnd_1858738] using wordTrace_append hprefix tailTrace_1858738
  have hstable : (prefixWord ++ tailWord_1858738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858738).length < 2 ^ (prefixWord ++ tailWord_1858738).sum := by decide
  have hdescent : baseEnd_1858738 < baseStart_1858738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858751 : List Nat := [1, 1, 2, 2, 2, 2, 3, 2, 3, 4]
def baseStart_1858751 : Nat := 118140960795 + 1858751 * 2 ^ 59
def prefixEnd_1858751 : Nat := 4983230072969 + 3 ^ 40 * 1858751 * 2
def baseEnd_1858751 : Nat := 636288453350241574576177

theorem tailTrace_1858751 : CollatzResearch.WordTrace tailWord_1858751 prefixEnd_1858751 636288453350241574576177 := by
  unfold tailWord_1858751
  simp only [CollatzResearch.WordTrace]
  refine ⟨67794218489070051242472107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45196145659380034161648071 67794218489070051242472107)
  ·
    refine ⟨101691327733605076863708161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67794218489070051242472107 101691327733605076863708161)
    ·
      refine ⟨76268495800203807647781121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101691327733605076863708161 76268495800203807647781121)
      ·
        refine ⟨57201371850152855735835841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76268495800203807647781121 57201371850152855735835841)
        ·
          refine ⟨42901028887614641801876881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57201371850152855735835841 42901028887614641801876881)
          ·
            refine ⟨32175771665710981351407661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42901028887614641801876881 32175771665710981351407661)
            ·
              refine ⟨12065914374641618006777873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32175771665710981351407661 12065914374641618006777873)
              ·
                refine ⟨9049435780981213505083405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12065914374641618006777873 9049435780981213505083405)
                ·
                  refine ⟨3393538417867955064406277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9049435780981213505083405 3393538417867955064406277)
                  ·
                    refine ⟨636288453350241574576177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3393538417867955064406277 636288453350241574576177)
                    ·
                      rfl

theorem cell22_1858751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 4].length) (baseStart_1858751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858751 prefixEnd_1858751 := by exact prefixLift 1858751
  have htrace : WordTrace (prefixWord ++ tailWord_1858751) baseStart_1858751 baseEnd_1858751 := by
    simpa [prefixWord, tailWord_1858751, baseEnd_1858751] using wordTrace_append hprefix tailTrace_1858751
  have hstable : (prefixWord ++ tailWord_1858751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858751).length < 2 ^ (prefixWord ++ tailWord_1858751).sum := by decide
  have hdescent : baseEnd_1858751 < baseStart_1858751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858753 : List Nat := [1, 2, 6, 1, 1, 1, 1, 1, 1, 7]
def baseStart_1858753 : Nat := 118140960795 + 1858753 * 2 ^ 59
def prefixEnd_1858753 : Nat := 4983230072969 + 3 ^ 40 * 1858753 * 2
def baseEnd_1858753 : Nat := 636289137991114236026171

theorem tailTrace_1858753 : CollatzResearch.WordTrace tailWord_1858753 prefixEnd_1858753 636289137991114236026171 := by
  unfold tailWord_1858753
  simp only [CollatzResearch.WordTrace]
  refine ⟨67794291435062805584044913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45196194290041870389363275 67794291435062805584044913)
  ·
    refine ⟨50845718576297104188033685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67794291435062805584044913 50845718576297104188033685)
    ·
      refine ⟨2383393058263926758814079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50845718576297104188033685 2383393058263926758814079)
      ·
        refine ⟨3575089587395890138221119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2383393058263926758814079 3575089587395890138221119)
        ·
          refine ⟨5362634381093835207331679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3575089587395890138221119 5362634381093835207331679)
          ·
            refine ⟨8043951571640752810997519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5362634381093835207331679 8043951571640752810997519)
            ·
              refine ⟨12065927357461129216496279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8043951571640752810997519 12065927357461129216496279)
              ·
                refine ⟨18098891036191693824744419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12065927357461129216496279 18098891036191693824744419)
                ·
                  refine ⟨27148336554287540737116629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18098891036191693824744419 27148336554287540737116629)
                  ·
                    refine ⟨636289137991114236026171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27148336554287540737116629 636289137991114236026171)
                    ·
                      rfl

theorem cell22_1858753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_1858753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858753 prefixEnd_1858753 := by exact prefixLift 1858753
  have htrace : WordTrace (prefixWord ++ tailWord_1858753) baseStart_1858753 baseEnd_1858753 := by
    simpa [prefixWord, tailWord_1858753, baseEnd_1858753] using wordTrace_append hprefix tailTrace_1858753
  have hstable : (prefixWord ++ tailWord_1858753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858753).length < 2 ^ (prefixWord ++ tailWord_1858753).sum := by decide
  have hdescent : baseEnd_1858753 < baseStart_1858753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858783 : List Nat := [1, 1, 2, 3, 2, 1, 3, 5, 4]
def baseStart_1858783 : Nat := 118140960795 + 1858783 * 2 ^ 59
def prefixEnd_1858783 : Nat := 4983230072969 + 3 ^ 40 * 1858783 * 2
def baseEnd_1858783 : Nat := 212099802534734719258693

theorem tailTrace_1858783 : CollatzResearch.WordTrace tailWord_1858783 prefixEnd_1858783 212099802534734719258693 := by
  unfold tailWord_1858783
  simp only [CollatzResearch.WordTrace]
  refine ⟨67795385624954120707637003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45196923749969413805091335 67795385624954120707637003)
  ·
    refine ⟨101693078437431181061455505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67795385624954120707637003 101693078437431181061455505)
    ·
      refine ⟨76269808828073385796091629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101693078437431181061455505 76269808828073385796091629)
      ·
        refine ⟨28601178310527519673534361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76269808828073385796091629 28601178310527519673534361)
        ·
          refine ⟨21450883732895639755150771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28601178310527519673534361 21450883732895639755150771)
          ·
            refine ⟨32176325599343459632726157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21450883732895639755150771 32176325599343459632726157)
            ·
              refine ⟨12066122099753797362272309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32176325599343459632726157 12066122099753797362272309)
              ·
                refine ⟨1131198946851918502713029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12066122099753797362272309 1131198946851918502713029)
                ·
                  refine ⟨212099802534734719258693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1131198946851918502713029 212099802534734719258693)
                  ·
                    rfl

theorem cell22_1858783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 5, 4].length) (baseStart_1858783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858783 prefixEnd_1858783 := by exact prefixLift 1858783
  have htrace : WordTrace (prefixWord ++ tailWord_1858783) baseStart_1858783 baseEnd_1858783 := by
    simpa [prefixWord, tailWord_1858783, baseEnd_1858783] using wordTrace_append hprefix tailTrace_1858783
  have hstable : (prefixWord ++ tailWord_1858783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858783).length < 2 ^ (prefixWord ++ tailWord_1858783).sum := by decide
  have hdescent : baseEnd_1858783 < baseStart_1858783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858785 : List Nat := [1, 2, 3, 1, 3, 2, 4, 1, 1, 4]
def baseStart_1858785 : Nat := 118140960795 + 1858785 * 2 ^ 59
def prefixEnd_1858785 : Nat := 4983230072969 + 3 ^ 40 * 1858785 * 2
def baseEnd_1858785 : Nat := 636300092245076819226073

theorem tailTrace_1858785 : CollatzResearch.WordTrace tailWord_1858785 prefixEnd_1858785 636300092245076819226073 := by
  unfold tailWord_1858785
  simp only [CollatzResearch.WordTrace]
  refine ⟨67795458570946875049209809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45196972380631250032806539 67795458570946875049209809)
  ·
    refine ⟨50846593928210156286907357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67795458570946875049209809 50846593928210156286907357)
    ·
      refine ⟨19067472723078808607590259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50846593928210156286907357 19067472723078808607590259)
      ·
        refine ⟨28601209084618212911385389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19067472723078808607590259 28601209084618212911385389)
        ·
          refine ⟨10725453406731829841769521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28601209084618212911385389 10725453406731829841769521)
          ·
            refine ⟨8044090055048872381327141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10725453406731829841769521 8044090055048872381327141)
            ·
              refine ⟨1508266885321663571498839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8044090055048872381327141 1508266885321663571498839)
              ·
                refine ⟨2262400327982495357248259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1508266885321663571498839 2262400327982495357248259)
                ·
                  refine ⟨3393600491973743035872389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2262400327982495357248259 3393600491973743035872389)
                  ·
                    refine ⟨636300092245076819226073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3393600491973743035872389 636300092245076819226073)
                    ·
                      rfl

theorem cell22_1858785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 1, 4].length) (baseStart_1858785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858785 prefixEnd_1858785 := by exact prefixLift 1858785
  have htrace : WordTrace (prefixWord ++ tailWord_1858785) baseStart_1858785 baseEnd_1858785 := by
    simpa [prefixWord, tailWord_1858785, baseEnd_1858785] using wordTrace_append hprefix tailTrace_1858785
  have hstable : (prefixWord ++ tailWord_1858785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858785).length < 2 ^ (prefixWord ++ tailWord_1858785).sum := by decide
  have hdescent : baseEnd_1858785 < baseStart_1858785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858826 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 1, 9]
def baseStart_1858826 : Nat := 118140960795 + 1858826 * 2 ^ 59
def prefixEnd_1858826 : Nat := 4983230072969 + 3 ^ 40 * 1858826 * 2
def baseEnd_1858826 : Nat := 636314127382966378950947

theorem tailTrace_1858826 : CollatzResearch.WordTrace tailWord_1858826 prefixEnd_1858826 636314127382966378950947 := by
  unfold tailWord_1858826
  simp only [CollatzResearch.WordTrace]
  refine ⟨16949238490949584762863083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45197969309198892700968221 16949238490949584762863083)
  ·
    refine ⟨25423857736424377144294625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16949238490949584762863083 25423857736424377144294625)
    ·
      refine ⟨19067893302318282858220969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25423857736424377144294625 19067893302318282858220969)
      ·
        refine ⟨14300919976738712143665727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19067893302318282858220969 14300919976738712143665727)
        ·
          refine ⟨21451379965108068215498591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14300919976738712143665727 21451379965108068215498591)
          ·
            refine ⟨32177069947662102323247887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21451379965108068215498591 32177069947662102323247887)
            ·
              refine ⟨48265604921493153484871831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32177069947662102323247887 48265604921493153484871831)
              ·
                refine ⟨72398407382239730227307747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48265604921493153484871831 72398407382239730227307747)
                ·
                  refine ⟨108597611073359595340961621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72398407382239730227307747 108597611073359595340961621)
                  ·
                    refine ⟨636314127382966378950947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 108597611073359595340961621 636314127382966378950947)
                    ·
                      rfl

theorem cell22_1858826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_1858826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858826 prefixEnd_1858826 := by exact prefixLift 1858826
  have htrace : WordTrace (prefixWord ++ tailWord_1858826) baseStart_1858826 baseEnd_1858826 := by
    simpa [prefixWord, tailWord_1858826, baseEnd_1858826] using wordTrace_append hprefix tailTrace_1858826
  have hstable : (prefixWord ++ tailWord_1858826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858826).length < 2 ^ (prefixWord ++ tailWord_1858826).sum := by decide
  have hdescent : baseEnd_1858826 < baseStart_1858826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858828 : List Nat := [2, 2, 1, 2, 2, 3, 4, 6]
def baseStart_1858828 : Nat := 118140960795 + 1858828 * 2 ^ 59
def prefixEnd_1858828 : Nat := 4983230072969 + 3 ^ 40 * 1858828 * 2
def baseEnd_1858828 : Nat := 70701645780426560044549

theorem tailTrace_1858828 : CollatzResearch.WordTrace tailWord_1858828 prefixEnd_1858828 70701645780426560044549 := by
  unfold tailWord_1858828
  simp only [CollatzResearch.WordTrace]
  refine ⟨33898513454895546696512569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45198017939860728928683425 33898513454895546696512569)
  ·
    refine ⟨25423885091171660022384427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33898513454895546696512569 25423885091171660022384427)
    ·
      refine ⟨38135827636757490033576641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25423885091171660022384427 38135827636757490033576641)
      ·
        refine ⟨28601870727568117525182481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38135827636757490033576641 28601870727568117525182481)
        ·
          refine ⟨21451403045676088143886861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28601870727568117525182481 21451403045676088143886861)
          ·
            refine ⟨8044276142128533053957573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21451403045676088143886861 8044276142128533053957573)
            ·
              refine ⟨1508301776649099947617045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8044276142128533053957573 1508301776649099947617045)
              ·
                refine ⟨70701645780426560044549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1508301776649099947617045 70701645780426560044549)
                ·
                  rfl

theorem cell22_1858828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 6].length) (baseStart_1858828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858828 prefixEnd_1858828 := by exact prefixLift 1858828
  have htrace : WordTrace (prefixWord ++ tailWord_1858828) baseStart_1858828 baseEnd_1858828 := by
    simpa [prefixWord, tailWord_1858828, baseEnd_1858828] using wordTrace_append hprefix tailTrace_1858828
  have hstable : (prefixWord ++ tailWord_1858828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858828).length < 2 ^ (prefixWord ++ tailWord_1858828).sum := by decide
  have hdescent : baseEnd_1858828 < baseStart_1858828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858952 : List Nat := [2, 1, 3, 3, 1, 3, 2, 3, 4]
def baseStart_1858952 : Nat := 118140960795 + 1858952 * 2 ^ 59
def prefixEnd_1858952 : Nat := 4983230072969 + 3 ^ 40 * 1858952 * 2
def baseEnd_1858952 : Nat := 212119086585981350100187

theorem tailTrace_1858952 : CollatzResearch.WordTrace tailWord_1858952 prefixEnd_1858952 212119086585981350100187 := by
  unfold tailWord_1858952
  simp only [CollatzResearch.WordTrace]
  refine ⟨33900774780670931285269555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45201033040894575047026073 33900774780670931285269555)
  ·
    refine ⟨50851162171006396927904333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33900774780670931285269555 50851162171006396927904333)
    ·
      refine ⟨19069185814127398847964125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50851162171006396927904333 19069185814127398847964125)
      ·
        refine ⟨7150944680297774567986547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19069185814127398847964125 7150944680297774567986547)
        ·
          refine ⟨10726417020446661851979821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7150944680297774567986547 10726417020446661851979821)
          ·
            refine ⟨4022406382667498194492433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10726417020446661851979821 4022406382667498194492433)
            ·
              refine ⟨3016804787000623645869325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4022406382667498194492433 3016804787000623645869325)
              ·
                refine ⟨1131301795125233867200997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3016804787000623645869325 1131301795125233867200997)
                ·
                  refine ⟨212119086585981350100187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1131301795125233867200997 212119086585981350100187)
                  ·
                    rfl

theorem cell22_1858952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 3, 4].length) (baseStart_1858952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858952 prefixEnd_1858952 := by exact prefixLift 1858952
  have htrace : WordTrace (prefixWord ++ tailWord_1858952) baseStart_1858952 baseEnd_1858952 := by
    simpa [prefixWord, tailWord_1858952, baseEnd_1858952] using wordTrace_append hprefix tailTrace_1858952
  have hstable : (prefixWord ++ tailWord_1858952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858952).length < 2 ^ (prefixWord ++ tailWord_1858952).sum := by decide
  have hdescent : baseEnd_1858952 < baseStart_1858952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858984 : List Nat := [2, 1, 6, 1, 2, 2, 1, 1, 1, 5]
def baseStart_1858984 : Nat := 118140960795 + 1858984 * 2 ^ 59
def prefixEnd_1858984 : Nat := 4983230072969 + 3 ^ 40 * 1858984 * 2
def baseEnd_1858984 : Nat := 636368214011906633500463

theorem tailTrace_1858984 : CollatzResearch.WordTrace tailWord_1858984 prefixEnd_1858984 636368214011906633500463 := by
  unfold tailWord_1858984
  simp only [CollatzResearch.WordTrace]
  refine ⟨33901358348612966017852003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45201811131483954690469337 33901358348612966017852003)
  ·
    refine ⟨50852037522919449026778005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33901358348612966017852003 50852037522919449026778005)
    ·
      refine ⟨2383689258886849173130219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50852037522919449026778005 2383689258886849173130219)
      ·
        refine ⟨3575533888330273759695329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2383689258886849173130219 3575533888330273759695329)
        ·
          refine ⟨2681650416247705319771497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3575533888330273759695329 2681650416247705319771497)
          ·
            refine ⟨2011237812185778989828623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2681650416247705319771497 2011237812185778989828623)
            ·
              refine ⟨3016856718278668484742935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2011237812185778989828623 3016856718278668484742935)
              ·
                refine ⟨4525285077418002727114403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3016856718278668484742935 4525285077418002727114403)
                ·
                  refine ⟨6787927616127004090671605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4525285077418002727114403 6787927616127004090671605)
                  ·
                    refine ⟨636368214011906633500463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6787927616127004090671605 636368214011906633500463)
                    ·
                      rfl

theorem cell22_1858984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_1858984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858984 prefixEnd_1858984 := by exact prefixLift 1858984
  have htrace : WordTrace (prefixWord ++ tailWord_1858984) baseStart_1858984 baseEnd_1858984 := by
    simpa [prefixWord, tailWord_1858984, baseEnd_1858984] using wordTrace_append hprefix tailTrace_1858984
  have hstable : (prefixWord ++ tailWord_1858984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858984).length < 2 ^ (prefixWord ++ tailWord_1858984).sum := by decide
  have hdescent : baseEnd_1858984 < baseStart_1858984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858997 : List Nat := [1, 3, 3, 2, 2, 3, 2, 6]
def baseStart_1858997 : Nat := 118140960795 + 1858997 * 2 ^ 59
def prefixEnd_1858997 : Nat := 4983230072969 + 3 ^ 40 * 1858997 * 2
def baseEnd_1858997 : Nat := 70708073797508770325047

theorem tailTrace_1858997 : CollatzResearch.WordTrace tailWord_1858997 prefixEnd_1858997 70708073797508770325047 := by
  unfold tailWord_1858997
  simp only [CollatzResearch.WordTrace]
  refine ⟨67803190846178835255927245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45202127230785890170618163 67803190846178835255927245)
  ·
    refine ⟨25426196567317063220972717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67803190846178835255927245 25426196567317063220972717)
    ·
      refine ⟨9534823712743898707864769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25426196567317063220972717 9534823712743898707864769)
      ·
        refine ⟨7151117784557924030898577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9534823712743898707864769 7151117784557924030898577)
        ·
          refine ⟨5363338338418443023173933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7151117784557924030898577 5363338338418443023173933)
          ·
            refine ⟨2011251876906916133690225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5363338338418443023173933 2011251876906916133690225)
            ·
              refine ⟨1508438907680187100267669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2011251876906916133690225 1508438907680187100267669)
              ·
                refine ⟨70708073797508770325047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1508438907680187100267669 70708073797508770325047)
                ·
                  rfl

theorem cell22_1858997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 6].length) (baseStart_1858997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1858997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1858997 prefixEnd_1858997 := by exact prefixLift 1858997
  have htrace : WordTrace (prefixWord ++ tailWord_1858997) baseStart_1858997 baseEnd_1858997 := by
    simpa [prefixWord, tailWord_1858997, baseEnd_1858997] using wordTrace_append hprefix tailTrace_1858997
  have hstable : (prefixWord ++ tailWord_1858997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858997).length < 2 ^ (prefixWord ++ tailWord_1858997).sum := by decide
  have hdescent : baseEnd_1858997 < baseStart_1858997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859008 : List Nat := [2, 1, 1, 2, 3, 1, 3, 2, 7]
def baseStart_1859008 : Nat := 118140960795 + 1859008 * 2 ^ 59
def prefixEnd_1859008 : Nat := 4983230072969 + 3 ^ 40 * 1859008 * 2
def baseEnd_1859008 : Nat := 212125476567459523633463

theorem tailTrace_1859008 : CollatzResearch.WordTrace tailWord_1859008 prefixEnd_1859008 212125476567459523633463 := by
  unfold tailWord_1859008
  simp only [CollatzResearch.WordTrace]
  refine ⟨33901796024569492067288839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45202394699425989423051785 33901796024569492067288839)
  ·
    refine ⟨50852694036854238100933259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33901796024569492067288839 50852694036854238100933259)
    ·
      refine ⟨76279041055281357151399889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50852694036854238100933259 76279041055281357151399889)
      ·
        refine ⟨57209280791461017863549917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76279041055281357151399889 57209280791461017863549917)
        ·
          refine ⟨21453480296797881698831219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57209280791461017863549917 21453480296797881698831219)
          ·
            refine ⟨32180220445196822548246829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21453480296797881698831219 32180220445196822548246829)
            ·
              refine ⟨12067582666948808455592561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32180220445196822548246829 12067582666948808455592561)
              ·
                refine ⟨9050687000211606341694421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12067582666948808455592561 9050687000211606341694421)
                ·
                  refine ⟨212125476567459523633463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9050687000211606341694421 212125476567459523633463)
                  ·
                    rfl

theorem cell22_1859008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 7].length) (baseStart_1859008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1859008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1859008 prefixEnd_1859008 := by exact prefixLift 1859008
  have htrace : WordTrace (prefixWord ++ tailWord_1859008) baseStart_1859008 baseEnd_1859008 := by
    simpa [prefixWord, tailWord_1859008, baseEnd_1859008] using wordTrace_append hprefix tailTrace_1859008
  have hstable : (prefixWord ++ tailWord_1859008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859008).length < 2 ^ (prefixWord ++ tailWord_1859008).sum := by decide
  have hdescent : baseEnd_1859008 < baseStart_1859008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859023 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 4, 5]
def baseStart_1859023 : Nat := 118140960795 + 1859023 * 2 ^ 59
def prefixEnd_1859023 : Nat := 4983230072969 + 3 ^ 40 * 1859023 * 2
def baseEnd_1859023 : Nat := 636381564508923531775343

theorem tailTrace_1859023 : CollatzResearch.WordTrace tailWord_1859023 prefixEnd_1859023 636381564508923531775343 := by
  unfold tailWord_1859023
  simp only [CollatzResearch.WordTrace]
  refine ⟨67804139144084641696373723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45202759429389761130915815 67804139144084641696373723)
  ·
    refine ⟨101706208716126962544560585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67804139144084641696373723 101706208716126962544560585)
    ·
      refine ⟨76279656537095221908420439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101706208716126962544560585 76279656537095221908420439)
      ·
        refine ⟨114419484805642832862630659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76279656537095221908420439 114419484805642832862630659)
        ·
          refine ⟨171629227208464249293945989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114419484805642832862630659 171629227208464249293945989)
          ·
            refine ⟨32180480101587046742614873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171629227208464249293945989 32180480101587046742614873)
            ·
              refine ⟨24135360076190285056961155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32180480101587046742614873 24135360076190285056961155)
              ·
                refine ⟨36203040114285427585441733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24135360076190285056961155 36203040114285427585441733)
                ·
                  refine ⟨6788070021428517672270325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36203040114285427585441733 6788070021428517672270325)
                  ·
                    refine ⟨636381564508923531775343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6788070021428517672270325 636381564508923531775343)
                    ·
                      rfl

theorem cell22_1859023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 5].length) (baseStart_1859023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1859023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1859023 prefixEnd_1859023 := by exact prefixLift 1859023
  have htrace : WordTrace (prefixWord ++ tailWord_1859023) baseStart_1859023 baseEnd_1859023 := by
    simpa [prefixWord, tailWord_1859023, baseEnd_1859023] using wordTrace_append hprefix tailTrace_1859023
  have hstable : (prefixWord ++ tailWord_1859023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859023).length < 2 ^ (prefixWord ++ tailWord_1859023).sum := by decide
  have hdescent : baseEnd_1859023 < baseStart_1859023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859100 : List Nat := [2, 2, 3, 1, 2, 1, 2, 2, 1, 6]
def baseStart_1859100 : Nat := 118140960795 + 1859100 * 2 ^ 59
def prefixEnd_1859100 : Nat := 4983230072969 + 3 ^ 40 * 1859100 * 2
def baseEnd_1859100 : Nat := 636407923182520997600107

theorem tailTrace_1859100 : CollatzResearch.WordTrace tailWord_1859100 prefixEnd_1859100 636407923182520997600107 := by
  unfold tailWord_1859100
  simp only [CollatzResearch.WordTrace]
  refine ⟨33903473782402841923463377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45204631709870455897951169 33903473782402841923463377)
  ·
    refine ⟨25427605336802131442597533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33903473782402841923463377 25427605336802131442597533)
    ·
      refine ⟨9535352001300799290974075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25427605336802131442597533 9535352001300799290974075)
      ·
        refine ⟨14303028001951198936461113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9535352001300799290974075 14303028001951198936461113)
        ·
          refine ⟨10727271001463399202345835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14303028001951198936461113 10727271001463399202345835)
          ·
            refine ⟨16090906502195098803518753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10727271001463399202345835 16090906502195098803518753)
            ·
              refine ⟨12068179876646324102639065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16090906502195098803518753 12068179876646324102639065)
              ·
                refine ⟨9051134907484743076979299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12068179876646324102639065 9051134907484743076979299)
                ·
                  refine ⟨13576702361227114615468949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9051134907484743076979299 13576702361227114615468949)
                  ·
                    refine ⟨636407923182520997600107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13576702361227114615468949 636407923182520997600107)
                    ·
                      rfl

theorem cell22_1859100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_1859100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1859100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1859100 prefixEnd_1859100 := by exact prefixLift 1859100
  have htrace : WordTrace (prefixWord ++ tailWord_1859100) baseStart_1859100 baseEnd_1859100 := by
    simpa [prefixWord, tailWord_1859100, baseEnd_1859100] using wordTrace_append hprefix tailTrace_1859100
  have hstable : (prefixWord ++ tailWord_1859100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859100).length < 2 ^ (prefixWord ++ tailWord_1859100).sum := by decide
  have hdescent : baseEnd_1859100 < baseStart_1859100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859164 : List Nat := [2, 2, 4, 1, 2, 1, 2, 2, 3, 3]
def baseStart_1859164 : Nat := 118140960795 + 1859164 * 2 ^ 59
def prefixEnd_1859164 : Nat := 4983230072969 + 3 ^ 40 * 1859164 * 2
def baseEnd_1859164 : Nat := 636429831690446163999911

theorem tailTrace_1859164 : CollatzResearch.WordTrace tailWord_1859164 prefixEnd_1859164 636429831690446163999911 := by
  unfold tailWord_1859164
  simp only [CollatzResearch.WordTrace]
  refine ⟨33904640918286911388628273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45206187891049215184837697 33904640918286911388628273)
  ·
    refine ⟨25428480688715183541471205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33904640918286911388628273 25428480688715183541471205)
    ·
      refine ⟨4767840129134096914025851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25428480688715183541471205 4767840129134096914025851)
      ·
        refine ⟨7151760193701145371038777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4767840129134096914025851 7151760193701145371038777)
        ·
          refine ⟨5363820145275859028279083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7151760193701145371038777 5363820145275859028279083)
          ·
            refine ⟨8045730217913788542418625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5363820145275859028279083 8045730217913788542418625)
            ·
              refine ⟨6034297663435341406813969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8045730217913788542418625 6034297663435341406813969)
              ·
                refine ⟨4525723247576506055110477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6034297663435341406813969 4525723247576506055110477)
                ·
                  refine ⟨1697146217841189770666429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4525723247576506055110477 1697146217841189770666429)
                  ·
                    refine ⟨636429831690446163999911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1697146217841189770666429 636429831690446163999911)
                    ·
                      rfl

theorem cell22_1859164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_1859164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1859164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1859164 prefixEnd_1859164 := by exact prefixLift 1859164
  have htrace : WordTrace (prefixWord ++ tailWord_1859164) baseStart_1859164 baseEnd_1859164 := by
    simpa [prefixWord, tailWord_1859164, baseEnd_1859164] using wordTrace_append hprefix tailTrace_1859164
  have hstable : (prefixWord ++ tailWord_1859164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859164).length < 2 ^ (prefixWord ++ tailWord_1859164).sum := by decide
  have hdescent : baseEnd_1859164 < baseStart_1859164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859175 : List Nat := [1, 1, 5, 1, 1, 1, 2, 2, 1, 7]
def baseStart_1859175 : Nat := 118140960795 + 1859175 * 2 ^ 59
def prefixEnd_1859175 : Nat := 4983230072969 + 3 ^ 40 * 1859175 * 2
def baseEnd_1859175 : Nat := 636433597215245801974877

theorem tailTrace_1859175 : CollatzResearch.WordTrace tailWord_1859175 prefixEnd_1859175 636433597215245801974877 := by
  unfold tailWord_1859175
  simp only [CollatzResearch.WordTrace]
  refine ⟨67809683039533971655906979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45206455359689314437271319 67809683039533971655906979)
  ·
    refine ⟨101714524559300957483860469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67809683039533971655906979 101714524559300957483860469)
    ·
      refine ⟨9535736677434464764111919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101714524559300957483860469 9535736677434464764111919)
      ·
        refine ⟨14303605016151697146167879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9535736677434464764111919 14303605016151697146167879)
        ·
          refine ⟨21455407524227545719251819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14303605016151697146167879 21455407524227545719251819)
          ·
            refine ⟨32183111286341318578877729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21455407524227545719251819 32183111286341318578877729)
            ·
              refine ⟨24137333464755988934158297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32183111286341318578877729 24137333464755988934158297)
              ·
                refine ⟨18103000098566991700618723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24137333464755988934158297 18103000098566991700618723)
                ·
                  refine ⟨27154500147850487550928085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18103000098566991700618723 27154500147850487550928085)
                  ·
                    refine ⟨636433597215245801974877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27154500147850487550928085 636433597215245801974877)
                    ·
                      rfl

theorem cell22_1859175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_1859175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1859175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1859175 prefixEnd_1859175 := by exact prefixLift 1859175
  have htrace : WordTrace (prefixWord ++ tailWord_1859175) baseStart_1859175 baseEnd_1859175 := by
    simpa [prefixWord, tailWord_1859175, baseEnd_1859175] using wordTrace_append hprefix tailTrace_1859175
  have hstable : (prefixWord ++ tailWord_1859175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859175).length < 2 ^ (prefixWord ++ tailWord_1859175).sum := by decide
  have hdescent : baseEnd_1859175 < baseStart_1859175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859224 : List Nat := [2, 1, 2, 4, 1, 2, 3, 2, 1, 4]
def baseStart_1859224 : Nat := 118140960795 + 1859224 * 2 ^ 59
def prefixEnd_1859224 : Nat := 4983230072969 + 3 ^ 40 * 1859224 * 2
def baseEnd_1859224 : Nat := 636450370916626007499727

theorem tailTrace_1859224 : CollatzResearch.WordTrace tailWord_1859224 prefixEnd_1859224 636450370916626007499727 := by
  unfold tailWord_1859224
  simp only [CollatzResearch.WordTrace]
  refine ⟨33905735108178226512220363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45207646810904302016293817 33905735108178226512220363)
  ·
    refine ⟨50858602662267339768330545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33905735108178226512220363 50858602662267339768330545)
    ·
      refine ⟨38143951996700504826247909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50858602662267339768330545 38143951996700504826247909)
      ·
        refine ⟨7151990999381344654921483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38143951996700504826247909 7151990999381344654921483)
        ·
          refine ⟨10727986499072016982382225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7151990999381344654921483 10727986499072016982382225)
          ·
            refine ⟨8045989874304012736786669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10727986499072016982382225 8045989874304012736786669)
            ·
              refine ⟨3017246202864004776295001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8045989874304012736786669 3017246202864004776295001)
              ·
                refine ⟨2262934652148003582221251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3017246202864004776295001 2262934652148003582221251)
                ·
                  refine ⟨3394401978222005373331877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2262934652148003582221251 3394401978222005373331877)
                  ·
                    refine ⟨636450370916626007499727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3394401978222005373331877 636450370916626007499727)
                    ·
                      rfl

theorem cell22_1859224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 1, 4].length) (baseStart_1859224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1859224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1859224 prefixEnd_1859224 := by exact prefixLift 1859224
  have htrace : WordTrace (prefixWord ++ tailWord_1859224) baseStart_1859224 baseEnd_1859224 := by
    simpa [prefixWord, tailWord_1859224, baseEnd_1859224] using wordTrace_append hprefix tailTrace_1859224
  have hstable : (prefixWord ++ tailWord_1859224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859224).length < 2 ^ (prefixWord ++ tailWord_1859224).sum := by decide
  have hdescent : baseEnd_1859224 < baseStart_1859224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859237 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 6, 3]
def baseStart_1859237 : Nat := 118140960795 + 1859237 * 2 ^ 59
def prefixEnd_1859237 : Nat := 4983230072969 + 3 ^ 40 * 1859237 * 2
def baseEnd_1859237 : Nat := 636454821082298306924687

theorem tailTrace_1859237 : CollatzResearch.WordTrace tailWord_1859237 prefixEnd_1859237 636454821082298306924687 := by
  unfold tailWord_1859237
  simp only [CollatzResearch.WordTrace]
  refine ⟨67811944365309356244663965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45207962910206237496442643 67811944365309356244663965)
  ·
    refine ⟨25429479136991008591748987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67811944365309356244663965 25429479136991008591748987)
    ·
      refine ⟨38144218705486512887623481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25429479136991008591748987 38144218705486512887623481)
      ·
        refine ⟨28608164029114884665717611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38144218705486512887623481 28608164029114884665717611)
        ·
          refine ⟨42912246043672326998576417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28608164029114884665717611 42912246043672326998576417)
          ·
            refine ⟨32184184532754245248932313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42912246043672326998576417 32184184532754245248932313)
            ·
              refine ⟨24138138399565683936699235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32184184532754245248932313 24138138399565683936699235)
              ·
                refine ⟨36207207599348525905048853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24138138399565683936699235 36207207599348525905048853)
                ·
                  refine ⟨1697212856219462151799165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36207207599348525905048853 1697212856219462151799165)
                  ·
                    refine ⟨636454821082298306924687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1697212856219462151799165 636454821082298306924687)
                    ·
                      rfl

theorem cell22_1859237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 6, 3].length) (baseStart_1859237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1859237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1859237 prefixEnd_1859237 := by exact prefixLift 1859237
  have htrace : WordTrace (prefixWord ++ tailWord_1859237) baseStart_1859237 baseEnd_1859237 := by
    simpa [prefixWord, tailWord_1859237, baseEnd_1859237] using wordTrace_append hprefix tailTrace_1859237
  have hstable : (prefixWord ++ tailWord_1859237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859237).length < 2 ^ (prefixWord ++ tailWord_1859237).sum := by decide
  have hdescent : baseEnd_1859237 < baseStart_1859237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859312 : List Nat := [2, 1, 1, 1, 3, 1, 2, 6, 5]
def baseStart_1859312 : Nat := 118140960795 + 1859312 * 2 ^ 59
def prefixEnd_1859312 : Nat := 4983230072969 + 3 ^ 40 * 1859312 * 2
def baseEnd_1859312 : Nat := 212160165038341037099819

theorem tailTrace_1859312 : CollatzResearch.WordTrace tailWord_1859312 prefixEnd_1859312 212160165038341037099819 := by
  unfold tailWord_1859312
  simp only [CollatzResearch.WordTrace]
  refine ⟨33907339920018822026822095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45209786560025096035762793 33907339920018822026822095)
  ·
    refine ⟨50861009880028233040233143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33907339920018822026822095 50861009880028233040233143)
    ·
      refine ⟨76291514820042349560349715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50861009880028233040233143 76291514820042349560349715)
      ·
        refine ⟨114437272230063524340524573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76291514820042349560349715 114437272230063524340524573)
        ·
          refine ⟨42913977086273821627696715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114437272230063524340524573 42913977086273821627696715)
          ·
            refine ⟨64370965629410732441545073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42913977086273821627696715 64370965629410732441545073)
            ·
              refine ⟨48278224222058049331158805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64370965629410732441545073 48278224222058049331158805)
              ·
                refine ⟨2263041760408971062398069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48278224222058049331158805 2263041760408971062398069)
                ·
                  refine ⟨212160165038341037099819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2263041760408971062398069 212160165038341037099819)
                  ·
                    rfl

theorem cell22_1859312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 5].length) (baseStart_1859312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1859312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1859312 prefixEnd_1859312 := by exact prefixLift 1859312
  have htrace : WordTrace (prefixWord ++ tailWord_1859312) baseStart_1859312 baseEnd_1859312 := by
    simpa [prefixWord, tailWord_1859312, baseEnd_1859312] using wordTrace_append hprefix tailTrace_1859312
  have hstable : (prefixWord ++ tailWord_1859312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859312).length < 2 ^ (prefixWord ++ tailWord_1859312).sum := by decide
  have hdescent : baseEnd_1859312 < baseStart_1859312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859327 : List Nat := [1, 1, 2, 2, 1, 3, 4, 1, 2, 5]
def baseStart_1859327 : Nat := 118140960795 + 1859327 * 2 ^ 59
def prefixEnd_1859327 : Nat := 4983230072969 + 3 ^ 40 * 1859327 * 2
def baseEnd_1859327 : Nat := 636485629921568072174411

theorem tailTrace_1859327 : CollatzResearch.WordTrace tailWord_1859327 prefixEnd_1859327 636485629921568072174411 := by
  unfold tailWord_1859327
  simp only [CollatzResearch.WordTrace]
  refine ⟨67815226934983301615440235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45210151289988867743626823 67815226934983301615440235)
  ·
    refine ⟨101722840402474952423160353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67815226934983301615440235 101722840402474952423160353)
    ·
      refine ⟨76292130301856214317370265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101722840402474952423160353 76292130301856214317370265)
      ·
        refine ⟨57219097726392160738027699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76292130301856214317370265 57219097726392160738027699)
        ·
          refine ⟨85828646589588241107041549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57219097726392160738027699 85828646589588241107041549)
          ·
            refine ⟨32185742471095590415140581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85828646589588241107041549 32185742471095590415140581)
            ·
              refine ⟨6034826713330423202838859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32185742471095590415140581 6034826713330423202838859)
              ·
                refine ⟨9052240069995634804258289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6034826713330423202838859 9052240069995634804258289)
                ·
                  refine ⟨6789180052496726103193717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9052240069995634804258289 6789180052496726103193717)
                  ·
                    refine ⟨636485629921568072174411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6789180052496726103193717 636485629921568072174411)
                    ·
                      rfl

theorem cell22_1859327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 5].length) (baseStart_1859327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1859327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1859327 prefixEnd_1859327 := by exact prefixLift 1859327
  have htrace : WordTrace (prefixWord ++ tailWord_1859327) baseStart_1859327 baseEnd_1859327 := by
    simpa [prefixWord, tailWord_1859327, baseEnd_1859327] using wordTrace_append hprefix tailTrace_1859327
  have hstable : (prefixWord ++ tailWord_1859327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859327).length < 2 ^ (prefixWord ++ tailWord_1859327).sum := by decide
  have hdescent : baseEnd_1859327 < baseStart_1859327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859359 : List Nat := [1, 1, 2, 4, 2, 1, 1, 5, 1, 4]
def baseStart_1859359 : Nat := 118140960795 + 1859359 * 2 ^ 59
def prefixEnd_1859359 : Nat := 4983230072969 + 3 ^ 40 * 1859359 * 2
def baseEnd_1859359 : Nat := 636496584175530655374313

theorem tailTrace_1859359 : CollatzResearch.WordTrace tailWord_1859359 prefixEnd_1859359 636496584175530655374313 := by
  unfold tailWord_1859359
  simp only [CollatzResearch.WordTrace]
  refine ⟨67816394070867371080605131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45210929380578247387070087 67816394070867371080605131)
  ·
    refine ⟨101724591106301056620907697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67816394070867371080605131 101724591106301056620907697)
    ·
      refine ⟨76293443329725792465680773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101724591106301056620907697 76293443329725792465680773)
      ·
        refine ⟨14305020624323586087315145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76293443329725792465680773 14305020624323586087315145)
        ·
          refine ⟨10728765468242689565486359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14305020624323586087315145 10728765468242689565486359)
          ·
            refine ⟨16093148202364034348229539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10728765468242689565486359 16093148202364034348229539)
            ·
              refine ⟨24139722303546051522344309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16093148202364034348229539 24139722303546051522344309)
              ·
                refine ⟨2263098965957442330219779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24139722303546051522344309 2263098965957442330219779)
                ·
                  refine ⟨3394648448936163495329669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2263098965957442330219779 3394648448936163495329669)
                  ·
                    refine ⟨636496584175530655374313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3394648448936163495329669 636496584175530655374313)
                    ·
                      rfl

theorem cell22_1859359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 4].length) (baseStart_1859359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1859359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1859359 prefixEnd_1859359 := by exact prefixLift 1859359
  have htrace : WordTrace (prefixWord ++ tailWord_1859359) baseStart_1859359 baseEnd_1859359 := by
    simpa [prefixWord, tailWord_1859359, baseEnd_1859359] using wordTrace_append hprefix tailTrace_1859359
  have hstable : (prefixWord ++ tailWord_1859359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859359).length < 2 ^ (prefixWord ++ tailWord_1859359).sum := by decide
  have hdescent : baseEnd_1859359 < baseStart_1859359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859402 : List Nat := [3, 1, 2, 1, 1, 1, 3, 10]
def baseStart_1859402 : Nat := 118140960795 + 1859402 * 2 ^ 59
def prefixEnd_1859402 : Nat := 4983230072969 + 3 ^ 40 * 1859402 * 2
def baseEnd_1859402 : Nat := 70723478217143652949909

theorem tailTrace_1859402 : CollatzResearch.WordTrace tailWord_1859402 prefixEnd_1859402 70723478217143652949909 := by
  unfold tailWord_1859402
  simp only [CollatzResearch.WordTrace]
  refine ⟨16954490602427897356105115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45211974939807726282946973 16954490602427897356105115)
  ·
    refine ⟨25431735903641846034157673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16954490602427897356105115 25431735903641846034157673)
    ·
      refine ⟨19073801927731384525618255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25431735903641846034157673 19073801927731384525618255)
      ·
        refine ⟨28610702891597076788427383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19073801927731384525618255 28610702891597076788427383)
        ·
          refine ⟨42916054337395615182641075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28610702891597076788427383 42916054337395615182641075)
          ·
            refine ⟨64374081506093422773961613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42916054337395615182641075 64374081506093422773961613)
            ·
              refine ⟨24140280564785033540235605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64374081506093422773961613 24140280564785033540235605)
              ·
                refine ⟨70723478217143652949909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 24140280564785033540235605 70723478217143652949909)
                ·
                  rfl

theorem cell22_1859402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 10].length) (baseStart_1859402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1859402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1859402 prefixEnd_1859402 := by exact prefixLift 1859402
  have htrace : WordTrace (prefixWord ++ tailWord_1859402) baseStart_1859402 baseEnd_1859402 := by
    simpa [prefixWord, tailWord_1859402, baseEnd_1859402] using wordTrace_append hprefix tailTrace_1859402
  have hstable : (prefixWord ++ tailWord_1859402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859402).length < 2 ^ (prefixWord ++ tailWord_1859402).sum := by decide
  have hdescent : baseEnd_1859402 < baseStart_1859402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859447 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 11]
def baseStart_1859447 : Nat := 118140960795 + 1859447 * 2 ^ 59
def prefixEnd_1859447 : Nat := 4983230072969 + 3 ^ 40 * 1859447 * 2
def baseEnd_1859447 : Nat := 212175569457975919724681

theorem tailTrace_1859447 : CollatzResearch.WordTrace tailWord_1859447 prefixEnd_1859447 212175569457975919724681 := by
  unfold tailWord_1859447
  simp only [CollatzResearch.WordTrace]
  refine ⟨67819603694548562109808595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45213069129699041406539063 67819603694548562109808595)
  ·
    refine ⟨101729405541822843164712893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67819603694548562109808595 101729405541822843164712893)
    ·
      refine ⟨38148527078183566186767335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101729405541822843164712893 38148527078183566186767335)
      ·
        refine ⟨57222790617275349280151003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38148527078183566186767335 57222790617275349280151003)
        ·
          refine ⟨85834185925913023920226505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57222790617275349280151003 85834185925913023920226505)
          ·
            refine ⟨64375639444434767940169879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85834185925913023920226505 64375639444434767940169879)
            ·
              refine ⟨96563459166652151910254819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64375639444434767940169879 96563459166652151910254819)
              ·
                refine ⟨144845188749978227865382229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96563459166652151910254819 144845188749978227865382229)
                ·
                  refine ⟨212175569457975919724681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 144845188749978227865382229 212175569457975919724681)
                  ·
                    rfl

theorem cell22_1859447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 11].length) (baseStart_1859447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1859447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1859447 prefixEnd_1859447 := by exact prefixLift 1859447
  have htrace : WordTrace (prefixWord ++ tailWord_1859447) baseStart_1859447 baseEnd_1859447 := by
    simpa [prefixWord, tailWord_1859447, baseEnd_1859447] using wordTrace_append hprefix tailTrace_1859447
  have hstable : (prefixWord ++ tailWord_1859447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859447).length < 2 ^ (prefixWord ++ tailWord_1859447).sum := by decide
  have hdescent : baseEnd_1859447 < baseStart_1859447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859479 : List Nat := [1, 1, 3, 3, 1, 3, 1, 2, 2, 5]
def baseStart_1859479 : Nat := 118140960795 + 1859479 * 2 ^ 59
def prefixEnd_1859479 : Nat := 4983230072969 + 3 ^ 40 * 1859479 * 2
def baseEnd_1859479 : Nat := 636537662627890342373945

theorem tailTrace_1859479 : CollatzResearch.WordTrace tailWord_1859479 prefixEnd_1859479 636537662627890342373945 := by
  unfold tailWord_1859479
  simp only [CollatzResearch.WordTrace]
  refine ⟨67820770830432631574973491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45213847220288421049982327 67820770830432631574973491)
  ·
    refine ⟨101731156245648947362460237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67820770830432631574973491 101731156245648947362460237)
    ·
      refine ⟨38149183592118355260922589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101731156245648947362460237 38149183592118355260922589)
      ·
        refine ⟨14305943847044383222845971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38149183592118355260922589 14305943847044383222845971)
        ·
          refine ⟨21458915770566574834268957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14305943847044383222845971 21458915770566574834268957)
          ·
            refine ⟨8047093413962465562850859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21458915770566574834268957 8047093413962465562850859)
            ·
              refine ⟨12070640120943698344276289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8047093413962465562850859 12070640120943698344276289)
              ·
                refine ⟨9052980090707773758207217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12070640120943698344276289 9052980090707773758207217)
                ·
                  refine ⟨6789735068030830318655413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9052980090707773758207217 6789735068030830318655413)
                  ·
                    refine ⟨636537662627890342373945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6789735068030830318655413 636537662627890342373945)
                    ·
                      rfl

theorem cell22_1859479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_1859479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1859479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1859479 prefixEnd_1859479 := by exact prefixLift 1859479
  have htrace : WordTrace (prefixWord ++ tailWord_1859479) baseStart_1859479 baseEnd_1859479 := by
    simpa [prefixWord, tailWord_1859479, baseEnd_1859479] using wordTrace_append hprefix tailTrace_1859479
  have hstable : (prefixWord ++ tailWord_1859479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859479).length < 2 ^ (prefixWord ++ tailWord_1859479).sum := by decide
  have hdescent : baseEnd_1859479 < baseStart_1859479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859543 : List Nat := [1, 1, 3, 2, 1, 1, 7, 2, 4]
def baseStart_1859543 : Nat := 118140960795 + 1859543 * 2 ^ 59
def prefixEnd_1859543 : Nat := 4983230072969 + 3 ^ 40 * 1859543 * 2
def baseEnd_1859543 : Nat := 212186523711938502924583

theorem tailTrace_1859543 : CollatzResearch.WordTrace tailWord_1859543 prefixEnd_1859543 212186523711938502924583 := by
  unfold tailWord_1859543
  simp only [CollatzResearch.WordTrace]
  refine ⟨67823105102200770505303283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45215403401467180336868855 67823105102200770505303283)
  ·
    refine ⟨101734657653301155757954925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67823105102200770505303283 101734657653301155757954925)
    ·
      refine ⟨38150496619987933409233097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101734657653301155757954925 38150496619987933409233097)
      ·
        refine ⟨28612872464990950056924823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38150496619987933409233097 28612872464990950056924823)
        ·
          refine ⟨42919308697486425085387235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28612872464990950056924823 42919308697486425085387235)
          ·
            refine ⟨64378963046229637628080853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42919308697486425085387235 64378963046229637628080853)
            ·
              refine ⟨1508881946396007131908145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 64378963046229637628080853 1508881946396007131908145)
              ·
                refine ⟨1131661459797005348931109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1508881946396007131908145 1131661459797005348931109)
                ·
                  refine ⟨212186523711938502924583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1131661459797005348931109 212186523711938502924583)
                  ·
                    rfl

theorem cell22_1859543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 2, 4].length) (baseStart_1859543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1859543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1859543 prefixEnd_1859543 := by exact prefixLift 1859543
  have htrace : WordTrace (prefixWord ++ tailWord_1859543) baseStart_1859543 baseEnd_1859543 := by
    simpa [prefixWord, tailWord_1859543, baseEnd_1859543] using wordTrace_append hprefix tailTrace_1859543
  have hstable : (prefixWord ++ tailWord_1859543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859543).length < 2 ^ (prefixWord ++ tailWord_1859543).sum := by decide
  have hdescent : baseEnd_1859543 < baseStart_1859543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859588 : List Nat := [2, 3, 2, 4, 2, 9]
def baseStart_1859588 : Nat := 118140960795 + 1859588 * 2 ^ 59
def prefixEnd_1859588 : Nat := 4983230072969 + 3 ^ 40 * 1859588 * 2
def baseEnd_1859588 : Nat := 7858950315499387548131

theorem tailTrace_1859588 : CollatzResearch.WordTrace tailWord_1859588 prefixEnd_1859588 7858950315499387548131 := by
  unfold tailWord_1859588
  simp only [CollatzResearch.WordTrace]
  refine ⟨33912373193518871595345709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45216497591358495460460945 33912373193518871595345709)
  ·
    refine ⟨12717139947569576848254641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33912373193518871595345709 12717139947569576848254641)
    ·
      refine ⟨9537854960677182636190981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12717139947569576848254641 9537854960677182636190981)
      ·
        refine ⟨1788347805126971744285809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9537854960677182636190981 1788347805126971744285809)
        ·
          refine ⟨1341260853845228808214357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1788347805126971744285809 1341260853845228808214357)
          ·
            refine ⟨7858950315499387548131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1341260853845228808214357 7858950315499387548131)
            ·
              rfl

theorem cell22_1859588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 9].length) (baseStart_1859588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1859588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1859588 prefixEnd_1859588 := by exact prefixLift 1859588
  have htrace : WordTrace (prefixWord ++ tailWord_1859588) baseStart_1859588 baseEnd_1859588 := by
    simpa [prefixWord, tailWord_1859588, baseEnd_1859588] using wordTrace_append hprefix tailTrace_1859588
  have hstable : (prefixWord ++ tailWord_1859588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859588).length < 2 ^ (prefixWord ++ tailWord_1859588).sum := by decide
  have hdescent : baseEnd_1859588 < baseStart_1859588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859620 : List Nat := [2, 3, 1, 4, 2, 1, 1, 2, 3, 3]
def baseStart_1859620 : Nat := 118140960795 + 1859620 * 2 ^ 59
def prefixEnd_1859620 : Nat := 4983230072969 + 3 ^ 40 * 1859620 * 2
def baseEnd_1859620 : Nat := 636585929809412974598513

theorem tailTrace_1859620 : CollatzResearch.WordTrace tailWord_1859620 prefixEnd_1859620 636585929809412974598513 := by
  unfold tailWord_1859620
  simp only [CollatzResearch.WordTrace]
  refine ⟨33912956761460906327928157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45217275681947875103904209 33912956761460906327928157)
  ·
    refine ⟨12717358785547839872973059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33912956761460906327928157 12717358785547839872973059)
    ·
      refine ⟨19076038178321759809459589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12717358785547839872973059 19076038178321759809459589)
      ·
        refine ⟨3576757158435329964273673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19076038178321759809459589 3576757158435329964273673)
        ·
          refine ⟨2682567868826497473205255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3576757158435329964273673 2682567868826497473205255)
          ·
            refine ⟨4023851803239746209807883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2682567868826497473205255 4023851803239746209807883)
            ·
              refine ⟨6035777704859619314711825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4023851803239746209807883 6035777704859619314711825)
              ·
                refine ⟨4526833278644714486033869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6035777704859619314711825 4526833278644714486033869)
                ·
                  refine ⟨1697562479491767932262701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4526833278644714486033869 1697562479491767932262701)
                  ·
                    refine ⟨636585929809412974598513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1697562479491767932262701 636585929809412974598513)
                    ·
                      rfl

theorem cell22_1859620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_1859620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1859620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1859620 prefixEnd_1859620 := by exact prefixLift 1859620
  have htrace : WordTrace (prefixWord ++ tailWord_1859620) baseStart_1859620 baseEnd_1859620 := by
    simpa [prefixWord, tailWord_1859620, baseEnd_1859620] using wordTrace_append hprefix tailTrace_1859620
  have hstable : (prefixWord ++ tailWord_1859620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859620).length < 2 ^ (prefixWord ++ tailWord_1859620).sum := by decide
  have hdescent : baseEnd_1859620 < baseStart_1859620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859693 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 6, 3]
def baseStart_1859693 : Nat := 118140960795 + 1859693 * 2 ^ 59
def prefixEnd_1859693 : Nat := 4983230072969 + 3 ^ 40 * 1859693 * 2
def baseEnd_1859693 : Nat := 636610919201265117523289

theorem tailTrace_1859693 : CollatzResearch.WordTrace tailWord_1859693 prefixEnd_1859693 636610919201265117523289 := by
  unfold tailWord_1859693
  simp only [CollatzResearch.WordTrace]
  refine ⟨67828576051657346123263733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45219050701104897415509155 67828576051657346123263733)
  ·
    refine ⟨6358929004842876199055975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67828576051657346123263733 6358929004842876199055975)
    ·
      refine ⟨9538393507264314298583963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6358929004842876199055975 9538393507264314298583963)
      ·
        refine ⟨14307590260896471447875945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9538393507264314298583963 14307590260896471447875945)
        ·
          refine ⟨10730692695672353585906959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14307590260896471447875945 10730692695672353585906959)
          ·
            refine ⟨16096039043508530378860439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10730692695672353585906959 16096039043508530378860439)
            ·
              refine ⟨24144058565262795568290659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16096039043508530378860439 24144058565262795568290659)
              ·
                refine ⟨36216087847894193352435989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24144058565262795568290659 36216087847894193352435989)
                ·
                  refine ⟨1697629117870040313395437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36216087847894193352435989 1697629117870040313395437)
                  ·
                    refine ⟨636610919201265117523289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1697629117870040313395437 636610919201265117523289)
                    ·
                      rfl

theorem cell22_1859693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_1859693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1859693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1859693 prefixEnd_1859693 := by exact prefixLift 1859693
  have htrace : WordTrace (prefixWord ++ tailWord_1859693) baseStart_1859693 baseEnd_1859693 := by
    simpa [prefixWord, tailWord_1859693, baseEnd_1859693] using wordTrace_append hprefix tailTrace_1859693
  have hstable : (prefixWord ++ tailWord_1859693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859693).length < 2 ^ (prefixWord ++ tailWord_1859693).sum := by decide
  have hdescent : baseEnd_1859693 < baseStart_1859693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859695 : List Nat := [1, 1, 2, 1, 3, 6, 1, 3, 4]
def baseStart_1859695 : Nat := 118140960795 + 1859695 * 2 ^ 59
def prefixEnd_1859695 : Nat := 4983230072969 + 3 ^ 40 * 1859695 * 2
def baseEnd_1859695 : Nat := 212203867947379259657761

theorem tailTrace_1859695 : CollatzResearch.WordTrace tailWord_1859695 prefixEnd_1859695 212203867947379259657761 := by
  unfold tailWord_1859695
  simp only [CollatzResearch.WordTrace]
  refine ⟨67828648997650100464836539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45219099331766733643224359 67828648997650100464836539)
  ·
    refine ⟨101742973496475150697254809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67828648997650100464836539 101742973496475150697254809)
    ·
      refine ⟨76307230122356363022941107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101742973496475150697254809 76307230122356363022941107)
      ·
        refine ⟨114460845183534544534411661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76307230122356363022941107 114460845183534544534411661)
        ·
          refine ⟨42922816943825454200404373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114460845183534544534411661 42922816943825454200404373)
          ·
            refine ⟨2012007044241818165643955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42922816943825454200404373 2012007044241818165643955)
            ·
              refine ⟨3018010566362727248465933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2012007044241818165643955 3018010566362727248465933)
              ·
                refine ⟨1131753962386022718174725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3018010566362727248465933 1131753962386022718174725)
                ·
                  refine ⟨212203867947379259657761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1131753962386022718174725 212203867947379259657761)
                  ·
                    rfl

theorem cell22_1859695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 3, 4].length) (baseStart_1859695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1859695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1859695 prefixEnd_1859695 := by exact prefixLift 1859695
  have htrace : WordTrace (prefixWord ++ tailWord_1859695) baseStart_1859695 baseEnd_1859695 := by
    simpa [prefixWord, tailWord_1859695, baseEnd_1859695] using wordTrace_append hprefix tailTrace_1859695
  have hstable : (prefixWord ++ tailWord_1859695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859695).length < 2 ^ (prefixWord ++ tailWord_1859695).sum := by decide
  have hdescent : baseEnd_1859695 < baseStart_1859695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859708 : List Nat := [2, 2, 2, 1, 1, 5, 1, 2, 2, 4]
def baseStart_1859708 : Nat := 118140960795 + 1859708 * 2 ^ 59
def prefixEnd_1859708 : Nat := 4983230072969 + 3 ^ 40 * 1859708 * 2
def baseEnd_1859708 : Nat := 636616054007810078398243

theorem tailTrace_1859708 : CollatzResearch.WordTrace tailWord_1859708 prefixEnd_1859708 636616054007810078398243 := by
  unfold tailWord_1859708
  simp only [CollatzResearch.WordTrace]
  refine ⟨33914561573301501842529889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45219415431068669123373185 33914561573301501842529889)
  ·
    refine ⟨25435921179976126381897417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33914561573301501842529889 25435921179976126381897417)
    ·
      refine ⟨19076940884982094786423063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25435921179976126381897417 19076940884982094786423063)
      ·
        refine ⟨28615411327473142179634595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19076940884982094786423063 28615411327473142179634595)
        ·
          refine ⟨42923116991209713269451893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28615411327473142179634595 42923116991209713269451893)
          ·
            refine ⟨4024042217925910619011115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42923116991209713269451893 4024042217925910619011115)
            ·
              refine ⟨6036063326888865928516673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4024042217925910619011115 6036063326888865928516673)
              ·
                refine ⟨4527047495166649446387505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6036063326888865928516673 4527047495166649446387505)
                ·
                  refine ⟨3395285621374987084790629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4527047495166649446387505 3395285621374987084790629)
                  ·
                    refine ⟨636616054007810078398243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3395285621374987084790629 636616054007810078398243)
                    ·
                      rfl

theorem cell22_1859708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_1859708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1859708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1859708 prefixEnd_1859708 := by exact prefixLift 1859708
  have htrace : WordTrace (prefixWord ++ tailWord_1859708) baseStart_1859708 baseEnd_1859708 := by
    simpa [prefixWord, tailWord_1859708, baseEnd_1859708] using wordTrace_append hprefix tailTrace_1859708
  have hstable : (prefixWord ++ tailWord_1859708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859708).length < 2 ^ (prefixWord ++ tailWord_1859708).sum := by decide
  have hdescent : baseEnd_1859708 < baseStart_1859708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859742 : List Nat := [4, 3, 1, 1, 3, 1, 2, 1, 2, 4]
def baseStart_1859742 : Nat := 118140960795 + 1859742 * 2 ^ 59
def prefixEnd_1859742 : Nat := 4983230072969 + 3 ^ 40 * 1859742 * 2
def baseEnd_1859742 : Nat := 636627692902645323048139

theorem tailTrace_1859742 : CollatzResearch.WordTrace tailWord_1859742 prefixEnd_1859742 636627692902645323048139 := by
  unfold tailWord_1859742
  simp only [CollatzResearch.WordTrace]
  refine ⟨8478795403559978436474685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45220242152319884994531653 8478795403559978436474685)
  ·
    refine ⟨3179548276334991913678007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8478795403559978436474685 3179548276334991913678007)
    ·
      refine ⟨4769322414502487870517011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3179548276334991913678007 4769322414502487870517011)
      ·
        refine ⟨7153983621753731805775517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4769322414502487870517011 7153983621753731805775517)
        ·
          refine ⟨2682743858157649427165819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7153983621753731805775517 2682743858157649427165819)
          ·
            refine ⟨4024115787236474140748729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2682743858157649427165819 4024115787236474140748729)
            ·
              refine ⟨3018086840427355605561547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4024115787236474140748729 3018086840427355605561547)
              ·
                refine ⟨4527130260641033408342321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3018086840427355605561547 4527130260641033408342321)
                ·
                  refine ⟨3395347695480775056256741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4527130260641033408342321 3395347695480775056256741)
                  ·
                    refine ⟨636627692902645323048139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3395347695480775056256741 636627692902645323048139)
                    ·
                      rfl

theorem cell22_1859742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_1859742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1859742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1859742 prefixEnd_1859742 := by exact prefixLift 1859742
  have htrace : WordTrace (prefixWord ++ tailWord_1859742) baseStart_1859742 baseEnd_1859742 := by
    simpa [prefixWord, tailWord_1859742, baseEnd_1859742] using wordTrace_append hprefix tailTrace_1859742
  have hstable : (prefixWord ++ tailWord_1859742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859742).length < 2 ^ (prefixWord ++ tailWord_1859742).sum := by decide
  have hdescent : baseEnd_1859742 < baseStart_1859742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859768 : List Nat := [2, 1, 2, 1, 2, 1, 6, 2, 5]
def baseStart_1859768 : Nat := 118140960795 + 1859768 * 2 ^ 59
def prefixEnd_1859768 : Nat := 4983230072969 + 3 ^ 40 * 1859768 * 2
def baseEnd_1859768 : Nat := 212212197744663307299353

theorem tailTrace_1859768 : CollatzResearch.WordTrace tailWord_1859768 prefixEnd_1859768 212212197744663307299353 := by
  unfold tailWord_1859768
  simp only [CollatzResearch.WordTrace]
  refine ⟨33915655763192816966121979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45220874350923755954829305 33915655763192816966121979)
  ·
    refine ⟨50873483644789225449182969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33915655763192816966121979 50873483644789225449182969)
    ·
      refine ⟨38155112733591919086887227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50873483644789225449182969 38155112733591919086887227)
      ·
        refine ⟨57232669100387878630330841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38155112733591919086887227 57232669100387878630330841)
        ·
          refine ⟨42924501825290908972748131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57232669100387878630330841 42924501825290908972748131)
          ·
            refine ⟨64386752737936363459122197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42924501825290908972748131 64386752737936363459122197)
            ·
              refine ⟨3018129034590767037146353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64386752737936363459122197 3018129034590767037146353)
              ·
                refine ⟨2263596775943075277859765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3018129034590767037146353 2263596775943075277859765)
                ·
                  refine ⟨212212197744663307299353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2263596775943075277859765 212212197744663307299353)
                  ·
                    rfl

theorem cell22_1859768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 5].length) (baseStart_1859768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1859768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1859768 prefixEnd_1859768 := by exact prefixLift 1859768
  have htrace : WordTrace (prefixWord ++ tailWord_1859768) baseStart_1859768 baseEnd_1859768 := by
    simpa [prefixWord, tailWord_1859768, baseEnd_1859768] using wordTrace_append hprefix tailTrace_1859768
  have hstable : (prefixWord ++ tailWord_1859768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859768).length < 2 ^ (prefixWord ++ tailWord_1859768).sum := by decide
  have hdescent : baseEnd_1859768 < baseStart_1859768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859918 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 3, 7]
def baseStart_1859918 : Nat := 118140960795 + 1859918 * 2 ^ 59
def prefixEnd_1859918 : Nat := 4983230072969 + 3 ^ 40 * 1859918 * 2
def baseEnd_1859918 : Nat := 636687941299439530647599

theorem tailTrace_1859918 : CollatzResearch.WordTrace tailWord_1859918 prefixEnd_1859918 636687941299439530647599 := by
  unfold tailWord_1859918
  simp only [CollatzResearch.WordTrace]
  refine ⟨8479597809480276193775551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45224521650561473033469605 8479597809480276193775551)
  ·
    refine ⟨12719396714220414290663327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8479597809480276193775551 12719396714220414290663327)
    ·
      refine ⟨19079095071330621435994991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12719396714220414290663327 19079095071330621435994991)
      ·
        refine ⟨28618642606995932153992487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19079095071330621435994991 28618642606995932153992487)
        ·
          refine ⟨42927963910493898230988731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28618642606995932153992487 42927963910493898230988731)
          ·
            refine ⟨64391945865740847346483097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42927963910493898230988731 64391945865740847346483097)
            ·
              refine ⟨48293959399305635509862323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64391945865740847346483097 48293959399305635509862323)
              ·
                refine ⟨72440939098958453264793485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48293959399305635509862323 72440939098958453264793485)
                ·
                  refine ⟨27165352162109419974297557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72440939098958453264793485 27165352162109419974297557)
                  ·
                    refine ⟨636687941299439530647599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27165352162109419974297557 636687941299439530647599)
                    ·
                      rfl

theorem cell22_1859918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_1859918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1859918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1859918 prefixEnd_1859918 := by exact prefixLift 1859918
  have htrace : WordTrace (prefixWord ++ tailWord_1859918) baseStart_1859918 baseEnd_1859918 := by
    simpa [prefixWord, tailWord_1859918, baseEnd_1859918] using wordTrace_append hprefix tailTrace_1859918
  have hstable : (prefixWord ++ tailWord_1859918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859918).length < 2 ^ (prefixWord ++ tailWord_1859918).sum := by decide
  have hdescent : baseEnd_1859918 < baseStart_1859918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859941 : List Nat := [1, 3, 1, 3, 1, 5, 2, 2, 1, 3]
def baseStart_1859941 : Nat := 118140960795 + 1859941 * 2 ^ 59
def prefixEnd_1859941 : Nat := 4983230072969 + 3 ^ 40 * 1859941 * 2
def baseEnd_1859941 : Nat := 636695814669475137322529

theorem tailTrace_1859941 : CollatzResearch.WordTrace tailWord_1859941 prefixEnd_1859941 636695814669475137322529 := by
  unfold tailWord_1859941
  simp only [CollatzResearch.WordTrace]
  refine ⟨67837621354758884478291677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45225080903172589652194451 67837621354758884478291677)
  ·
    refine ⟨25439108008034581679359379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67837621354758884478291677 25439108008034581679359379)
    ·
      refine ⟨38158662012051872519039069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25439108008034581679359379 38158662012051872519039069)
      ·
        refine ⟨14309498254519452194639651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38158662012051872519039069 14309498254519452194639651)
        ·
          refine ⟨21464247381779178291959477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14309498254519452194639651 21464247381779178291959477)
          ·
            refine ⟨2012273192041797964871201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21464247381779178291959477 2012273192041797964871201)
            ·
              refine ⟨1509204894031348473653401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2012273192041797964871201 1509204894031348473653401)
              ·
                refine ⟨1131903670523511355240051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1509204894031348473653401 1131903670523511355240051)
                ·
                  refine ⟨1697855505785267032860077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1131903670523511355240051 1697855505785267032860077)
                  ·
                    refine ⟨636695814669475137322529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1697855505785267032860077 636695814669475137322529)
                    ·
                      rfl

theorem cell22_1859941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 2, 1, 3].length) (baseStart_1859941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1859941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1859941 prefixEnd_1859941 := by exact prefixLift 1859941
  have htrace : WordTrace (prefixWord ++ tailWord_1859941) baseStart_1859941 baseEnd_1859941 := by
    simpa [prefixWord, tailWord_1859941, baseEnd_1859941] using wordTrace_append hprefix tailTrace_1859941
  have hstable : (prefixWord ++ tailWord_1859941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859941).length < 2 ^ (prefixWord ++ tailWord_1859941).sum := by decide
  have hdescent : baseEnd_1859941 < baseStart_1859941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859965 : List Nat := [1, 4, 1, 1, 2, 4, 1, 2, 6]
def baseStart_1859965 : Nat := 118140960795 + 1859965 * 2 ^ 59
def prefixEnd_1859965 : Nat := 4983230072969 + 3 ^ 40 * 1859965 * 2
def baseEnd_1859965 : Nat := 212234676786649024907485

theorem tailTrace_1859965 : CollatzResearch.WordTrace tailWord_1859965 prefixEnd_1859965 212234676786649024907485 := by
  unfold tailWord_1859965
  simp only [CollatzResearch.WordTrace]
  refine ⟨67838496706671936577165349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45225664471114624384776899 67838496706671936577165349)
  ·
    refine ⟨12719718132500988108218503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67838496706671936577165349 12719718132500988108218503)
    ·
      refine ⟨19079577198751482162327755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12719718132500988108218503 19079577198751482162327755)
      ·
        refine ⟨28619365798127223243491633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19079577198751482162327755 28619365798127223243491633)
        ·
          refine ⟨21464524348595417432618725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28619365798127223243491633 21464524348595417432618725)
          ·
            refine ⟨4024598315361640768616011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21464524348595417432618725 4024598315361640768616011)
            ·
              refine ⟨6036897473042461152924017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4024598315361640768616011 6036897473042461152924017)
              ·
                refine ⟨4527673104781845864693013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6036897473042461152924017 4527673104781845864693013)
                ·
                  refine ⟨212234676786649024907485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4527673104781845864693013 212234676786649024907485)
                  ·
                    rfl

theorem cell22_1859965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_1859965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1859965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1859965 prefixEnd_1859965 := by exact prefixLift 1859965
  have htrace : WordTrace (prefixWord ++ tailWord_1859965) baseStart_1859965 baseEnd_1859965 := by
    simpa [prefixWord, tailWord_1859965, baseEnd_1859965] using wordTrace_append hprefix tailTrace_1859965
  have hstable : (prefixWord ++ tailWord_1859965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859965).length < 2 ^ (prefixWord ++ tailWord_1859965).sum := by decide
  have hdescent : baseEnd_1859965 < baseStart_1859965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859980 : List Nat := [2, 2, 1, 2, 1, 4, 2, 2, 1, 5]
def baseStart_1859980 : Nat := 118140960795 + 1859980 * 2 ^ 59
def prefixEnd_1859980 : Nat := 4983230072969 + 3 ^ 40 * 1859980 * 2
def baseEnd_1859980 : Nat := 636709165166492035597409

theorem tailTrace_1859980 : CollatzResearch.WordTrace tailWord_1859980 prefixEnd_1859980 636709165166492035597409 := by
  unfold tailWord_1859980
  simp only [CollatzResearch.WordTrace]
  refine ⟨33919521900808797069480697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45226029201078396092640929 33919521900808797069480697)
  ·
    refine ⟨25439641425606597802110523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33919521900808797069480697 25439641425606597802110523)
    ·
      refine ⟨38159462138409896703165785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25439641425606597802110523 38159462138409896703165785)
      ·
        refine ⟨28619596603807422527374339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38159462138409896703165785 28619596603807422527374339)
        ·
          refine ⟨42929394905711133791061509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28619596603807422527374339 42929394905711133791061509)
          ·
            refine ⟨8049261544820837585824033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42929394905711133791061509 8049261544820837585824033)
            ·
              refine ⟨6036946158615628189368025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8049261544820837585824033 6036946158615628189368025)
              ·
                refine ⟨4527709618961721142026019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6036946158615628189368025 4527709618961721142026019)
                ·
                  refine ⟨6791564428442581713039029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4527709618961721142026019 6791564428442581713039029)
                  ·
                    refine ⟨636709165166492035597409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6791564428442581713039029 636709165166492035597409)
                    ·
                      rfl

theorem cell22_1859980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_1859980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1859980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1859980 prefixEnd_1859980 := by exact prefixLift 1859980
  have htrace : WordTrace (prefixWord ++ tailWord_1859980) baseStart_1859980 baseEnd_1859980 := by
    simpa [prefixWord, tailWord_1859980, baseEnd_1859980] using wordTrace_append hprefix tailTrace_1859980
  have hstable : (prefixWord ++ tailWord_1859980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859980).length < 2 ^ (prefixWord ++ tailWord_1859980).sum := by decide
  have hdescent : baseEnd_1859980 < baseStart_1859980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859993 : List Nat := [1, 2, 1, 2, 1, 4, 11]
def baseStart_1859993 : Nat := 118140960795 + 1859993 * 2 ^ 59
def prefixEnd_1859993 : Nat := 4983230072969 + 3 ^ 40 * 1859993 * 2
def baseEnd_1859993 : Nat := 23581985753043123519347

theorem tailTrace_1859993 : CollatzResearch.WordTrace tailWord_1859993 prefixEnd_1859993 23581985753043123519347 := by
  unfold tailWord_1859993
  simp only [CollatzResearch.WordTrace]
  refine ⟨67839517950570497359184633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45226345300380331572789755 67839517950570497359184633)
  ·
    refine ⟨50879638462927873019388475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67839517950570497359184633 50879638462927873019388475)
    ·
      refine ⟨76319457694391809529082713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50879638462927873019388475 76319457694391809529082713)
      ·
        refine ⟨57239593270793857146812035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76319457694391809529082713 57239593270793857146812035)
        ·
          refine ⟨85859389906190785720218053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57239593270793857146812035 85859389906190785720218053)
          ·
            refine ⟨16098635607410772322540885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85859389906190785720218053 16098635607410772322540885)
            ·
              refine ⟨23581985753043123519347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 16098635607410772322540885 23581985753043123519347)
              ·
                rfl

theorem cell22_1859993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 11].length) (baseStart_1859993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1859993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1859993 prefixEnd_1859993 := by exact prefixLift 1859993
  have htrace : WordTrace (prefixWord ++ tailWord_1859993) baseStart_1859993 baseEnd_1859993 := by
    simpa [prefixWord, tailWord_1859993, baseEnd_1859993] using wordTrace_append hprefix tailTrace_1859993
  have hstable : (prefixWord ++ tailWord_1859993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859993).length < 2 ^ (prefixWord ++ tailWord_1859993).sum := by decide
  have hdescent : baseEnd_1859993 < baseStart_1859993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860072 : List Nat := [2, 1, 4, 1, 1, 4, 1, 3, 5]
def baseStart_1860072 : Nat := 118140960795 + 1860072 * 2 ^ 59
def prefixEnd_1860072 : Nat := 4983230072969 + 3 ^ 40 * 1860072 * 2
def baseEnd_1860072 : Nat := 212246886215544820765709

theorem tailTrace_1860072 : CollatzResearch.WordTrace tailWord_1860072 prefixEnd_1860072 212246886215544820765709 := by
  unfold tailWord_1860072
  simp only [CollatzResearch.WordTrace]
  refine ⟨33921199658642146925655235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45228266211522862567540313 33921199658642146925655235)
  ·
    refine ⟨50881799487963220388482853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33921199658642146925655235 50881799487963220388482853)
    ·
      refine ⟨9540337403993103822840535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50881799487963220388482853 9540337403993103822840535)
      ·
        refine ⟨14310506105989655734260803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9540337403993103822840535 14310506105989655734260803)
        ·
          refine ⟨21465759158984483601391205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14310506105989655734260803 21465759158984483601391205)
          ·
            refine ⟨4024829842309590675260851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21465759158984483601391205 4024829842309590675260851)
            ·
              refine ⟨6037244763464386012891277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4024829842309590675260851 6037244763464386012891277)
              ·
                refine ⟨2263966786299144754834229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6037244763464386012891277 2263966786299144754834229)
                ·
                  refine ⟨212246886215544820765709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2263966786299144754834229 212246886215544820765709)
                  ·
                    rfl

theorem cell22_1860072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 5].length) (baseStart_1860072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1860072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1860072 prefixEnd_1860072 := by exact prefixLift 1860072
  have htrace : WordTrace (prefixWord ++ tailWord_1860072) baseStart_1860072 baseEnd_1860072 := by
    simpa [prefixWord, tailWord_1860072, baseEnd_1860072] using wordTrace_append hprefix tailTrace_1860072
  have hstable : (prefixWord ++ tailWord_1860072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860072).length < 2 ^ (prefixWord ++ tailWord_1860072).sum := by decide
  have hdescent : baseEnd_1860072 < baseStart_1860072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860115 : List Nat := [1, 1, 1, 2, 1, 5, 1, 2, 3, 5]
def baseStart_1860115 : Nat := 118140960795 + 1860115 * 2 ^ 59
def prefixEnd_1860115 : Nat := 4983230072969 + 3 ^ 40 * 1860115 * 2
def baseEnd_1860115 : Nat := 636755378425396683471995

theorem tailTrace_1860115 : CollatzResearch.WordTrace tailWord_1860115 prefixEnd_1860115 636755378425396683471995 := by
  unfold tailWord_1860115
  simp only [CollatzResearch.WordTrace]
  refine ⟨67843967656128512195125799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45229311770752341463417199 67843967656128512195125799)
  ·
    refine ⟨101765951484192768292688699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67843967656128512195125799 101765951484192768292688699)
    ·
      refine ⟨152648927226289152439033049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101765951484192768292688699 152648927226289152439033049)
      ·
        refine ⟨114486695419716864329274787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152648927226289152439033049 114486695419716864329274787)
        ·
          refine ⟨171730043129575296493912181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114486695419716864329274787 171730043129575296493912181)
          ·
            refine ⟨16099691543397684046304267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 171730043129575296493912181 16099691543397684046304267)
            ·
              refine ⟨24149537315096526069456401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16099691543397684046304267 24149537315096526069456401)
              ·
                refine ⟨18112152986322394552092301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24149537315096526069456401 18112152986322394552092301)
                ·
                  refine ⟨6792057369870897957034613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18112152986322394552092301 6792057369870897957034613)
                  ·
                    refine ⟨636755378425396683471995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6792057369870897957034613 636755378425396683471995)
                    ·
                      rfl

theorem cell22_1860115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 5].length) (baseStart_1860115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1860115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1860115 prefixEnd_1860115 := by exact prefixLift 1860115
  have htrace : WordTrace (prefixWord ++ tailWord_1860115) baseStart_1860115 baseEnd_1860115 := by
    simpa [prefixWord, tailWord_1860115, baseEnd_1860115] using wordTrace_append hprefix tailTrace_1860115
  have hstable : (prefixWord ++ tailWord_1860115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860115).length < 2 ^ (prefixWord ++ tailWord_1860115).sum := by decide
  have hdescent : baseEnd_1860115 < baseStart_1860115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860145 : List Nat := [1, 2, 2, 3, 1, 1, 2, 10]
def baseStart_1860145 : Nat := 118140960795 + 1860145 * 2 ^ 59
def prefixEnd_1860145 : Nat := 4983230072969 + 3 ^ 40 * 1860145 * 2
def baseEnd_1860145 : Nat := 70751738670942956135767

theorem tailTrace_1860145 : CollatzResearch.WordTrace tailWord_1860145 prefixEnd_1860145 70751738670942956135767 := by
  unfold tailWord_1860145
  simp only [CollatzResearch.WordTrace]
  refine ⟨67845061846019827318717889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45230041230679884879145259 67845061846019827318717889)
  ·
    refine ⟨50883796384514870489038417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67845061846019827318717889 50883796384514870489038417)
    ·
      refine ⟨38162847288386152866778813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50883796384514870489038417 38162847288386152866778813)
      ·
        refine ⟨14311067733144807325042055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38162847288386152866778813 14311067733144807325042055)
        ·
          refine ⟨21466601599717210987563083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14311067733144807325042055 21466601599717210987563083)
          ·
            refine ⟨32199902399575816481344625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21466601599717210987563083 32199902399575816481344625)
            ·
              refine ⟨24149926799681862361008469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32199902399575816481344625 24149926799681862361008469)
              ·
                refine ⟨70751738670942956135767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 24149926799681862361008469 70751738670942956135767)
                ·
                  rfl

theorem cell22_1860145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 10].length) (baseStart_1860145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1860145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1860145 prefixEnd_1860145 := by exact prefixLift 1860145
  have htrace : WordTrace (prefixWord ++ tailWord_1860145) baseStart_1860145 baseEnd_1860145 := by
    simpa [prefixWord, tailWord_1860145, baseEnd_1860145] using wordTrace_append hprefix tailTrace_1860145
  have hstable : (prefixWord ++ tailWord_1860145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860145).length < 2 ^ (prefixWord ++ tailWord_1860145).sum := by decide
  have hdescent : baseEnd_1860145 < baseStart_1860145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860175 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 1, 8]
def baseStart_1860175 : Nat := 118140960795 + 1860175 * 2 ^ 59
def prefixEnd_1860175 : Nat := 4983230072969 + 3 ^ 40 * 1860175 * 2
def baseEnd_1860175 : Nat := 636775917651576526971811

theorem tailTrace_1860175 : CollatzResearch.WordTrace tailWord_1860175 prefixEnd_1860175 636775917651576526971811 := by
  unfold tailWord_1860175
  simp only [CollatzResearch.WordTrace]
  refine ⟨67846156035911142442309979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45230770690607428294873319 67846156035911142442309979)
  ·
    refine ⟨101769234053866713663464969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67846156035911142442309979 101769234053866713663464969)
    ·
      refine ⟨76326925540400035247598727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101769234053866713663464969 76326925540400035247598727)
      ·
        refine ⟨114490388310600052871398091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76326925540400035247598727 114490388310600052871398091)
        ·
          refine ⟨171735582465900079307097137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114490388310600052871398091 171735582465900079307097137)
          ·
            refine ⟨128801686849425059480322853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171735582465900079307097137 128801686849425059480322853)
            ·
              refine ⟨24150316284267198652560535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128801686849425059480322853 24150316284267198652560535)
              ·
                refine ⟨36225474426400797978840803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24150316284267198652560535 36225474426400797978840803)
                ·
                  refine ⟨54338211639601196968261205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36225474426400797978840803 54338211639601196968261205)
                  ·
                    refine ⟨636775917651576526971811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54338211639601196968261205 636775917651576526971811)
                    ·
                      rfl

theorem cell22_1860175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 8].length) (baseStart_1860175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1860175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1860175 prefixEnd_1860175 := by exact prefixLift 1860175
  have htrace : WordTrace (prefixWord ++ tailWord_1860175) baseStart_1860175 baseEnd_1860175 := by
    simpa [prefixWord, tailWord_1860175, baseEnd_1860175] using wordTrace_append hprefix tailTrace_1860175
  have hstable : (prefixWord ++ tailWord_1860175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860175).length < 2 ^ (prefixWord ++ tailWord_1860175).sum := by decide
  have hdescent : baseEnd_1860175 < baseStart_1860175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860271 : List Nat := [1, 1, 2, 1, 2, 6, 3, 1, 1, 4]
def baseStart_1860271 : Nat := 118140960795 + 1860271 * 2 ^ 59
def prefixEnd_1860271 : Nat := 4983230072969 + 3 ^ 40 * 1860271 * 2
def baseEnd_1860271 : Nat := 636808780413464276571517

theorem tailTrace_1860271 : CollatzResearch.WordTrace tailWord_1860271 prefixEnd_1860271 636808780413464276571517 := by
  unfold tailWord_1860271
  simp only [CollatzResearch.WordTrace]
  refine ⟨67849657443563350837804667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45233104962375567225203111 67849657443563350837804667)
  ·
    refine ⟨101774486165345026256707001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67849657443563350837804667 101774486165345026256707001)
    ·
      refine ⟨76330864624008769692530251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101774486165345026256707001 76330864624008769692530251)
      ·
        refine ⟨114496296936013154538795377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76330864624008769692530251 114496296936013154538795377)
        ·
          refine ⟨85872222702009865904096533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114496296936013154538795377 85872222702009865904096533)
          ·
            refine ⟨4025260439156712464254525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 85872222702009865904096533 4025260439156712464254525)
            ·
              refine ⟨1509472664683767174095447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4025260439156712464254525 1509472664683767174095447)
              ·
                refine ⟨2264208997025650761143171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1509472664683767174095447 2264208997025650761143171)
                ·
                  refine ⟨3396313495538476141714757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2264208997025650761143171 3396313495538476141714757)
                  ·
                    refine ⟨636808780413464276571517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3396313495538476141714757 636808780413464276571517)
                    ·
                      rfl

theorem cell22_1860271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 1, 4].length) (baseStart_1860271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1860271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1860271 prefixEnd_1860271 := by exact prefixLift 1860271
  have htrace : WordTrace (prefixWord ++ tailWord_1860271) baseStart_1860271 baseEnd_1860271 := by
    simpa [prefixWord, tailWord_1860271, baseEnd_1860271] using wordTrace_append hprefix tailTrace_1860271
  have hstable : (prefixWord ++ tailWord_1860271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860271).length < 2 ^ (prefixWord ++ tailWord_1860271).sum := by decide
  have hdescent : baseEnd_1860271 < baseStart_1860271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860286 : List Nat := [4, 2, 1, 1, 2, 1, 3, 4, 4]
def baseStart_1860286 : Nat := 118140960795 + 1860286 * 2 ^ 59
def prefixEnd_1860286 : Nat := 4983230072969 + 3 ^ 40 * 1860286 * 2
def baseEnd_1860286 : Nat := 212271305073336412482157

theorem tailTrace_1860286 : CollatzResearch.WordTrace tailWord_1860286 prefixEnd_1860286 212271305073336412482157 := by
  unfold tailWord_1860286
  simp only [CollatzResearch.WordTrace]
  refine ⟨8481275567313626049950089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45233469692339338933067141 8481275567313626049950089)
  ·
    refine ⟨6360956675485219537462567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8481275567313626049950089 6360956675485219537462567)
    ·
      refine ⟨9541435013227829306193851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6360956675485219537462567 9541435013227829306193851)
      ·
        refine ⟨14312152519841743959290777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9541435013227829306193851 14312152519841743959290777)
        ·
          refine ⟨10734114389881307969468083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14312152519841743959290777 10734114389881307969468083)
          ·
            refine ⟨16101171584821961954202125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10734114389881307969468083 16101171584821961954202125)
            ·
              refine ⟨6037939344308235732825797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16101171584821961954202125 6037939344308235732825797)
              ·
                refine ⟨1132113627057794199904837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6037939344308235732825797 1132113627057794199904837)
                ·
                  refine ⟨212271305073336412482157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1132113627057794199904837 212271305073336412482157)
                  ·
                    rfl

theorem cell22_1860286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_1860286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1860286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1860286 prefixEnd_1860286 := by exact prefixLift 1860286
  have htrace : WordTrace (prefixWord ++ tailWord_1860286) baseStart_1860286 baseEnd_1860286 := by
    simpa [prefixWord, tailWord_1860286, baseEnd_1860286] using wordTrace_append hprefix tailTrace_1860286
  have hstable : (prefixWord ++ tailWord_1860286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860286).length < 2 ^ (prefixWord ++ tailWord_1860286).sum := by decide
  have hdescent : baseEnd_1860286 < baseStart_1860286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860314 : List Nat := [3, 1, 1, 2, 2, 2, 5, 6]
def baseStart_1860314 : Nat := 118140960795 + 1860314 * 2 ^ 59
def prefixEnd_1860314 : Nat := 4983230072969 + 3 ^ 40 * 1860314 * 2
def baseEnd_1860314 : Nat := 70758166688025166416265

theorem tailTrace_1860314 : CollatzResearch.WordTrace tailWord_1860314 prefixEnd_1860314 70758166688025166416265 := by
  unfold tailWord_1860314
  simp only [CollatzResearch.WordTrace]
  refine ⟨16962806445601892295404999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45234150521605046121079997 16962806445601892295404999)
  ·
    refine ⟨25444209668402838443107499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16962806445601892295404999 25444209668402838443107499)
    ·
      refine ⟨38166314502604257664661249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25444209668402838443107499 38166314502604257664661249)
      ·
        refine ⟨28624735876953193248495937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38166314502604257664661249 28624735876953193248495937)
        ·
          refine ⟨21468551907714894936371953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28624735876953193248495937 21468551907714894936371953)
          ·
            refine ⟨16101413930786171202278965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21468551907714894936371953 16101413930786171202278965)
            ·
              refine ⟨1509507556011203550213653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16101413930786171202278965 1509507556011203550213653)
              ·
                refine ⟨70758166688025166416265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1509507556011203550213653 70758166688025166416265)
                ·
                  rfl

theorem cell22_1860314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 6].length) (baseStart_1860314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1860314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1860314 prefixEnd_1860314 := by exact prefixLift 1860314
  have htrace : WordTrace (prefixWord ++ tailWord_1860314) baseStart_1860314 baseEnd_1860314 := by
    simpa [prefixWord, tailWord_1860314, baseEnd_1860314] using wordTrace_append hprefix tailTrace_1860314
  have hstable : (prefixWord ++ tailWord_1860314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860314).length < 2 ^ (prefixWord ++ tailWord_1860314).sum := by decide
  have hdescent : baseEnd_1860314 < baseStart_1860314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860316 : List Nat := [2, 2, 5, 1, 1, 2, 1, 1, 1, 6]
def baseStart_1860316 : Nat := 118140960795 + 1860316 * 2 ^ 59
def prefixEnd_1860316 : Nat := 4983230072969 + 3 ^ 40 * 1860316 * 2
def baseEnd_1860316 : Nat := 636824184833099159196379

theorem tailTrace_1860316 : CollatzResearch.WordTrace tailWord_1860316 prefixEnd_1860316 636824184833099159196379 := by
  unfold tailWord_1860316
  simp only [CollatzResearch.WordTrace]
  refine ⟨33925649364200161761596401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45234199152266882348795201 33925649364200161761596401)
  ·
    refine ⟨25444237023150121321197301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33925649364200161761596401 25444237023150121321197301)
    ·
      refine ⟨2385397220920323873862247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25444237023150121321197301 2385397220920323873862247)
      ·
        refine ⟨3578095831380485810793371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2385397220920323873862247 3578095831380485810793371)
        ·
          refine ⟨5367143747070728716190057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3578095831380485810793371 5367143747070728716190057)
          ·
            refine ⟨4025357810303046537142543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5367143747070728716190057 4025357810303046537142543)
            ·
              refine ⟨6038036715454569805713815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4025357810303046537142543 6038036715454569805713815)
              ·
                refine ⟨9057055073181854708570723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6038036715454569805713815 9057055073181854708570723)
                ·
                  refine ⟨13585582609772782062856085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9057055073181854708570723 13585582609772782062856085)
                  ·
                    refine ⟨636824184833099159196379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13585582609772782062856085 636824184833099159196379)
                    ·
                      rfl

theorem cell22_1860316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_1860316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1860316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1860316 prefixEnd_1860316 := by exact prefixLift 1860316
  have htrace : WordTrace (prefixWord ++ tailWord_1860316) baseStart_1860316 baseEnd_1860316 := by
    simpa [prefixWord, tailWord_1860316, baseEnd_1860316] using wordTrace_append hprefix tailTrace_1860316
  have hstable : (prefixWord ++ tailWord_1860316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860316).length < 2 ^ (prefixWord ++ tailWord_1860316).sum := by decide
  have hdescent : baseEnd_1860316 < baseStart_1860316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860380 : List Nat := [2, 2, 3, 1, 1, 5, 1, 3, 1, 3]
def baseStart_1860380 : Nat := 118140960795 + 1860380 * 2 ^ 59
def prefixEnd_1860380 : Nat := 4983230072969 + 3 ^ 40 * 1860380 * 2
def baseEnd_1860380 : Nat := 636846093341024325596183

theorem tailTrace_1860380 : CollatzResearch.WordTrace tailWord_1860380 prefixEnd_1860380 636846093341024325596183 := by
  unfold tailWord_1860380
  simp only [CollatzResearch.WordTrace]
  refine ⟨33926816500084231226761297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45235755333445641635681729 33926816500084231226761297)
  ·
    refine ⟨25445112375063173420070973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33926816500084231226761297 25445112375063173420070973)
    ·
      refine ⟨9541917140648690032526615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25445112375063173420070973 9541917140648690032526615)
      ·
        refine ⟨14312875710973035048789923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9541917140648690032526615 14312875710973035048789923)
        ·
          refine ⟨21469313566459552573184885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14312875710973035048789923 21469313566459552573184885)
          ·
            refine ⟨2012748146855583053736083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21469313566459552573184885 2012748146855583053736083)
            ·
              refine ⟨3019122220283374580604125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2012748146855583053736083 3019122220283374580604125)
              ·
                refine ⟨1132170832606265467726547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3019122220283374580604125 1132170832606265467726547)
                ·
                  refine ⟨1698256248909398201589821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1132170832606265467726547 1698256248909398201589821)
                  ·
                    refine ⟨636846093341024325596183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1698256248909398201589821 636846093341024325596183)
                    ·
                      rfl

theorem cell22_1860380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_1860380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1860380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1860380 prefixEnd_1860380 := by exact prefixLift 1860380
  have htrace : WordTrace (prefixWord ++ tailWord_1860380) baseStart_1860380 baseEnd_1860380 := by
    simpa [prefixWord, tailWord_1860380, baseEnd_1860380] using wordTrace_append hprefix tailTrace_1860380
  have hstable : (prefixWord ++ tailWord_1860380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860380).length < 2 ^ (prefixWord ++ tailWord_1860380).sum := by decide
  have hdescent : baseEnd_1860380 < baseStart_1860380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860397 : List Nat := [1, 5, 3, 2, 1, 2, 1, 1, 3, 3]
def baseStart_1860397 : Nat := 118140960795 + 1860397 * 2 ^ 59
def prefixEnd_1860397 : Nat := 4983230072969 + 3 ^ 40 * 1860397 * 2
def baseEnd_1860397 : Nat := 636851912788441947921131

theorem tailTrace_1860397 : CollatzResearch.WordTrace tailWord_1860397 prefixEnd_1860397 636851912788441947921131 := by
  unfold tailWord_1860397
  simp only [CollatzResearch.WordTrace]
  refine ⟨67854253041106874356891445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45236168694071249571260963 67854253041106874356891445)
  ·
    refine ⟨6361336222603769470958573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67854253041106874356891445 6361336222603769470958573)
    ·
      refine ⟨2385501083476413551609465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6361336222603769470958573 2385501083476413551609465)
      ·
        refine ⟨1789125812607310163707099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2385501083476413551609465 1789125812607310163707099)
        ·
          refine ⟨2683688718910965245560649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1789125812607310163707099 2683688718910965245560649)
          ·
            refine ⟨2012766539183223934170487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2683688718910965245560649 2012766539183223934170487)
            ·
              refine ⟨3019149808774835901255731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2012766539183223934170487 3019149808774835901255731)
              ·
                refine ⟨4528724713162253851883597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3019149808774835901255731 4528724713162253851883597)
                ·
                  refine ⟨1698271767435845194456349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4528724713162253851883597 1698271767435845194456349)
                  ·
                    refine ⟨636851912788441947921131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1698271767435845194456349 636851912788441947921131)
                    ·
                      rfl

theorem cell22_1860397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_1860397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1860397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1860397 prefixEnd_1860397 := by exact prefixLift 1860397
  have htrace : WordTrace (prefixWord ++ tailWord_1860397) baseStart_1860397 baseEnd_1860397 := by
    simpa [prefixWord, tailWord_1860397, baseEnd_1860397] using wordTrace_append hprefix tailTrace_1860397
  have hstable : (prefixWord ++ tailWord_1860397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860397).length < 2 ^ (prefixWord ++ tailWord_1860397).sum := by decide
  have hdescent : baseEnd_1860397 < baseStart_1860397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860410 : List Nat := [3, 1, 1, 1, 7, 1, 2, 1, 5]
def baseStart_1860410 : Nat := 118140960795 + 1860410 * 2 ^ 59
def prefixEnd_1860410 : Nat := 4983230072969 + 3 ^ 40 * 1860410 * 2
def baseEnd_1860410 : Nat := 212285454318038082448697

theorem tailTrace_1860410 : CollatzResearch.WordTrace tailWord_1860410 prefixEnd_1860410 212285454318038082448697 := by
  unfold tailWord_1860410
  simp only [CollatzResearch.WordTrace]
  refine ⟨16963681797514944394278671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45236484793373185051409789 16963681797514944394278671)
  ·
    refine ⟨25445522696272416591418007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16963681797514944394278671 25445522696272416591418007)
    ·
      refine ⟨38168284044408624887127011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25445522696272416591418007 38168284044408624887127011)
      ·
        refine ⟨57252426066612937330690517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38168284044408624887127011 57252426066612937330690517)
        ·
          refine ⟨1341853735936240718688059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 57252426066612937330690517 1341853735936240718688059)
          ·
            refine ⟨2012780603904361078032089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1341853735936240718688059 2012780603904361078032089)
            ·
              refine ⟨1509585452928270808524067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2012780603904361078032089 1509585452928270808524067)
              ·
                refine ⟨2264378179392406212786101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1509585452928270808524067 2264378179392406212786101)
                ·
                  refine ⟨212285454318038082448697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2264378179392406212786101 212285454318038082448697)
                  ·
                    rfl

theorem cell22_1860410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 5].length) (baseStart_1860410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1860410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1860410 prefixEnd_1860410 := by exact prefixLift 1860410
  have htrace : WordTrace (prefixWord ++ tailWord_1860410) baseStart_1860410 baseEnd_1860410 := by
    simpa [prefixWord, tailWord_1860410, baseEnd_1860410] using wordTrace_append hprefix tailTrace_1860410
  have hstable : (prefixWord ++ tailWord_1860410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860410).length < 2 ^ (prefixWord ++ tailWord_1860410).sum := by decide
  have hdescent : baseEnd_1860410 < baseStart_1860410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860419 : List Nat := [1, 1, 1, 3, 1, 4, 2, 3, 1, 5]
def baseStart_1860419 : Nat := 118140960795 + 1860419 * 2 ^ 59
def prefixEnd_1860419 : Nat := 4983230072969 + 3 ^ 40 * 1860419 * 2
def baseEnd_1860419 : Nat := 636859443838041223871063

theorem tailTrace_1860419 : CollatzResearch.WordTrace tailWord_1860419 prefixEnd_1860419 636859443838041223871063 := by
  unfold tailWord_1860419
  simp only [CollatzResearch.WordTrace]
  refine ⟨67855055447027172114192311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45236703631351448076128207 67855055447027172114192311)
  ·
    refine ⟨101782583170540758171288467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67855055447027172114192311 101782583170540758171288467)
    ·
      refine ⟨152673874755811137256932701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101782583170540758171288467 152673874755811137256932701)
      ·
        refine ⟨57252703033429176471349763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152673874755811137256932701 57252703033429176471349763)
        ·
          refine ⟨85879054550143764707024645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57252703033429176471349763 85879054550143764707024645)
          ·
            refine ⟨16102322728151955882567121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85879054550143764707024645 16102322728151955882567121)
            ·
              refine ⟨12076742046113966911925341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16102322728151955882567121 12076742046113966911925341)
              ·
                refine ⟨4528778267292737591972003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12076742046113966911925341 4528778267292737591972003)
                ·
                  refine ⟨6793167400939106387958005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4528778267292737591972003 6793167400939106387958005)
                  ·
                    refine ⟨636859443838041223871063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6793167400939106387958005 636859443838041223871063)
                    ·
                      rfl

theorem cell22_1860419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 5].length) (baseStart_1860419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1860419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1860419 prefixEnd_1860419 := by exact prefixLift 1860419
  have htrace : WordTrace (prefixWord ++ tailWord_1860419) baseStart_1860419 baseEnd_1860419 := by
    simpa [prefixWord, tailWord_1860419, baseEnd_1860419] using wordTrace_append hprefix tailTrace_1860419
  have hstable : (prefixWord ++ tailWord_1860419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860419).length < 2 ^ (prefixWord ++ tailWord_1860419).sum := by decide
  have hdescent : baseEnd_1860419 < baseStart_1860419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860451 : List Nat := [1, 1, 1, 5, 3, 1, 2, 2, 2, 4]
def baseStart_1860451 : Nat := 118140960795 + 1860451 * 2 ^ 59
def prefixEnd_1860451 : Nat := 4983230072969 + 3 ^ 40 * 1860451 * 2
def baseEnd_1860451 : Nat := 636870398092003807070965

theorem tailTrace_1860451 : CollatzResearch.WordTrace tailWord_1860451 prefixEnd_1860451 636870398092003807070965 := by
  unfold tailWord_1860451
  simp only [CollatzResearch.WordTrace]
  refine ⟨67856222582911241579357207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45237481721940827719571471 67856222582911241579357207)
  ·
    refine ⟨101784333874366862369035811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67856222582911241579357207 101784333874366862369035811)
    ·
      refine ⟨152676500811550293553553717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101784333874366862369035811 152676500811550293553553717)
      ·
        refine ⟨14313421951082840020645661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152676500811550293553553717 14313421951082840020645661)
        ·
          refine ⟨5367533231656065007742123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14313421951082840020645661 5367533231656065007742123)
          ·
            refine ⟨8051299847484097511613185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5367533231656065007742123 8051299847484097511613185)
            ·
              refine ⟨6038474885613073133709889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8051299847484097511613185 6038474885613073133709889)
              ·
                refine ⟨4528856164209804850282417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6038474885613073133709889 4528856164209804850282417)
                ·
                  refine ⟨3396642123157353637711813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4528856164209804850282417 3396642123157353637711813)
                  ·
                    refine ⟨636870398092003807070965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3396642123157353637711813 636870398092003807070965)
                    ·
                      rfl

theorem cell22_1860451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 4].length) (baseStart_1860451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1860451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1860451 prefixEnd_1860451 := by exact prefixLift 1860451
  have htrace : WordTrace (prefixWord ++ tailWord_1860451) baseStart_1860451 baseEnd_1860451 := by
    simpa [prefixWord, tailWord_1860451, baseEnd_1860451] using wordTrace_append hprefix tailTrace_1860451
  have hstable : (prefixWord ++ tailWord_1860451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860451).length < 2 ^ (prefixWord ++ tailWord_1860451).sum := by decide
  have hdescent : baseEnd_1860451 < baseStart_1860451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860455 : List Nat := [1, 1, 5, 1, 2, 4, 2, 2, 4]
def baseStart_1860455 : Nat := 118140960795 + 1860455 * 2 ^ 59
def prefixEnd_1860455 : Nat := 4983230072969 + 3 ^ 40 * 1860455 * 2
def baseEnd_1860455 : Nat := 212290589124583043323651

theorem tailTrace_1860455 : CollatzResearch.WordTrace tailWord_1860455 prefixEnd_1860455 212290589124583043323651 := by
  unfold tailWord_1860455
  simp only [CollatzResearch.WordTrace]
  refine ⟨67856368474896750262502819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45237578983264500175001879 67856368474896750262502819)
  ·
    refine ⟨101784552712345125393754229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67856368474896750262502819 101784552712345125393754229)
    ·
      refine ⟨9542301816782355505664459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101784552712345125393754229 9542301816782355505664459)
      ·
        refine ⟨14313452725173533258496689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9542301816782355505664459 14313452725173533258496689)
        ·
          refine ⟨10735089543880149943872517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14313452725173533258496689 10735089543880149943872517)
          ·
            refine ⟨2012829289477528114476097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10735089543880149943872517 2012829289477528114476097)
            ·
              refine ⟨1509621967108146085857073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2012829289477528114476097 1509621967108146085857073)
              ·
                refine ⟨1132216475331109564392805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1509621967108146085857073 1132216475331109564392805)
                ·
                  refine ⟨212290589124583043323651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1132216475331109564392805 212290589124583043323651)
                  ·
                    rfl

theorem cell22_1860455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 2, 4].length) (baseStart_1860455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1860455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1860455 prefixEnd_1860455 := by exact prefixLift 1860455
  have htrace : WordTrace (prefixWord ++ tailWord_1860455) baseStart_1860455 baseEnd_1860455 := by
    simpa [prefixWord, tailWord_1860455, baseEnd_1860455] using wordTrace_append hprefix tailTrace_1860455
  have hstable : (prefixWord ++ tailWord_1860455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860455).length < 2 ^ (prefixWord ++ tailWord_1860455).sum := by decide
  have hdescent : baseEnd_1860455 < baseStart_1860455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860470 : List Nat := [5, 1, 1, 3, 1, 1, 2, 3, 2, 3]
def baseStart_1860470 : Nat := 118140960795 + 1860470 * 2 ^ 59
def prefixEnd_1860470 : Nat := 4983230072969 + 3 ^ 40 * 1860470 * 2
def baseEnd_1860470 : Nat := 636876902180294090845907

theorem tailTrace_1860470 : CollatzResearch.WordTrace tailWord_1860470 prefixEnd_1860470 636876902180294090845907 := by
  unfold tailWord_1860470
  simp only [CollatzResearch.WordTrace]
  refine ⟨4241057223115150489018679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45237943713228271882865909 4241057223115150489018679)
  ·
    refine ⟨6361585834672725733528019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4241057223115150489018679 6361585834672725733528019)
    ·
      refine ⟨9542378752009088600292029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6361585834672725733528019 9542378752009088600292029)
      ·
        refine ⟨3578392032003408225109511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9542378752009088600292029 3578392032003408225109511)
        ·
          refine ⟨5367588048005112337664267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3578392032003408225109511 5367588048005112337664267)
          ·
            refine ⟨8051382072007668506496401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5367588048005112337664267 8051382072007668506496401)
            ·
              refine ⟨6038536554005751379872301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8051382072007668506496401 6038536554005751379872301)
              ·
                refine ⟨2264451207752156767452113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6038536554005751379872301 2264451207752156767452113)
                ·
                  refine ⟨1698338405814117575589085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2264451207752156767452113 1698338405814117575589085)
                  ·
                    refine ⟨636876902180294090845907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1698338405814117575589085 636876902180294090845907)
                    ·
                      rfl

theorem cell22_1860470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_1860470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1860470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1860470 prefixEnd_1860470 := by exact prefixLift 1860470
  have htrace : WordTrace (prefixWord ++ tailWord_1860470) baseStart_1860470 baseEnd_1860470 := by
    simpa [prefixWord, tailWord_1860470, baseEnd_1860470] using wordTrace_append hprefix tailTrace_1860470
  have hstable : (prefixWord ++ tailWord_1860470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860470).length < 2 ^ (prefixWord ++ tailWord_1860470).sum := by decide
  have hdescent : baseEnd_1860470 < baseStart_1860470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860511 : List Nat := [1, 1, 2, 5, 2, 2, 1, 1, 7]
def baseStart_1860511 : Nat := 118140960795 + 1860511 * 2 ^ 59
def prefixEnd_1860511 : Nat := 4983230072969 + 3 ^ 40 * 1860511 * 2
def baseEnd_1860511 : Nat := 212296979106061216856927

theorem tailTrace_1860511 : CollatzResearch.WordTrace tailWord_1860511 prefixEnd_1860511 212296979106061216856927 := by
  unfold tailWord_1860511
  simp only [CollatzResearch.WordTrace]
  refine ⟨67858410962693871826541387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45238940641795914551027591 67858410962693871826541387)
  ·
    refine ⟨101787616444040807739812081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67858410962693871826541387 101787616444040807739812081)
    ·
      refine ⟨76340712333030605804859061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101787616444040807739812081 76340712333030605804859061)
      ·
        refine ⟨7156941781221619294205537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76340712333030605804859061 7156941781221619294205537)
        ·
          refine ⟨5367706335916214470654153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7156941781221619294205537 5367706335916214470654153)
          ·
            refine ⟨4025779751937160852990615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5367706335916214470654153 4025779751937160852990615)
            ·
              refine ⟨6038669627905741279485923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4025779751937160852990615 6038669627905741279485923)
              ·
                refine ⟨9058004441858611919228885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6038669627905741279485923 9058004441858611919228885)
                ·
                  refine ⟨212296979106061216856927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9058004441858611919228885 212296979106061216856927)
                  ·
                    rfl

theorem cell22_1860511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 7].length) (baseStart_1860511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1860511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1860511 prefixEnd_1860511 := by exact prefixLift 1860511
  have htrace : WordTrace (prefixWord ++ tailWord_1860511) baseStart_1860511 baseEnd_1860511 := by
    simpa [prefixWord, tailWord_1860511, baseEnd_1860511] using wordTrace_append hprefix tailTrace_1860511
  have hstable : (prefixWord ++ tailWord_1860511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860511).length < 2 ^ (prefixWord ++ tailWord_1860511).sum := by decide
  have hdescent : baseEnd_1860511 < baseStart_1860511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860534 : List Nat := [5, 1, 4, 1, 1, 2, 2, 6]
def baseStart_1860534 : Nat := 118140960795 + 1860534 * 2 ^ 59
def prefixEnd_1860534 : Nat := 4983230072969 + 3 ^ 40 * 1860534 * 2
def baseEnd_1860534 : Nat := 70766534520913250805079

theorem tailTrace_1860534 : CollatzResearch.WordTrace tailWord_1860534 prefixEnd_1860534 70766534520913250805079 := by
  unfold tailWord_1860534
  simp only [CollatzResearch.WordTrace]
  refine ⟨4241203115100659172164291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45239499894407031169752437 4241203115100659172164291)
  ·
    refine ⟨6361804672650988758246437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4241203115100659172164291 6361804672650988758246437)
    ·
      refine ⟨1192838376122060392171207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6361804672650988758246437 1192838376122060392171207)
      ·
        refine ⟨1789257564183090588256811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1192838376122060392171207 1789257564183090588256811)
        ·
          refine ⟨2683886346274635882385217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1789257564183090588256811 2683886346274635882385217)
          ·
            refine ⟨2012914759705976911788913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2683886346274635882385217 2012914759705976911788913)
            ·
              refine ⟨1509686069779482683841685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2012914759705976911788913 1509686069779482683841685)
              ·
                refine ⟨70766534520913250805079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1509686069779482683841685 70766534520913250805079)
                ·
                  rfl

theorem cell22_1860534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_1860534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1860534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1860534 prefixEnd_1860534 := by exact prefixLift 1860534
  have htrace : WordTrace (prefixWord ++ tailWord_1860534) baseStart_1860534 baseEnd_1860534 := by
    simpa [prefixWord, tailWord_1860534, baseEnd_1860534] using wordTrace_append hprefix tailTrace_1860534
  have hstable : (prefixWord ++ tailWord_1860534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860534).length < 2 ^ (prefixWord ++ tailWord_1860534).sum := by decide
  have hdescent : baseEnd_1860534 < baseStart_1860534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860558 : List Nat := [4, 1, 1, 1, 2, 3, 2, 3, 1, 4]
def baseStart_1860558 : Nat := 118140960795 + 1860558 * 2 ^ 59
def prefixEnd_1860558 : Nat := 4983230072969 + 3 ^ 40 * 1860558 * 2
def baseEnd_1860558 : Nat := 636907026378691194645637

theorem tailTrace_1860558 : CollatzResearch.WordTrace tailWord_1860558 prefixEnd_1860558 636907026378691194645637 := by
  unfold tailWord_1860558
  simp only [CollatzResearch.WordTrace]
  refine ⟨8482515649190449856687791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45240083462349065902334885 8482515649190449856687791)
  ·
    refine ⟨12723773473785674785031687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8482515649190449856687791 12723773473785674785031687)
    ·
      refine ⟨19085660210678512177547531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12723773473785674785031687 19085660210678512177547531)
      ·
        refine ⟨28628490316017768266321297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19085660210678512177547531 28628490316017768266321297)
        ·
          refine ⟨21471367737013326199740973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28628490316017768266321297 21471367737013326199740973)
          ·
            refine ⟨8051762901379997324902865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21471367737013326199740973 8051762901379997324902865)
            ·
              refine ⟨6038822176034997993677149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8051762901379997324902865 6038822176034997993677149)
              ·
                refine ⟨2264558316013124247628931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6038822176034997993677149 2264558316013124247628931)
                ·
                  refine ⟨3396837474019686371443397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2264558316013124247628931 3396837474019686371443397)
                  ·
                    refine ⟨636907026378691194645637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3396837474019686371443397 636907026378691194645637)
                    ·
                      rfl

theorem cell22_1860558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_1860558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1860558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1860558 prefixEnd_1860558 := by exact prefixLift 1860558
  have htrace : WordTrace (prefixWord ++ tailWord_1860558) baseStart_1860558 baseEnd_1860558 := by
    simpa [prefixWord, tailWord_1860558, baseEnd_1860558] using wordTrace_append hprefix tailTrace_1860558
  have hstable : (prefixWord ++ tailWord_1860558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860558).length < 2 ^ (prefixWord ++ tailWord_1860558).sum := by decide
  have hdescent : baseEnd_1860558 < baseStart_1860558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860573 : List Nat := [1, 4, 3, 1, 2, 1, 3, 1, 6]
def baseStart_1860573 : Nat := 118140960795 + 1860573 * 2 ^ 59
def prefixEnd_1860573 : Nat := 4983230072969 + 3 ^ 40 * 1860573 * 2
def baseEnd_1860573 : Nat := 212304053728412051840197

theorem tailTrace_1860573 : CollatzResearch.WordTrace tailWord_1860573 prefixEnd_1860573 212304053728412051840197 := by
  unfold tailWord_1860573
  simp only [CollatzResearch.WordTrace]
  refine ⟨67860672288469256415298373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45240448192312837610198915 67860672288469256415298373)
  ·
    refine ⟨12723876054087985577868445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67860672288469256415298373 12723876054087985577868445)
    ·
      refine ⟨4771453520282994591700667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12723876054087985577868445 4771453520282994591700667)
      ·
        refine ⟨7157180280424491887551001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4771453520282994591700667 7157180280424491887551001)
        ·
          refine ⟨5367885210318368915663251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7157180280424491887551001 5367885210318368915663251)
          ·
            refine ⟨8051827815477553373494877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5367885210318368915663251 8051827815477553373494877)
            ·
              refine ⟨3019435430804082515060579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8051827815477553373494877 3019435430804082515060579)
              ·
                refine ⟨4529153146206123772590869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3019435430804082515060579 4529153146206123772590869)
                ·
                  refine ⟨212304053728412051840197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4529153146206123772590869 212304053728412051840197)
                  ·
                    rfl

theorem cell22_1860573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_1860573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1860573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1860573 prefixEnd_1860573 := by exact prefixLift 1860573
  have htrace : WordTrace (prefixWord ++ tailWord_1860573) baseStart_1860573 baseEnd_1860573 := by
    simpa [prefixWord, tailWord_1860573, baseEnd_1860573] using wordTrace_append hprefix tailTrace_1860573
  have hstable : (prefixWord ++ tailWord_1860573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860573).length < 2 ^ (prefixWord ++ tailWord_1860573).sum := by decide
  have hdescent : baseEnd_1860573 < baseStart_1860573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860661 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 3, 7]
def baseStart_1860661 : Nat := 118140960795 + 1860661 * 2 ^ 59
def prefixEnd_1860661 : Nat := 4983230072969 + 3 ^ 40 * 1860661 * 2
def baseEnd_1860661 : Nat := 636942285383633259320321

theorem tailTrace_1860661 : CollatzResearch.WordTrace tailWord_1860661 prefixEnd_1860661 636942285383633259320321 := by
  unfold tailWord_1860661
  simp only [CollatzResearch.WordTrace]
  refine ⟨67863881912150447444501837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45242587941433631629667891 67863881912150447444501837)
  ·
    refine ⟨25448955717056417791688189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67863881912150447444501837 25448955717056417791688189)
    ·
      refine ⟨9543358393896156671883071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25448955717056417791688189 9543358393896156671883071)
      ·
        refine ⟨14315037590844235007824607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9543358393896156671883071 14315037590844235007824607)
        ·
          refine ⟨21472556386266352511736911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14315037590844235007824607 21472556386266352511736911)
          ·
            refine ⟨32208834579399528767605367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21472556386266352511736911 32208834579399528767605367)
            ·
              refine ⟨48313251869099293151408051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32208834579399528767605367 48313251869099293151408051)
              ·
                refine ⟨72469877803648939727112077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48313251869099293151408051 72469877803648939727112077)
                ·
                  refine ⟨27176204176368352397667029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72469877803648939727112077 27176204176368352397667029)
                  ·
                    refine ⟨636942285383633259320321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27176204176368352397667029 636942285383633259320321)
                    ·
                      rfl

theorem cell22_1860661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_1860661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1860661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1860661 prefixEnd_1860661 := by exact prefixLift 1860661
  have htrace : WordTrace (prefixWord ++ tailWord_1860661) baseStart_1860661 baseEnd_1860661 := by
    simpa [prefixWord, tailWord_1860661, baseEnd_1860661] using wordTrace_append hprefix tailTrace_1860661
  have hstable : (prefixWord ++ tailWord_1860661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860661).length < 2 ^ (prefixWord ++ tailWord_1860661).sum := by decide
  have hdescent : baseEnd_1860661 < baseStart_1860661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860691 : List Nat := [1, 1, 1, 2, 1, 1, 2, 7, 6]
def baseStart_1860691 : Nat := 118140960795 + 1860691 * 2 ^ 59
def prefixEnd_1860691 : Nat := 4983230072969 + 3 ^ 40 * 1860691 * 2
def baseEnd_1860691 : Nat := 212317518332241060356743

theorem tailTrace_1860691 : CollatzResearch.WordTrace tailWord_1860691 prefixEnd_1860691 212317518332241060356743 := by
  unfold tailWord_1860691
  simp only [CollatzResearch.WordTrace]
  refine ⟨67864976102041762568093927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45243317401361175045395951 67864976102041762568093927)
  ·
    refine ⟨101797464153062643852140891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67864976102041762568093927 101797464153062643852140891)
    ·
      refine ⟨152696196229593965778211337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101797464153062643852140891 152696196229593965778211337)
      ·
        refine ⟨114522147172195474333658503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152696196229593965778211337 114522147172195474333658503)
        ·
          refine ⟨171783220758293211500487755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114522147172195474333658503 171783220758293211500487755)
          ·
            refine ⟨257674831137439817250731633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171783220758293211500487755 257674831137439817250731633)
            ·
              refine ⟨193256123353079862938048725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257674831137439817250731633 193256123353079862938048725)
              ·
                refine ⟨4529440391087809287610517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 193256123353079862938048725 4529440391087809287610517)
                ·
                  refine ⟨212317518332241060356743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4529440391087809287610517 212317518332241060356743)
                  ·
                    rfl

theorem cell22_1860691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 6].length) (baseStart_1860691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1860691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1860691 prefixEnd_1860691 := by exact prefixLift 1860691
  have htrace : WordTrace (prefixWord ++ tailWord_1860691) baseStart_1860691 baseEnd_1860691 := by
    simpa [prefixWord, tailWord_1860691, baseEnd_1860691] using wordTrace_append hprefix tailTrace_1860691
  have hstable : (prefixWord ++ tailWord_1860691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860691).length < 2 ^ (prefixWord ++ tailWord_1860691).sum := by decide
  have hdescent : baseEnd_1860691 < baseStart_1860691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860736 : List Nat := [2, 1, 1, 2, 1, 3, 12]
def baseStart_1860736 : Nat := 118140960795 + 1860736 * 2 ^ 59
def prefixEnd_1860736 : Nat := 4983230072969 + 3 ^ 40 * 1860736 * 2
def baseEnd_1860736 : Nat := 23591405904309557914633

theorem tailTrace_1860736 : CollatzResearch.WordTrace tailWord_1860736 prefixEnd_1860736 23591405904309557914633 := by
  unfold tailWord_1860736
  simp only [CollatzResearch.WordTrace]
  refine ⟨33933308693439367626741031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45244411591252490168988041 33933308693439367626741031)
  ·
    refine ⟨50899963040159051440111547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33933308693439367626741031 50899963040159051440111547)
    ·
      refine ⟨76349944560238577160167321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50899963040159051440111547 76349944560238577160167321)
      ·
        refine ⟨57262458420178932870125491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76349944560238577160167321 57262458420178932870125491)
        ·
          refine ⟨85893687630268399305188237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57262458420178932870125491 85893687630268399305188237)
          ·
            refine ⟨32210132861350649739445589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85893687630268399305188237 32210132861350649739445589)
            ·
              refine ⟨23591405904309557914633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 32210132861350649739445589 23591405904309557914633)
              ·
                rfl

theorem cell22_1860736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 12].length) (baseStart_1860736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1860736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1860736 prefixEnd_1860736 := by exact prefixLift 1860736
  have htrace : WordTrace (prefixWord ++ tailWord_1860736) baseStart_1860736 baseEnd_1860736 := by
    simpa [prefixWord, tailWord_1860736, baseEnd_1860736] using wordTrace_append hprefix tailTrace_1860736
  have hstable : (prefixWord ++ tailWord_1860736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860736).length < 2 ^ (prefixWord ++ tailWord_1860736).sum := by decide
  have hdescent : baseEnd_1860736 < baseStart_1860736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860740 : List Nat := [2, 3, 2, 1, 2, 2, 2, 1, 4, 3]
def baseStart_1860740 : Nat := 118140960795 + 1860740 * 2 ^ 59
def prefixEnd_1860740 : Nat := 4983230072969 + 3 ^ 40 * 1860740 * 2
def baseEnd_1860740 : Nat := 636969328698103386595079

theorem tailTrace_1860740 : CollatzResearch.WordTrace tailWord_1860740 prefixEnd_1860740 636969328698103386595079 := by
  unfold tailWord_1860740
  simp only [CollatzResearch.WordTrace]
  refine ⟨33933381639432121968313837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45244508852576162624418449 33933381639432121968313837)
  ·
    refine ⟨12725018114787045738117689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33933381639432121968313837 12725018114787045738117689)
    ·
      refine ⟨9543763586090284303588267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12725018114787045738117689 9543763586090284303588267)
      ·
        refine ⟨14315645379135426455382401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9543763586090284303588267 14315645379135426455382401)
        ·
          refine ⟨10736734034351569841536801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14315645379135426455382401 10736734034351569841536801)
          ·
            refine ⟨8052550525763677381152601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10736734034351569841536801 8052550525763677381152601)
            ·
              refine ⟨6039412894322758035864451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8052550525763677381152601 6039412894322758035864451)
              ·
                refine ⟨9059119341484137053796677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6039412894322758035864451 9059119341484137053796677)
                ·
                  refine ⟨1698584876528275697586877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9059119341484137053796677 1698584876528275697586877)
                  ·
                    refine ⟨636969328698103386595079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1698584876528275697586877 636969328698103386595079)
                    ·
                      rfl

theorem cell22_1860740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_1860740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1860740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1860740 prefixEnd_1860740 := by exact prefixLift 1860740
  have htrace : WordTrace (prefixWord ++ tailWord_1860740) baseStart_1860740 baseEnd_1860740 := by
    simpa [prefixWord, tailWord_1860740, baseEnd_1860740] using wordTrace_append hprefix tailTrace_1860740
  have hstable : (prefixWord ++ tailWord_1860740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860740).length < 2 ^ (prefixWord ++ tailWord_1860740).sum := by decide
  have hdescent : baseEnd_1860740 < baseStart_1860740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860751 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 3, 9]
def baseStart_1860751 : Nat := 118140960795 + 1860751 * 2 ^ 59
def prefixEnd_1860751 : Nat := 4983230072969 + 3 ^ 40 * 1860751 * 2
def baseEnd_1860751 : Nat := 636973094222903024570045

theorem tailTrace_1860751 : CollatzResearch.WordTrace tailWord_1860751 prefixEnd_1860751 636973094222903024570045 := by
  unfold tailWord_1860751
  simp only [CollatzResearch.WordTrace]
  refine ⟨67867164481824392815278107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45244776321216261876852071 67867164481824392815278107)
  ·
    refine ⟨101800746722736589222917161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67867164481824392815278107 101800746722736589222917161)
    ·
      refine ⟨76350560042052441917187871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101800746722736589222917161 76350560042052441917187871)
      ·
        refine ⟨114525840063078662875781807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76350560042052441917187871 114525840063078662875781807)
        ·
          refine ⟨171788760094617994313672711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114525840063078662875781807 171788760094617994313672711)
          ·
            refine ⟨257683140141926991470509067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171788760094617994313672711 257683140141926991470509067)
            ·
              refine ⟨386524710212890487205763601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257683140141926991470509067 386524710212890487205763601)
              ·
                refine ⟨289893532659667865404322701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 386524710212890487205763601 289893532659667865404322701)
                ·
                  refine ⟨108710074747375449526621013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 289893532659667865404322701 108710074747375449526621013)
                  ·
                    refine ⟨636973094222903024570045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 108710074747375449526621013 636973094222903024570045)
                    ·
                      rfl

theorem cell22_1860751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 9].length) (baseStart_1860751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1860751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1860751 prefixEnd_1860751 := by exact prefixLift 1860751
  have htrace : WordTrace (prefixWord ++ tailWord_1860751) baseStart_1860751 baseEnd_1860751 := by
    simpa [prefixWord, tailWord_1860751, baseEnd_1860751] using wordTrace_append hprefix tailTrace_1860751
  have hstable : (prefixWord ++ tailWord_1860751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860751).length < 2 ^ (prefixWord ++ tailWord_1860751).sum := by decide
  have hdescent : baseEnd_1860751 < baseStart_1860751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860873 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 3, 6]
def baseStart_1860873 : Nat := 118140960795 + 1860873 * 2 ^ 59
def prefixEnd_1860873 : Nat := 4983230072969 + 3 ^ 40 * 1860873 * 2
def baseEnd_1860873 : Nat := 637014857316135373019671

theorem tailTrace_1860873 : CollatzResearch.WordTrace tailWord_1860873 prefixEnd_1860873 637014857316135373019671 := by
  unfold tailWord_1860873
  simp only [CollatzResearch.WordTrace]
  refine ⟨67871614187382407651219273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45247742791588271767479515 67871614187382407651219273)
  ·
    refine ⟨50903710640536805738414455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67871614187382407651219273 50903710640536805738414455)
    ·
      refine ⟨76355565960805208607621683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50903710640536805738414455 76355565960805208607621683)
      ·
        refine ⟨114533348941207812911432525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76355565960805208607621683 114533348941207812911432525)
        ·
          refine ⟨42950005852952929841787197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114533348941207812911432525 42950005852952929841787197)
          ·
            refine ⟨16106252194857348690670199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42950005852952929841787197 16106252194857348690670199)
            ·
              refine ⟨24159378292286023036005299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16106252194857348690670199 24159378292286023036005299)
              ·
                refine ⟨36239067438429034554007949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24159378292286023036005299 36239067438429034554007949)
                ·
                  refine ⟨13589650289410887957752981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36239067438429034554007949 13589650289410887957752981)
                  ·
                    refine ⟨637014857316135373019671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13589650289410887957752981 637014857316135373019671)
                    ·
                      rfl

theorem cell22_1860873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 6].length) (baseStart_1860873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1860873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1860873 prefixEnd_1860873 := by exact prefixLift 1860873
  have htrace : WordTrace (prefixWord ++ tailWord_1860873) baseStart_1860873 baseEnd_1860873 := by
    simpa [prefixWord, tailWord_1860873, baseEnd_1860873] using wordTrace_append hprefix tailTrace_1860873
  have hstable : (prefixWord ++ tailWord_1860873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860873).length < 2 ^ (prefixWord ++ tailWord_1860873).sum := by decide
  have hdescent : baseEnd_1860873 < baseStart_1860873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860875 : List Nat := [1, 1, 1, 1, 5, 3, 3, 1, 1, 5]
def baseStart_1860875 : Nat := 118140960795 + 1860875 * 2 ^ 59
def prefixEnd_1860875 : Nat := 4983230072969 + 3 ^ 40 * 1860875 * 2
def baseEnd_1860875 : Nat := 637015541957008034469665

theorem tailTrace_1860875 : CollatzResearch.WordTrace tailWord_1860875 prefixEnd_1860875 637015541957008034469665 := by
  unfold tailWord_1860875
  simp only [CollatzResearch.WordTrace]
  refine ⟨67871687133375161992792079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45247791422250107995194719 67871687133375161992792079)
  ·
    refine ⟨101807530700062742989188119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67871687133375161992792079 101807530700062742989188119)
    ·
      refine ⟨152711296050094114483782179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101807530700062742989188119 152711296050094114483782179)
      ·
        refine ⟨229066944075141171725673269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152711296050094114483782179 229066944075141171725673269)
        ·
          refine ⟨21475026007044484849281869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 229066944075141171725673269 21475026007044484849281869)
          ·
            refine ⟨8053134752641681818480701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21475026007044484849281869 8053134752641681818480701)
            ·
              refine ⟨3019925532240630681930263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8053134752641681818480701 3019925532240630681930263)
              ·
                refine ⟨4529888298360946022895395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3019925532240630681930263 4529888298360946022895395)
                ·
                  refine ⟨6794832447541419034343093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4529888298360946022895395 6794832447541419034343093)
                  ·
                    refine ⟨637015541957008034469665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6794832447541419034343093 637015541957008034469665)
                    ·
                      rfl

theorem cell22_1860875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 5].length) (baseStart_1860875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1860875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1860875 prefixEnd_1860875 := by exact prefixLift 1860875
  have htrace : WordTrace (prefixWord ++ tailWord_1860875) baseStart_1860875 baseEnd_1860875 := by
    simpa [prefixWord, tailWord_1860875, baseEnd_1860875] using wordTrace_append hprefix tailTrace_1860875
  have hstable : (prefixWord ++ tailWord_1860875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860875).length < 2 ^ (prefixWord ++ tailWord_1860875).sum := by decide
  have hdescent : baseEnd_1860875 < baseStart_1860875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860890 : List Nat := [3, 1, 1, 3, 3, 1, 2, 1, 1, 6]
def baseStart_1860890 : Nat := 118140960795 + 1860890 * 2 ^ 59
def prefixEnd_1860890 : Nat := 4983230072969 + 3 ^ 40 * 1860890 * 2
def baseEnd_1860890 : Nat := 637020676763552995344619

theorem tailTrace_1860890 : CollatzResearch.WordTrace tailWord_1860890 prefixEnd_1860890 637020676763552995344619 := by
  unfold tailWord_1860890
  simp only [CollatzResearch.WordTrace]
  refine ⟨16968058557080204888647031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45248156152213879703058749 16968058557080204888647031)
  ·
    refine ⟨25452087835620307332970547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16968058557080204888647031 25452087835620307332970547)
    ·
      refine ⟨38178131753430460999455821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25452087835620307332970547 38178131753430460999455821)
      ·
        refine ⟨14316799407536422874795933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38178131753430460999455821 14316799407536422874795933)
        ·
          refine ⟨5368799777826158578048475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14316799407536422874795933 5368799777826158578048475)
          ·
            refine ⟨8053199666739237867072713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5368799777826158578048475 8053199666739237867072713)
            ·
              refine ⟨6039899750054428400304535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8053199666739237867072713 6039899750054428400304535)
              ·
                refine ⟨9059849625081642600456803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6039899750054428400304535 9059849625081642600456803)
                ·
                  refine ⟨13589774437622463900685205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9059849625081642600456803 13589774437622463900685205)
                  ·
                    refine ⟨637020676763552995344619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13589774437622463900685205 637020676763552995344619)
                    ·
                      rfl

theorem cell22_1860890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_1860890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1860890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1860890 prefixEnd_1860890 := by exact prefixLift 1860890
  have htrace : WordTrace (prefixWord ++ tailWord_1860890) baseStart_1860890 baseEnd_1860890 := by
    simpa [prefixWord, tailWord_1860890, baseEnd_1860890] using wordTrace_append hprefix tailTrace_1860890
  have hstable : (prefixWord ++ tailWord_1860890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860890).length < 2 ^ (prefixWord ++ tailWord_1860890).sum := by decide
  have hdescent : baseEnd_1860890 < baseStart_1860890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860909 : List Nat := [1, 5, 3, 1, 1, 1, 2, 1, 4, 3]
def baseStart_1860909 : Nat := 118140960795 + 1860909 * 2 ^ 59
def prefixEnd_1860909 : Nat := 4983230072969 + 3 ^ 40 * 1860909 * 2
def baseEnd_1860909 : Nat := 637027180851843279119561

theorem tailTrace_1860909 : CollatzResearch.WordTrace tailWord_1860909 prefixEnd_1860909 637027180851843279119561 := by
  unfold tailWord_1860909
  simp only [CollatzResearch.WordTrace]
  refine ⟨67872927215251985799529781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45248618143501323866353187 67872927215251985799529781)
  ·
    refine ⟨6363086926429873668705917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67872927215251985799529781 6363086926429873668705917)
    ·
      refine ⟨2386157597411202625764719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6363086926429873668705917 2386157597411202625764719)
      ·
        refine ⟨3579236396116803938647079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2386157597411202625764719 3579236396116803938647079)
        ·
          refine ⟨5368854594175205907970619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3579236396116803938647079 5368854594175205907970619)
          ·
            refine ⟨8053281891262808861955929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5368854594175205907970619 8053281891262808861955929)
            ·
              refine ⟨6039961418447106646466947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8053281891262808861955929 6039961418447106646466947)
              ·
                refine ⟨9059942127670659969700421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6039961418447106646466947 9059942127670659969700421)
                ·
                  refine ⟨1698739148938248744318829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9059942127670659969700421 1698739148938248744318829)
                  ·
                    refine ⟨637027180851843279119561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1698739148938248744318829 637027180851843279119561)
                    ·
                      rfl

theorem cell22_1860909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_1860909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1860909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1860909 prefixEnd_1860909 := by exact prefixLift 1860909
  have htrace : WordTrace (prefixWord ++ tailWord_1860909) baseStart_1860909 baseEnd_1860909 := by
    simpa [prefixWord, tailWord_1860909, baseEnd_1860909] using wordTrace_append hprefix tailTrace_1860909
  have hstable : (prefixWord ++ tailWord_1860909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860909).length < 2 ^ (prefixWord ++ tailWord_1860909).sum := by decide
  have hdescent : baseEnd_1860909 < baseStart_1860909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860941 : List Nat := [1, 6, 1, 3, 1, 1, 2, 1, 2, 4]
def baseStart_1860941 : Nat := 118140960795 + 1860941 * 2 ^ 59
def prefixEnd_1860941 : Nat := 4983230072969 + 3 ^ 40 * 1860941 * 2
def baseEnd_1860941 : Nat := 637038135105805862319463

theorem tailTrace_1860941 : CollatzResearch.WordTrace tailWord_1860941 prefixEnd_1860941 637038135105805862319463 := by
  unfold tailWord_1860941
  simp only [CollatzResearch.WordTrace]
  refine ⟨67874094351136055264694677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45249396234090703509796451 67874094351136055264694677)
  ·
    refine ⟨3181598172709502590532563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 67874094351136055264694677 3181598172709502590532563)
    ·
      refine ⟨4772397259064253885798845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3181598172709502590532563 4772397259064253885798845)
      ·
        refine ⟨1789648972149095207174567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4772397259064253885798845 1789648972149095207174567)
        ·
          refine ⟨2684473458223642810761851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1789648972149095207174567 2684473458223642810761851)
          ·
            refine ⟨4026710187335464216142777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2684473458223642810761851 4026710187335464216142777)
            ·
              refine ⟨3020032640501598162107083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4026710187335464216142777 3020032640501598162107083)
              ·
                refine ⟨4530048960752397243160625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3020032640501598162107083 4530048960752397243160625)
                ·
                  refine ⟨3397536720564297932370469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4530048960752397243160625 3397536720564297932370469)
                  ·
                    refine ⟨637038135105805862319463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3397536720564297932370469 637038135105805862319463)
                    ·
                      rfl

theorem cell22_1860941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_1860941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1860941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1860941 prefixEnd_1860941 := by exact prefixLift 1860941
  have htrace : WordTrace (prefixWord ++ tailWord_1860941) baseStart_1860941 baseEnd_1860941 := by
    simpa [prefixWord, tailWord_1860941, baseEnd_1860941] using wordTrace_append hprefix tailTrace_1860941
  have hstable : (prefixWord ++ tailWord_1860941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860941).length < 2 ^ (prefixWord ++ tailWord_1860941).sum := by decide
  have hdescent : baseEnd_1860941 < baseStart_1860941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860965 : List Nat := [1, 3, 1, 3, 1, 2, 2, 2, 2, 5]
def baseStart_1860965 : Nat := 118140960795 + 1860965 * 2 ^ 59
def prefixEnd_1860965 : Nat := 4983230072969 + 3 ^ 40 * 1860965 * 2
def baseEnd_1860965 : Nat := 637046350796277799719389

theorem tailTrace_1860965 : CollatzResearch.WordTrace tailWord_1860965 prefixEnd_1860965 637046350796277799719389 := by
  unfold tailWord_1860965
  simp only [CollatzResearch.WordTrace]
  refine ⟨67874969703049107363568349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45249979802032738242378899 67874969703049107363568349)
  ·
    refine ⟨25453113638643415261338131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67874969703049107363568349 25453113638643415261338131)
    ·
      refine ⟨38179670457965122892007197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25453113638643415261338131 38179670457965122892007197)
      ·
        refine ⟨14317376421736921084502699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38179670457965122892007197 14317376421736921084502699)
        ·
          refine ⟨21476064632605381626754049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14317376421736921084502699 21476064632605381626754049)
          ·
            refine ⟨16107048474454036220065537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21476064632605381626754049 16107048474454036220065537)
            ·
              refine ⟨12080286355840527165049153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16107048474454036220065537 12080286355840527165049153)
              ·
                refine ⟨9060214766880395373786865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12080286355840527165049153 9060214766880395373786865)
                ·
                  refine ⟨6795161075160296530340149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9060214766880395373786865 6795161075160296530340149)
                  ·
                    refine ⟨637046350796277799719389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6795161075160296530340149 637046350796277799719389)
                    ·
                      rfl

theorem cell22_1860965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_1860965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1860965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1860965 prefixEnd_1860965 := by exact prefixLift 1860965
  have htrace : WordTrace (prefixWord ++ tailWord_1860965) baseStart_1860965 baseEnd_1860965 := by
    simpa [prefixWord, tailWord_1860965, baseEnd_1860965] using wordTrace_append hprefix tailTrace_1860965
  have hstable : (prefixWord ++ tailWord_1860965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860965).length < 2 ^ (prefixWord ++ tailWord_1860965).sum := by decide
  have hdescent : baseEnd_1860965 < baseStart_1860965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860995 : List Nat := [1, 1, 1, 3, 5, 1, 1, 1, 8]
def baseStart_1860995 : Nat := 118140960795 + 1860995 * 2 ^ 59
def prefixEnd_1860995 : Nat := 4983230072969 + 3 ^ 40 * 1860995 * 2
def baseEnd_1860995 : Nat := 212352206803122573823099

theorem tailTrace_1860995 : CollatzResearch.WordTrace tailWord_1860995 prefixEnd_1860995 212352206803122573823099 := by
  unfold tailWord_1860995
  simp only [CollatzResearch.WordTrace]
  refine ⟨67876063892940422487160439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45250709261960281658106959 67876063892940422487160439)
  ·
    refine ⟨101814095839410633730740659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67876063892940422487160439 101814095839410633730740659)
    ·
      refine ⟨152721143759115950596110989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101814095839410633730740659 152721143759115950596110989)
      ·
        refine ⟨57270428909668481473541621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152721143759115950596110989 57270428909668481473541621)
        ·
          refine ⟨5369102710281420138144527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57270428909668481473541621 5369102710281420138144527)
          ·
            refine ⟨8053654065422130207216791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5369102710281420138144527 8053654065422130207216791)
            ·
              refine ⟨12080481098133195310825187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8053654065422130207216791 12080481098133195310825187)
              ·
                refine ⟨18120721647199792966237781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12080481098133195310825187 18120721647199792966237781)
                ·
                  refine ⟨212352206803122573823099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18120721647199792966237781 212352206803122573823099)
                  ·
                    rfl

theorem cell22_1860995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 8].length) (baseStart_1860995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1860995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1860995 prefixEnd_1860995 := by exact prefixLift 1860995
  have htrace : WordTrace (prefixWord ++ tailWord_1860995) baseStart_1860995 baseEnd_1860995 := by
    simpa [prefixWord, tailWord_1860995, baseEnd_1860995] using wordTrace_append hprefix tailTrace_1860995
  have hstable : (prefixWord ++ tailWord_1860995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860995).length < 2 ^ (prefixWord ++ tailWord_1860995).sum := by decide
  have hdescent : baseEnd_1860995 < baseStart_1860995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861027 : List Nat := [1, 1, 1, 4, 1, 3, 3, 1, 4, 3]
def baseStart_1861027 : Nat := 118140960795 + 1861027 * 2 ^ 59
def prefixEnd_1861027 : Nat := 4983230072969 + 3 ^ 40 * 1861027 * 2
def baseEnd_1861027 : Nat := 637067574663330304669199

theorem tailTrace_1861027 : CollatzResearch.WordTrace tailWord_1861027 prefixEnd_1861027 637067574663330304669199 := by
  unfold tailWord_1861027
  simp only [CollatzResearch.WordTrace]
  refine ⟨67877231028824491952325335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45251487352549661301550223 67877231028824491952325335)
  ·
    refine ⟨101815846543236737928488003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67877231028824491952325335 101815846543236737928488003)
    ·
      refine ⟨152723769814855106892732005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101815846543236737928488003 152723769814855106892732005)
      ·
        refine ⟨28635706840285332542387251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152723769814855106892732005 28635706840285332542387251)
        ·
          refine ⟨42953560260427998813580877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28635706840285332542387251 42953560260427998813580877)
          ·
            refine ⟨16107585097660499555092829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42953560260427998813580877 16107585097660499555092829)
            ·
              refine ⟨6040344411622687333159811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16107585097660499555092829 6040344411622687333159811)
              ·
                refine ⟨9060516617434030999739717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6040344411622687333159811 9060516617434030999739717)
                ·
                  refine ⟨1698846865768880812451197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9060516617434030999739717 1698846865768880812451197)
                  ·
                    refine ⟨637067574663330304669199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1698846865768880812451197 637067574663330304669199)
                    ·
                      rfl

theorem cell22_1861027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 4, 3].length) (baseStart_1861027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1861027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1861027 prefixEnd_1861027 := by exact prefixLift 1861027
  have htrace : WordTrace (prefixWord ++ tailWord_1861027) baseStart_1861027 baseEnd_1861027 := by
    simpa [prefixWord, tailWord_1861027, baseEnd_1861027] using wordTrace_append hprefix tailTrace_1861027
  have hstable : (prefixWord ++ tailWord_1861027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861027).length < 2 ^ (prefixWord ++ tailWord_1861027).sum := by decide
  have hdescent : baseEnd_1861027 < baseStart_1861027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861089 : List Nat := [1, 2, 3, 1, 2, 3, 3, 1, 3, 3]
def baseStart_1861089 : Nat := 118140960795 + 1861089 * 2 ^ 59
def prefixEnd_1861089 : Nat := 4983230072969 + 3 ^ 40 * 1861089 * 2
def baseEnd_1861089 : Nat := 637088798530382809619009

theorem tailTrace_1861089 : CollatzResearch.WordTrace tailWord_1861089 prefixEnd_1861089 637088798530382809619009 := by
  unfold tailWord_1861089
  simp only [CollatzResearch.WordTrace]
  refine ⟨67879492354599876541082321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45252994903066584360721547 67879492354599876541082321)
  ·
    refine ⟨50909619265949907405811741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67879492354599876541082321 50909619265949907405811741)
    ·
      refine ⟨19091107224731215277179403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50909619265949907405811741 19091107224731215277179403)
      ·
        refine ⟨28636660837096822915769105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19091107224731215277179403 28636660837096822915769105)
        ·
          refine ⟨21477495627822617186826829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28636660837096822915769105 21477495627822617186826829)
          ·
            refine ⟨8054060860433481445060061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21477495627822617186826829 8054060860433481445060061)
            ·
              refine ⟨3020272822662555541897523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8054060860433481445060061 3020272822662555541897523)
              ·
                refine ⟨4530409233993833312846285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3020272822662555541897523 4530409233993833312846285)
                ·
                  refine ⟨1698903462747687492317357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4530409233993833312846285 1698903462747687492317357)
                  ·
                    refine ⟨637088798530382809619009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1698903462747687492317357 637088798530382809619009)
                    ·
                      rfl

theorem cell22_1861089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_1861089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1861089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1861089 prefixEnd_1861089 := by exact prefixLift 1861089
  have htrace : WordTrace (prefixWord ++ tailWord_1861089) baseStart_1861089 baseEnd_1861089 := by
    simpa [prefixWord, tailWord_1861089, baseEnd_1861089] using wordTrace_append hprefix tailTrace_1861089
  have hstable : (prefixWord ++ tailWord_1861089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861089).length < 2 ^ (prefixWord ++ tailWord_1861089).sum := by decide
  have hdescent : baseEnd_1861089 < baseStart_1861089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861115 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 2, 8]
def baseStart_1861115 : Nat := 118140960795 + 1861115 * 2 ^ 59
def prefixEnd_1861115 : Nat := 4983230072969 + 3 ^ 40 * 1861115 * 2
def baseEnd_1861115 : Nat := 637097698861727408468929

theorem tailTrace_1861115 : CollatzResearch.WordTrace tailWord_1861115 prefixEnd_1861115 637097698861727408468929 := by
  unfold tailWord_1861115
  simp only [CollatzResearch.WordTrace]
  refine ⟨67880440652505682981528799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45253627101670455321019199 67880440652505682981528799)
  ·
    refine ⟨101820660978758524472293199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67880440652505682981528799 101820660978758524472293199)
    ·
      refine ⟨152730991468137786708439799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101820660978758524472293199 152730991468137786708439799)
      ·
        refine ⟨229096487202206680062659699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152730991468137786708439799 229096487202206680062659699)
        ·
          refine ⟨343644730803310020093989549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229096487202206680062659699 343644730803310020093989549)
          ·
            refine ⟨128866774051241257535246081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 343644730803310020093989549 128866774051241257535246081)
            ·
              refine ⟨96650080538430943151434561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128866774051241257535246081 96650080538430943151434561)
              ·
                refine ⟨72487560403823207363575921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96650080538430943151434561 72487560403823207363575921)
                ·
                  refine ⟨54365670302867405522681941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72487560403823207363575921 54365670302867405522681941)
                  ·
                    refine ⟨637097698861727408468929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54365670302867405522681941 637097698861727408468929)
                    ·
                      rfl

theorem cell22_1861115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 8].length) (baseStart_1861115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1861115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1861115 prefixEnd_1861115 := by exact prefixLift 1861115
  have htrace : WordTrace (prefixWord ++ tailWord_1861115) baseStart_1861115 baseEnd_1861115 := by
    simpa [prefixWord, tailWord_1861115, baseEnd_1861115] using wordTrace_append hprefix tailTrace_1861115
  have hstable : (prefixWord ++ tailWord_1861115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861115).length < 2 ^ (prefixWord ++ tailWord_1861115).sum := by decide
  have hdescent : baseEnd_1861115 < baseStart_1861115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861140 : List Nat := [2, 4, 3, 1, 2, 1, 1, 4, 1, 3]
def baseStart_1861140 : Nat := 118140960795 + 1861140 * 2 ^ 59
def prefixEnd_1861140 : Nat := 4983230072969 + 3 ^ 40 * 1861140 * 2
def baseEnd_1861140 : Nat := 637106256872635676593853

theorem tailTrace_1861140 : CollatzResearch.WordTrace tailWord_1861140 prefixEnd_1861140 637106256872635676593853 := by
  unfold tailWord_1861140
  simp only [CollatzResearch.WordTrace]
  refine ⟨33940676238707556125594437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45254234984943408167459249 33940676238707556125594437)
  ·
    refine ⟨6363876794757666773548957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33940676238707556125594437 6363876794757666773548957)
    ·
      refine ⟨2386453798034125040080859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6363876794757666773548957 2386453798034125040080859)
      ·
        refine ⟨3579680697051187560121289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2386453798034125040080859 3579680697051187560121289)
        ·
          refine ⟨2684760522788390670090967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3579680697051187560121289 2684760522788390670090967)
          ·
            refine ⟨4027140784182586005136451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2684760522788390670090967 4027140784182586005136451)
            ·
              refine ⟨6040711176273879007704677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4027140784182586005136451 6040711176273879007704677)
              ·
                refine ⟨1132633345551352313944627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6040711176273879007704677 1132633345551352313944627)
                ·
                  refine ⟨1698950018327028470916941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1132633345551352313944627 1698950018327028470916941)
                  ·
                    refine ⟨637106256872635676593853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1698950018327028470916941 637106256872635676593853)
                    ·
                      rfl

theorem cell22_1861140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_1861140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1861140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1861140 prefixEnd_1861140 := by exact prefixLift 1861140
  have htrace : WordTrace (prefixWord ++ tailWord_1861140) baseStart_1861140 baseEnd_1861140 := by
    simpa [prefixWord, tailWord_1861140, baseEnd_1861140] using wordTrace_append hprefix tailTrace_1861140
  have hstable : (prefixWord ++ tailWord_1861140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861140).length < 2 ^ (prefixWord ++ tailWord_1861140).sum := by decide
  have hdescent : baseEnd_1861140 < baseStart_1861140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861196 : List Nat := [2, 2, 1, 3, 1, 3, 3, 2, 2, 3]
def baseStart_1861196 : Nat := 118140960795 + 1861196 * 2 ^ 59
def prefixEnd_1861196 : Nat := 4983230072969 + 3 ^ 40 * 1861196 * 2
def baseEnd_1861196 : Nat := 637125426817070197193681

theorem tailTrace_1861196 : CollatzResearch.WordTrace tailWord_1861196 prefixEnd_1861196 637125426817070197193681 := by
  unfold tailWord_1861196
  simp only [CollatzResearch.WordTrace]
  refine ⟨33941697482606116907613721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45255596643474822543484961 33941697482606116907613721)
  ·
    refine ⟨25456273111954587680710291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33941697482606116907613721 25456273111954587680710291)
    ·
      refine ⟨38184409667931881521065437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25456273111954587680710291 38184409667931881521065437)
      ·
        refine ⟨14319153625474455570399539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38184409667931881521065437 14319153625474455570399539)
        ·
          refine ⟨21478730438211683355599309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14319153625474455570399539 21478730438211683355599309)
          ·
            refine ⟨8054523914329381258349741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21478730438211683355599309 8054523914329381258349741)
            ·
              refine ⟨3020446467873517971881153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8054523914329381258349741 3020446467873517971881153)
              ·
                refine ⟨2265334850905138478910865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3020446467873517971881153 2265334850905138478910865)
                ·
                  refine ⟨1699001138178853859183149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2265334850905138478910865 1699001138178853859183149)
                  ·
                    refine ⟨637125426817070197193681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1699001138178853859183149 637125426817070197193681)
                    ·
                      rfl

theorem cell22_1861196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 2, 3].length) (baseStart_1861196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1861196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1861196 prefixEnd_1861196 := by exact prefixLift 1861196
  have htrace : WordTrace (prefixWord ++ tailWord_1861196) baseStart_1861196 baseEnd_1861196 := by
    simpa [prefixWord, tailWord_1861196, baseEnd_1861196] using wordTrace_append hprefix tailTrace_1861196
  have hstable : (prefixWord ++ tailWord_1861196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861196).length < 2 ^ (prefixWord ++ tailWord_1861196).sum := by decide
  have hdescent : baseEnd_1861196 < baseStart_1861196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861226 : List Nat := [3, 1, 3, 2, 1, 4, 2, 6]
def baseStart_1861226 : Nat := 118140960795 + 1861226 * 2 ^ 59
def prefixEnd_1861226 : Nat := 4983230072969 + 3 ^ 40 * 1861226 * 2
def baseEnd_1861226 : Nat := 70792855158906679882621

theorem tailTrace_1861226 : CollatzResearch.WordTrace tailWord_1861226 prefixEnd_1861226 70792855158906679882621 := by
  unfold tailWord_1861226
  simp only [CollatzResearch.WordTrace]
  refine ⟨16971122288775887234704883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45256326103402365959213021 16971122288775887234704883)
  ·
    refine ⟨25456683433163830852057325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16971122288775887234704883 25456683433163830852057325)
    ·
      refine ⟨9546256287436436569521497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25456683433163830852057325 9546256287436436569521497)
      ·
        refine ⟨7159692215577327427141123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9546256287436436569521497 7159692215577327427141123)
        ·
          refine ⟨10739538323365991140711685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7159692215577327427141123 10739538323365991140711685)
          ·
            refine ⟨2013663435631123338883441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10739538323365991140711685 2013663435631123338883441)
            ·
              refine ⟨1510247576723342504162581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2013663435631123338883441 1510247576723342504162581)
              ·
                refine ⟨70792855158906679882621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1510247576723342504162581 70792855158906679882621)
                ·
                  rfl

theorem cell22_1861226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 6].length) (baseStart_1861226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1861226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1861226 prefixEnd_1861226 := by exact prefixLift 1861226
  have htrace : WordTrace (prefixWord ++ tailWord_1861226) baseStart_1861226 baseEnd_1861226 := by
    simpa [prefixWord, tailWord_1861226, baseEnd_1861226] using wordTrace_append hprefix tailTrace_1861226
  have hstable : (prefixWord ++ tailWord_1861226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861226).length < 2 ^ (prefixWord ++ tailWord_1861226).sum := by decide
  have hdescent : baseEnd_1861226 < baseStart_1861226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861258 : List Nat := [3, 1, 2, 3, 2, 3, 1, 1, 3, 3]
def baseStart_1861258 : Nat := 118140960795 + 1861258 * 2 ^ 59
def prefixEnd_1861258 : Nat := 4983230072969 + 3 ^ 40 * 1861258 * 2
def baseEnd_1861258 : Nat := 637146650684122702143491

theorem tailTrace_1861258 : CollatzResearch.WordTrace tailWord_1861258 prefixEnd_1861258 637146650684122702143491 := by
  unfold tailWord_1861258
  simp only [CollatzResearch.WordTrace]
  refine ⟨16971414072746904600996107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45257104193991745602656285 16971414072746904600996107)
  ·
    refine ⟨25457121109120356901494161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16971414072746904600996107 25457121109120356901494161)
    ·
      refine ⟨19092840831840267676120621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25457121109120356901494161 19092840831840267676120621)
      ·
        refine ⟨7159815311940100378545233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19092840831840267676120621 7159815311940100378545233)
        ·
          refine ⟨5369861483955075283908925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7159815311940100378545233 5369861483955075283908925)
          ·
            refine ⟨2013698056483153231465847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5369861483955075283908925 2013698056483153231465847)
            ·
              refine ⟨3020547084724729847198771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2013698056483153231465847 3020547084724729847198771)
              ·
                refine ⟨4530820627087094770798157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3020547084724729847198771 4530820627087094770798157)
                ·
                  refine ⟨1699057735157660539049309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4530820627087094770798157 1699057735157660539049309)
                  ·
                    refine ⟨637146650684122702143491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1699057735157660539049309 637146650684122702143491)
                    ·
                      rfl

theorem cell22_1861258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_1861258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1861258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1861258 prefixEnd_1861258 := by exact prefixLift 1861258
  have htrace : WordTrace (prefixWord ++ tailWord_1861258) baseStart_1861258 baseEnd_1861258 := by
    simpa [prefixWord, tailWord_1861258, baseEnd_1861258] using wordTrace_append hprefix tailTrace_1861258
  have hstable : (prefixWord ++ tailWord_1861258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861258).length < 2 ^ (prefixWord ++ tailWord_1861258).sum := by decide
  have hdescent : baseEnd_1861258 < baseStart_1861258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861271 : List Nat := [1, 1, 3, 3, 2, 2, 4, 1, 5]
def baseStart_1861271 : Nat := 118140960795 + 1861271 * 2 ^ 59
def prefixEnd_1861271 : Nat := 4983230072969 + 3 ^ 40 * 1861271 * 2
def baseEnd_1861271 : Nat := 212383700283265000522817

theorem tailTrace_1861271 : CollatzResearch.WordTrace tailWord_1861271 prefixEnd_1861271 212383700283265000522817 := by
  unfold tailWord_1861271
  simp only [CollatzResearch.WordTrace]
  refine ⟨67886130439940521624207667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45257420293293681082805111 67886130439940521624207667)
  ·
    refine ⟨101829195659910782436311501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67886130439940521624207667 101829195659910782436311501)
    ·
      refine ⟨38185948372466543413616813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101829195659910782436311501 38185948372466543413616813)
      ·
        refine ⟨14319730639674953780106305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38185948372466543413616813 14319730639674953780106305)
        ·
          refine ⟨10739797979756215335079729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14319730639674953780106305 10739797979756215335079729)
          ·
            refine ⟨8054848484817161501309797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10739797979756215335079729 8054848484817161501309797)
            ·
              refine ⟨1510284090903217781495587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8054848484817161501309797 1510284090903217781495587)
              ·
                refine ⟨2265426136354826672243381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1510284090903217781495587 2265426136354826672243381)
                ·
                  refine ⟨212383700283265000522817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2265426136354826672243381 212383700283265000522817)
                  ·
                    rfl

theorem cell22_1861271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 5].length) (baseStart_1861271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1861271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1861271 prefixEnd_1861271 := by exact prefixLift 1861271
  have htrace : WordTrace (prefixWord ++ tailWord_1861271) baseStart_1861271 baseEnd_1861271 := by
    simpa [prefixWord, tailWord_1861271, baseEnd_1861271] using wordTrace_append hprefix tailTrace_1861271
  have hstable : (prefixWord ++ tailWord_1861271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861271).length < 2 ^ (prefixWord ++ tailWord_1861271).sum := by decide
  have hdescent : baseEnd_1861271 < baseStart_1861271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861427 : List Nat := [1, 1, 1, 2, 7, 1, 3, 2, 1, 3]
def baseStart_1861427 : Nat := 118140960795 + 1861427 * 2 ^ 59
def prefixEnd_1861427 : Nat := 4983230072969 + 3 ^ 40 * 1861427 * 2
def baseEnd_1861427 : Nat := 637204502837862594667973

theorem tailTrace_1861427 : CollatzResearch.WordTrace tailWord_1861427 prefixEnd_1861427 637204502837862594667973 := by
  unfold tailWord_1861427
  simp only [CollatzResearch.WordTrace]
  refine ⟨67891820227375360266886535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45261213484916906844591023 67891820227375360266886535)
  ·
    refine ⟨101837730341063040400329803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67891820227375360266886535 101837730341063040400329803)
    ·
      refine ⟨152756595511594560600494705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101837730341063040400329803 152756595511594560600494705)
      ·
        refine ⟨114567446633695920450371029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152756595511594560600494705 114567446633695920450371029)
        ·
          refine ⟨2685174530477248135555571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 114567446633695920450371029 2685174530477248135555571)
          ·
            refine ⟨4027761795715872203333357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2685174530477248135555571 4027761795715872203333357)
            ·
              refine ⟨1510410673393452076250009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4027761795715872203333357 1510410673393452076250009)
              ·
                refine ⟨1132808005045089057187507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1510410673393452076250009 1132808005045089057187507)
                ·
                  refine ⟨1699212007567633585781261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1132808005045089057187507 1699212007567633585781261)
                  ·
                    refine ⟨637204502837862594667973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1699212007567633585781261 637204502837862594667973)
                    ·
                      rfl

theorem cell22_1861427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 2, 1, 3].length) (baseStart_1861427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1861427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1861427 prefixEnd_1861427 := by exact prefixLift 1861427
  have htrace : WordTrace (prefixWord ++ tailWord_1861427) baseStart_1861427 baseEnd_1861427 := by
    simpa [prefixWord, tailWord_1861427, baseEnd_1861427] using wordTrace_append hprefix tailTrace_1861427
  have hstable : (prefixWord ++ tailWord_1861427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861427).length < 2 ^ (prefixWord ++ tailWord_1861427).sum := by decide
  have hdescent : baseEnd_1861427 < baseStart_1861427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861466 : List Nat := [3, 1, 1, 2, 1, 3, 3, 2, 1, 5]
def baseStart_1861466 : Nat := 118140960795 + 1861466 * 2 ^ 59
def prefixEnd_1861466 : Nat := 4983230072969 + 3 ^ 40 * 1861466 * 2
def baseEnd_1861466 : Nat := 637217853334879492942853

theorem tailTrace_1861466 : CollatzResearch.WordTrace tailWord_1861466 prefixEnd_1861466 637217853334879492942853 := by
  unfold tailWord_1861466
  simp only [CollatzResearch.WordTrace]
  refine ⟨16973310668558517481889063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45262161782822713285037501 16973310668558517481889063)
  ·
    refine ⟨25459966002837776222833595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16973310668558517481889063 25459966002837776222833595)
    ·
      refine ⟨38189949004256664334250393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25459966002837776222833595 38189949004256664334250393)
      ·
        refine ⟨28642461753192498250687795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38189949004256664334250393 28642461753192498250687795)
        ·
          refine ⟨42963692629788747376031693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28642461753192498250687795 42963692629788747376031693)
          ·
            refine ⟨16111384736170780266011885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42963692629788747376031693 16111384736170780266011885)
            ·
              refine ⟨6041769276064042599754457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16111384736170780266011885 6041769276064042599754457)
              ·
                refine ⟨4531326957048031949815843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6041769276064042599754457 4531326957048031949815843)
                ·
                  refine ⟨6796990435572047924723765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4531326957048031949815843 6796990435572047924723765)
                  ·
                    refine ⟨637217853334879492942853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6796990435572047924723765 637217853334879492942853)
                    ·
                      rfl

theorem cell22_1861466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_1861466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1861466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1861466 prefixEnd_1861466 := by exact prefixLift 1861466
  have htrace : WordTrace (prefixWord ++ tailWord_1861466) baseStart_1861466 baseEnd_1861466 := by
    simpa [prefixWord, tailWord_1861466, baseEnd_1861466] using wordTrace_append hprefix tailTrace_1861466
  have hstable : (prefixWord ++ tailWord_1861466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861466).length < 2 ^ (prefixWord ++ tailWord_1861466).sum := by decide
  have hdescent : baseEnd_1861466 < baseStart_1861466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861485 : List Nat := [1, 5, 1, 1, 1, 1, 6, 2, 4]
def baseStart_1861485 : Nat := 118140960795 + 1861485 * 2 ^ 59
def prefixEnd_1861485 : Nat := 4983230072969 + 3 ^ 40 * 1861485 * 2
def baseEnd_1861485 : Nat := 212408119141056592239265

theorem tailTrace_1861485 : CollatzResearch.WordTrace tailWord_1861485 prefixEnd_1861485 212408119141056592239265 := by
  unfold tailWord_1861485
  simp only [CollatzResearch.WordTrace]
  refine ⟨67893935661165236172497909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45262623774110157448331939 67893935661165236172497909)
  ·
    refine ⟨6365056468234240891171679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67893935661165236172497909 6365056468234240891171679)
    ·
      refine ⟨9547584702351361336757519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6365056468234240891171679 9547584702351361336757519)
      ·
        refine ⟨14321377053527042005136279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9547584702351361336757519 14321377053527042005136279)
        ·
          refine ⟨21482065580290563007704419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14321377053527042005136279 21482065580290563007704419)
          ·
            refine ⟨32223098370435844511556629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21482065580290563007704419 32223098370435844511556629)
            ·
              refine ⟨1510457736114180211479217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32223098370435844511556629 1510457736114180211479217)
              ·
                refine ⟨1132843302085635158609413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1510457736114180211479217 1132843302085635158609413)
                ·
                  refine ⟨212408119141056592239265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1132843302085635158609413 212408119141056592239265)
                  ·
                    rfl

theorem cell22_1861485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_1861485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1861485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1861485 prefixEnd_1861485 := by exact prefixLift 1861485
  have htrace : WordTrace (prefixWord ++ tailWord_1861485) baseStart_1861485 baseEnd_1861485 := by
    simpa [prefixWord, tailWord_1861485, baseEnd_1861485] using wordTrace_append hprefix tailTrace_1861485
  have hstable : (prefixWord ++ tailWord_1861485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861485).length < 2 ^ (prefixWord ++ tailWord_1861485).sum := by decide
  have hdescent : baseEnd_1861485 < baseStart_1861485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861596 : List Nat := [2, 2, 6, 1, 1, 2, 1, 1, 3, 3]
def baseStart_1861596 : Nat := 118140960795 + 1861596 * 2 ^ 59
def prefixEnd_1861596 : Nat := 4983230072969 + 3 ^ 40 * 1861596 * 2
def baseEnd_1861596 : Nat := 637262354991602487192455

theorem tailTrace_1861596 : CollatzResearch.WordTrace tailWord_1861596 prefixEnd_1861596 637262354991602487192455 := by
  unfold tailWord_1861596
  simp only [CollatzResearch.WordTrace]
  refine ⟨33948992081881551064894321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45265322775842068086525761 33948992081881551064894321)
  ·
    refine ⟨25461744061411163298670741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33948992081881551064894321 25461744061411163298670741)
    ·
      refine ⟨1193519252878648279625191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25461744061411163298670741 1193519252878648279625191)
      ·
        refine ⟨1790278879317972419437787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1193519252878648279625191 1790278879317972419437787)
        ·
          refine ⟨2685418318976958629156681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1790278879317972419437787 2685418318976958629156681)
          ·
            refine ⟨2014063739232718971867511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2685418318976958629156681 2014063739232718971867511)
            ·
              refine ⟨3021095608849078457801267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2014063739232718971867511 3021095608849078457801267)
              ·
                refine ⟨4531643413273617686701901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3021095608849078457801267 4531643413273617686701901)
                ·
                  refine ⟨1699366279977606632513213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4531643413273617686701901 1699366279977606632513213)
                  ·
                    refine ⟨637262354991602487192455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1699366279977606632513213 637262354991602487192455)
                    ·
                      rfl

theorem cell22_1861596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_1861596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1861596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1861596 prefixEnd_1861596 := by exact prefixLift 1861596
  have htrace : WordTrace (prefixWord ++ tailWord_1861596) baseStart_1861596 baseEnd_1861596 := by
    simpa [prefixWord, tailWord_1861596, baseEnd_1861596] using wordTrace_append hprefix tailTrace_1861596
  have hstable : (prefixWord ++ tailWord_1861596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861596).length < 2 ^ (prefixWord ++ tailWord_1861596).sum := by decide
  have hdescent : baseEnd_1861596 < baseStart_1861596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861603 : List Nat := [1, 1, 1, 6, 1, 2, 3, 1, 6]
def baseStart_1861603 : Nat := 118140960795 + 1861603 * 2 ^ 59
def prefixEnd_1861603 : Nat := 4983230072969 + 3 ^ 40 * 1861603 * 2
def baseEnd_1861603 : Nat := 212421583744885600755811

theorem tailTrace_1861603 : CollatzResearch.WordTrace tailWord_1861603 prefixEnd_1861603 212421583744885600755811 := by
  unfold tailWord_1861603
  simp only [CollatzResearch.WordTrace]
  refine ⟨67898239474737742325293463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45265492983158494883528975 67898239474737742325293463)
  ·
    refine ⟨101847359212106613487940195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67898239474737742325293463 101847359212106613487940195)
    ·
      refine ⟨152771038818159920231910293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101847359212106613487940195 152771038818159920231910293)
      ·
        refine ⟨7161142444601246260870795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 152771038818159920231910293 7161142444601246260870795)
        ·
          refine ⟨10741713666901869391306193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7161142444601246260870795 10741713666901869391306193)
          ·
            refine ⟨8056285250176402043479645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10741713666901869391306193 8056285250176402043479645)
            ·
              refine ⟨3021106968816150766304867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8056285250176402043479645 3021106968816150766304867)
              ·
                refine ⟨4531660453224226149457301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3021106968816150766304867 4531660453224226149457301)
                ·
                  refine ⟨212421583744885600755811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4531660453224226149457301 212421583744885600755811)
                  ·
                    rfl

theorem cell22_1861603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 6].length) (baseStart_1861603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1861603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1861603 prefixEnd_1861603 := by exact prefixLift 1861603
  have htrace : WordTrace (prefixWord ++ tailWord_1861603) baseStart_1861603 baseEnd_1861603 := by
    simpa [prefixWord, tailWord_1861603, baseEnd_1861603] using wordTrace_append hprefix tailTrace_1861603
  have hstable : (prefixWord ++ tailWord_1861603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861603).length < 2 ^ (prefixWord ++ tailWord_1861603).sum := by decide
  have hdescent : baseEnd_1861603 < baseStart_1861603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861616 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 3, 6]
def baseStart_1861616 : Nat := 118140960795 + 1861616 * 2 ^ 59
def prefixEnd_1861616 : Nat := 4983230072969 + 3 ^ 40 * 1861616 * 2
def baseEnd_1861616 : Nat := 637269201400329101692393

theorem tailTrace_1861616 : CollatzResearch.WordTrace tailWord_1861616 prefixEnd_1861616 637269201400329101692393 := by
  unfold tailWord_1861616
  simp only [CollatzResearch.WordTrace]
  refine ⟨33949356811845322772758351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45265809082460430363677801 33949356811845322772758351)
  ·
    refine ⟨50924035217767984159137527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33949356811845322772758351 50924035217767984159137527)
    ·
      refine ⟨76386052826651976238706291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50924035217767984159137527 76386052826651976238706291)
      ·
        refine ⟨114579079239977964358059437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76386052826651976238706291 114579079239977964358059437)
        ·
          refine ⟨42967154714991736634272289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114579079239977964358059437 42967154714991736634272289)
          ·
            refine ⟨32225366036243802475704217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42967154714991736634272289 32225366036243802475704217)
            ·
              refine ⟨24169024527182851856778163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32225366036243802475704217 24169024527182851856778163)
              ·
                refine ⟨36253536790774277785167245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24169024527182851856778163 36253536790774277785167245)
                ·
                  refine ⟨13595076296540354169437717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36253536790774277785167245 13595076296540354169437717)
                  ·
                    refine ⟨637269201400329101692393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13595076296540354169437717 637269201400329101692393)
                    ·
                      rfl

theorem cell22_1861616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 3, 6].length) (baseStart_1861616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1861616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1861616 prefixEnd_1861616 := by exact prefixLift 1861616
  have htrace : WordTrace (prefixWord ++ tailWord_1861616) baseStart_1861616 baseEnd_1861616 := by
    simpa [prefixWord, tailWord_1861616, baseEnd_1861616] using wordTrace_append hprefix tailTrace_1861616
  have hstable : (prefixWord ++ tailWord_1861616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861616).length < 2 ^ (prefixWord ++ tailWord_1861616).sum := by decide
  have hdescent : baseEnd_1861616 < baseStart_1861616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861665 : List Nat := [1, 2, 3, 2, 4, 2, 1, 7]
def baseStart_1861665 : Nat := 118140960795 + 1861665 * 2 ^ 59
def prefixEnd_1861665 : Nat := 4983230072969 + 3 ^ 40 * 1861665 * 2
def baseEnd_1861665 : Nat := 70809552789078811913027

theorem tailTrace_1861665 : CollatzResearch.WordTrace tailWord_1861665 prefixEnd_1861665 70809552789078811913027 := by
  unfold tailWord_1861665
  simp only [CollatzResearch.WordTrace]
  refine ⟨67900500800513126914050449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45267000533675417942700299 67900500800513126914050449)
  ·
    refine ⟨50925375600384845185537837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67900500800513126914050449 50925375600384845185537837)
    ·
      refine ⟨19097015850144316944576689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50925375600384845185537837 19097015850144316944576689)
      ·
        refine ⟨14322761887608237708432517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19097015850144316944576689 14322761887608237708432517)
        ·
          refine ⟨2685517853926544570331097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14322761887608237708432517 2685517853926544570331097)
          ·
            refine ⟨2014138390444908427748323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2685517853926544570331097 2014138390444908427748323)
            ·
              refine ⟨3021207585667362641622485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2014138390444908427748323 3021207585667362641622485)
              ·
                refine ⟨70809552789078811913027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3021207585667362641622485 70809552789078811913027)
                ·
                  rfl

theorem cell22_1861665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 7].length) (baseStart_1861665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1861665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1861665 prefixEnd_1861665 := by exact prefixLift 1861665
  have htrace : WordTrace (prefixWord ++ tailWord_1861665) baseStart_1861665 baseEnd_1861665 := by
    simpa [prefixWord, tailWord_1861665, baseEnd_1861665] using wordTrace_append hprefix tailTrace_1861665
  have hstable : (prefixWord ++ tailWord_1861665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861665).length < 2 ^ (prefixWord ++ tailWord_1861665).sum := by decide
  have hdescent : baseEnd_1861665 < baseStart_1861665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861680 : List Nat := [2, 1, 1, 1, 2, 6, 1, 2, 3, 3]
def baseStart_1861680 : Nat := 118140960795 + 1861680 * 2 ^ 59
def prefixEnd_1861680 : Nat := 4983230072969 + 3 ^ 40 * 1861680 * 2
def baseEnd_1861680 : Nat := 637291109908254268092197

theorem tailTrace_1861680 : CollatzResearch.WordTrace tailWord_1861680 prefixEnd_1861680 637291109908254268092197 := by
  unfold tailWord_1861680
  simp only [CollatzResearch.WordTrace]
  refine ⟨33950523947729392237923247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45267365263639189650564329 33950523947729392237923247)
  ·
    refine ⟨50925785921594088356884871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33950523947729392237923247 50925785921594088356884871)
    ·
      refine ⟨76388678882391132535327307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50925785921594088356884871 76388678882391132535327307)
      ·
        refine ⟨114583018323586698802990961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76388678882391132535327307 114583018323586698802990961)
        ·
          refine ⟨85937263742690024102243221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114583018323586698802990961 85937263742690024102243221)
          ·
            refine ⟨4028309237938594879792651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 85937263742690024102243221 4028309237938594879792651)
            ·
              refine ⟨6042463856907892319688977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4028309237938594879792651 6042463856907892319688977)
              ·
                refine ⟨4531847892680919239766733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6042463856907892319688977 4531847892680919239766733)
                ·
                  refine ⟨1699442959755344714912525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4531847892680919239766733 1699442959755344714912525)
                  ·
                    refine ⟨637291109908254268092197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1699442959755344714912525 637291109908254268092197)
                    ·
                      rfl

theorem cell22_1861680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 3, 3].length) (baseStart_1861680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1861680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1861680 prefixEnd_1861680 := by exact prefixLift 1861680
  have htrace : WordTrace (prefixWord ++ tailWord_1861680) baseStart_1861680 baseEnd_1861680 := by
    simpa [prefixWord, tailWord_1861680, baseEnd_1861680] using wordTrace_append hprefix tailTrace_1861680
  have hstable : (prefixWord ++ tailWord_1861680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861680).length < 2 ^ (prefixWord ++ tailWord_1861680).sum := by decide
  have hdescent : baseEnd_1861680 < baseStart_1861680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861684 : List Nat := [2, 5, 1, 2, 2, 2, 1, 1, 2, 4]
def baseStart_1861684 : Nat := 118140960795 + 1861684 * 2 ^ 59
def prefixEnd_1861684 : Nat := 4983230072969 + 3 ^ 40 * 1861684 * 2
def baseEnd_1861684 : Nat := 637292479189999590992185

theorem tailTrace_1861684 : CollatzResearch.WordTrace tailWord_1861684 prefixEnd_1861684 637292479189999590992185 := by
  unfold tailWord_1861684
  simp only [CollatzResearch.WordTrace]
  refine ⟨33950596893722146579496053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45267462524962862105994737 33950596893722146579496053)
  ·
    refine ⟨3182868458786451241827755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33950596893722146579496053 3182868458786451241827755)
    ·
      refine ⟨4774302688179676862741633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3182868458786451241827755 4774302688179676862741633)
      ·
        refine ⟨3580727016134757647056225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4774302688179676862741633 3580727016134757647056225)
        ·
          refine ⟨2685545262101068235292169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3580727016134757647056225 2685545262101068235292169)
          ·
            refine ⟨2014158946575801176469127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2685545262101068235292169 2014158946575801176469127)
            ·
              refine ⟨3021238419863701764703691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2014158946575801176469127 3021238419863701764703691)
              ·
                refine ⟨4531857629795552647055537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3021238419863701764703691 4531857629795552647055537)
                ·
                  refine ⟨3398893222346664485291653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4531857629795552647055537 3398893222346664485291653)
                  ·
                    refine ⟨637292479189999590992185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3398893222346664485291653 637292479189999590992185)
                    ·
                      rfl

theorem cell22_1861684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_1861684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1861684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1861684 prefixEnd_1861684 := by exact prefixLift 1861684
  have htrace : WordTrace (prefixWord ++ tailWord_1861684) baseStart_1861684 baseEnd_1861684 := by
    simpa [prefixWord, tailWord_1861684, baseEnd_1861684] using wordTrace_append hprefix tailTrace_1861684
  have hstable : (prefixWord ++ tailWord_1861684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861684).length < 2 ^ (prefixWord ++ tailWord_1861684).sum := by decide
  have hdescent : baseEnd_1861684 < baseStart_1861684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861693 : List Nat := [1, 4, 1, 3, 1, 1, 2, 2, 7]
def baseStart_1861693 : Nat := 118140960795 + 1861693 * 2 ^ 59
def prefixEnd_1861693 : Nat := 4983230072969 + 3 ^ 40 * 1861693 * 2
def baseEnd_1861693 : Nat := 212431853357975522505719

theorem tailTrace_1861693 : CollatzResearch.WordTrace tailWord_1861693 prefixEnd_1861693 212431853357975522505719 := by
  unfold tailWord_1861693
  simp only [CollatzResearch.WordTrace]
  refine ⟨67901522044411687696069733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45267681362941125130713155 67901522044411687696069733)
  ·
    refine ⟨12731535383327191443013075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67901522044411687696069733 12731535383327191443013075)
    ·
      refine ⟨19097303074990787164519613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12731535383327191443013075 19097303074990787164519613)
      ·
        refine ⟨7161488653121545186694855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19097303074990787164519613 7161488653121545186694855)
        ·
          refine ⟨10742232979682317780042283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7161488653121545186694855 10742232979682317780042283)
          ·
            refine ⟨16113349469523476670063425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10742232979682317780042283 16113349469523476670063425)
            ·
              refine ⟨12085012102142607502547569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16113349469523476670063425 12085012102142607502547569)
              ·
                refine ⟨9063759076606955626910677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12085012102142607502547569 9063759076606955626910677)
                ·
                  refine ⟨212431853357975522505719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9063759076606955626910677 212431853357975522505719)
                  ·
                    rfl

theorem cell22_1861693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_1861693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1861693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1861693 prefixEnd_1861693 := by exact prefixLift 1861693
  have htrace : WordTrace (prefixWord ++ tailWord_1861693) baseStart_1861693 baseEnd_1861693 := by
    simpa [prefixWord, tailWord_1861693, baseEnd_1861693] using wordTrace_append hprefix tailTrace_1861693
  have hstable : (prefixWord ++ tailWord_1861693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861693).length < 2 ^ (prefixWord ++ tailWord_1861693).sum := by decide
  have hdescent : baseEnd_1861693 < baseStart_1861693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861708 : List Nat := [2, 2, 1, 3, 1, 1, 3, 2, 2, 5]
def baseStart_1861708 : Nat := 118140960795 + 1861708 * 2 ^ 59
def prefixEnd_1861708 : Nat := 4983230072969 + 3 ^ 40 * 1861708 * 2
def baseEnd_1861708 : Nat := 637300694880471528392111

theorem tailTrace_1861708 : CollatzResearch.WordTrace tailWord_1861708 prefixEnd_1861708 637300694880471528392111 := by
  unfold tailWord_1861708
  simp only [CollatzResearch.WordTrace]
  refine ⟨33951034569678672628932889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45268046092904896838577185 33951034569678672628932889)
  ·
    refine ⟨25463275927259004471699667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33951034569678672628932889 25463275927259004471699667)
    ·
      refine ⟨38194913890888506707549501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25463275927259004471699667 38194913890888506707549501)
      ·
        refine ⟨14323092709083190015331063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38194913890888506707549501 14323092709083190015331063)
        ·
          refine ⟨21484639063624785022996595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14323092709083190015331063 21484639063624785022996595)
          ·
            refine ⟨32226958595437177534494893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21484639063624785022996595 32226958595437177534494893)
            ·
              refine ⟨12085109473288941575435585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32226958595437177534494893 12085109473288941575435585)
              ·
                refine ⟨9063832104966706181576689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12085109473288941575435585 9063832104966706181576689)
                ·
                  refine ⟨6797874078725029636182517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9063832104966706181576689 6797874078725029636182517)
                  ·
                    refine ⟨637300694880471528392111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6797874078725029636182517 637300694880471528392111)
                    ·
                      rfl

theorem cell22_1861708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_1861708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1861708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1861708 prefixEnd_1861708 := by exact prefixLift 1861708
  have htrace : WordTrace (prefixWord ++ tailWord_1861708) baseStart_1861708 baseEnd_1861708 := by
    simpa [prefixWord, tailWord_1861708, baseEnd_1861708] using wordTrace_append hprefix tailTrace_1861708
  have hstable : (prefixWord ++ tailWord_1861708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861708).length < 2 ^ (prefixWord ++ tailWord_1861708).sum := by decide
  have hdescent : baseEnd_1861708 < baseStart_1861708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861710 : List Nat := [4, 1, 1, 1, 1, 4, 3, 2, 5]
def baseStart_1861710 : Nat := 118140960795 + 1861710 * 2 ^ 59
def prefixEnd_1861710 : Nat := 4983230072969 + 3 ^ 40 * 1861710 * 2
def baseEnd_1861710 : Nat := 212433793173781396614035

theorem tailTrace_1861710 : CollatzResearch.WordTrace tailWord_1861710 prefixEnd_1861710 212433793173781396614035 := by
  unfold tailWord_1861710
  simp only [CollatzResearch.WordTrace]
  refine ⟨8487767760668762449929823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45268094723566733066292389 8487767760668762449929823)
  ·
    refine ⟨12731651641003143674894735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8487767760668762449929823 12731651641003143674894735)
    ·
      refine ⟨19097477461504715512342103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12731651641003143674894735 19097477461504715512342103)
      ·
        refine ⟨28646216192257073268513155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19097477461504715512342103 28646216192257073268513155)
        ·
          refine ⟨42969324288385609902769733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28646216192257073268513155 42969324288385609902769733)
          ·
            refine ⟨8056748304072301856769325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42969324288385609902769733 8056748304072301856769325)
            ·
              refine ⟨3021280614027113196288497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8056748304072301856769325 3021280614027113196288497)
              ·
                refine ⟨2265960460520334897216373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3021280614027113196288497 2265960460520334897216373)
                ·
                  refine ⟨212433793173781396614035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2265960460520334897216373 212433793173781396614035)
                  ·
                    rfl

theorem cell22_1861710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_1861710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1861710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1861710 prefixEnd_1861710 := by exact prefixLift 1861710
  have htrace : WordTrace (prefixWord ++ tailWord_1861710) baseStart_1861710 baseEnd_1861710 := by
    simpa [prefixWord, tailWord_1861710, baseEnd_1861710] using wordTrace_append hprefix tailTrace_1861710
  have hstable : (prefixWord ++ tailWord_1861710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861710).length < 2 ^ (prefixWord ++ tailWord_1861710).sum := by decide
  have hdescent : baseEnd_1861710 < baseStart_1861710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861740 : List Nat := [2, 2, 1, 1, 3, 3, 1, 4, 1, 4]
def baseStart_1861740 : Nat := 118140960795 + 1861740 * 2 ^ 59
def prefixEnd_1861740 : Nat := 4983230072969 + 3 ^ 40 * 1861740 * 2
def baseEnd_1861740 : Nat := 637311649134434111592013

theorem tailTrace_1861740 : CollatzResearch.WordTrace tailWord_1861740 prefixEnd_1861740 637311649134434111592013 := by
  unfold tailWord_1861740
  simp only [CollatzResearch.WordTrace]
  refine ⟨33951618137620707361515337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45268824183494276482020449 33951618137620707361515337)
  ·
    refine ⟨25463713603215530521136503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33951618137620707361515337 25463713603215530521136503)
    ·
      refine ⟨38195570404823295781704755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25463713603215530521136503 38195570404823295781704755)
      ·
        refine ⟨57293355607234943672557133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38195570404823295781704755 57293355607234943672557133)
        ·
          refine ⟨21485008352713103877208925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57293355607234943672557133 21485008352713103877208925)
          ·
            refine ⟨8056878132267413953953347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21485008352713103877208925 8056878132267413953953347)
            ·
              refine ⟨12085317198401120930930021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8056878132267413953953347 12085317198401120930930021)
              ·
                refine ⟨2265996974700210174549379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12085317198401120930930021 2265996974700210174549379)
                ·
                  refine ⟨3398995462050315261824069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2265996974700210174549379 3398995462050315261824069)
                  ·
                    refine ⟨637311649134434111592013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3398995462050315261824069 637311649134434111592013)
                    ·
                      rfl

theorem cell22_1861740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 4].length) (baseStart_1861740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1861740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1861740 prefixEnd_1861740 := by exact prefixLift 1861740
  have htrace : WordTrace (prefixWord ++ tailWord_1861740) baseStart_1861740 baseEnd_1861740 := by
    simpa [prefixWord, tailWord_1861740, baseEnd_1861740] using wordTrace_append hprefix tailTrace_1861740
  have hstable : (prefixWord ++ tailWord_1861740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861740).length < 2 ^ (prefixWord ++ tailWord_1861740).sum := by decide
  have hdescent : baseEnd_1861740 < baseStart_1861740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861924 : List Nat := [2, 3, 1, 3, 1, 2, 3, 3, 4]
def baseStart_1861924 : Nat := 118140960795 + 1861924 * 2 ^ 59
def prefixEnd_1861924 : Nat := 4983230072969 + 3 ^ 40 * 1861924 * 2
def baseEnd_1861924 : Nat := 212458212031572988330483

theorem tailTrace_1861924 : CollatzResearch.WordTrace tailWord_1861924 prefixEnd_1861924 212458212031572988330483 := by
  unfold tailWord_1861924
  simp only [CollatzResearch.WordTrace]
  refine ⟨33954973653287407073864413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45273298204383209431819217 33954973653287407073864413)
  ·
    refine ⟨12733115119982777652699155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33954973653287407073864413 12733115119982777652699155)
    ·
      refine ⟨19099672679974166479048733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12733115119982777652699155 19099672679974166479048733)
      ·
        refine ⟨7162377254990312429643275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19099672679974166479048733 7162377254990312429643275)
        ·
          refine ⟨10743565882485468644464913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7162377254990312429643275 10743565882485468644464913)
          ·
            refine ⟨8057674411864101483348685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10743565882485468644464913 8057674411864101483348685)
            ·
              refine ⟨3021627904449038056255757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8057674411864101483348685 3021627904449038056255757)
              ·
                refine ⟨1133110464168389271095909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3021627904449038056255757 1133110464168389271095909)
                ·
                  refine ⟨212458212031572988330483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1133110464168389271095909 212458212031572988330483)
                  ·
                    rfl

theorem cell22_1861924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_1861924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1861924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1861924 prefixEnd_1861924 := by exact prefixLift 1861924
  have htrace : WordTrace (prefixWord ++ tailWord_1861924) baseStart_1861924 baseEnd_1861924 := by
    simpa [prefixWord, tailWord_1861924, baseEnd_1861924] using wordTrace_append hprefix tailTrace_1861924
  have hstable : (prefixWord ++ tailWord_1861924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861924).length < 2 ^ (prefixWord ++ tailWord_1861924).sum := by decide
  have hdescent : baseEnd_1861924 < baseStart_1861924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861995 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 4, 5]
def baseStart_1861995 : Nat := 118140960795 + 1861995 * 2 ^ 59
def prefixEnd_1861995 : Nat := 4983230072969 + 3 ^ 40 * 1861995 * 2
def baseEnd_1861995 : Nat := 637398940845698446466231

theorem tailTrace_1861995 : CollatzResearch.WordTrace tailWord_1861995 prefixEnd_1861995 637398940845698446466231 := by
  unfold tailWord_1861995
  simp only [CollatzResearch.WordTrace]
  refine ⟨67912536889317593273563439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45275024592878395515708959 67912536889317593273563439)
  ·
    refine ⟨101868805333976389910345159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67912536889317593273563439 101868805333976389910345159)
    ·
      refine ⟨152803208000964584865517739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101868805333976389910345159 152803208000964584865517739)
      ·
        refine ⟨229204812001446877298276609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152803208000964584865517739 229204812001446877298276609)
        ·
          refine ⟨171903609001085157973707457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229204812001446877298276609 171903609001085157973707457)
          ·
            refine ⟨128927706750813868480280593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171903609001085157973707457 128927706750813868480280593)
            ·
              refine ⟨96695780063110401360210445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128927706750813868480280593 96695780063110401360210445)
              ·
                refine ⟨36260917523666400510078917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96695780063110401360210445 36260917523666400510078917)
                ·
                  refine ⟨6798922035687450095639797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36260917523666400510078917 6798922035687450095639797)
                  ·
                    refine ⟨637398940845698446466231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6798922035687450095639797 637398940845698446466231)
                    ·
                      rfl

theorem cell22_1861995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 5].length) (baseStart_1861995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1861995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1861995 prefixEnd_1861995 := by exact prefixLift 1861995
  have htrace : WordTrace (prefixWord ++ tailWord_1861995) baseStart_1861995 baseEnd_1861995 := by
    simpa [prefixWord, tailWord_1861995, baseEnd_1861995] using wordTrace_append hprefix tailTrace_1861995
  have hstable : (prefixWord ++ tailWord_1861995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861995).length < 2 ^ (prefixWord ++ tailWord_1861995).sum := by decide
  have hdescent : baseEnd_1861995 < baseStart_1861995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862010 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 1, 10]
def baseStart_1862010 : Nat := 118140960795 + 1862010 * 2 ^ 59
def prefixEnd_1862010 : Nat := 4983230072969 + 3 ^ 40 * 1862010 * 2
def baseEnd_1862010 : Nat := 637404075652243407341185

theorem tailTrace_1862010 : CollatzResearch.WordTrace tailWord_1862010 prefixEnd_1862010 637404075652243407341185 := by
  unfold tailWord_1862010
  simp only [CollatzResearch.WordTrace]
  refine ⟨16978270996065812708839871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45275389322842167223572989 16978270996065812708839871)
  ·
    refine ⟨25467406494098719063259807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16978270996065812708839871 25467406494098719063259807)
    ·
      refine ⟨38201109741148078594889711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25467406494098719063259807 38201109741148078594889711)
      ·
        refine ⟨57301664611722117892334567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38201109741148078594889711 57301664611722117892334567)
        ·
          refine ⟨85952496917583176838501851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57301664611722117892334567 85952496917583176838501851)
          ·
            refine ⟨128928745376374765257752777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85952496917583176838501851 128928745376374765257752777)
            ·
              refine ⟨96696559032281073943314583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128928745376374765257752777 96696559032281073943314583)
              ·
                refine ⟨145044838548421610914971875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96696559032281073943314583 145044838548421610914971875)
                ·
                  refine ⟨217567257822632416372457813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145044838548421610914971875 217567257822632416372457813)
                  ·
                    refine ⟨637404075652243407341185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 217567257822632416372457813 637404075652243407341185)
                    ·
                      rfl

theorem cell22_1862010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_1862010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1862010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1862010 prefixEnd_1862010 := by exact prefixLift 1862010
  have htrace : WordTrace (prefixWord ++ tailWord_1862010) baseStart_1862010 baseEnd_1862010 := by
    simpa [prefixWord, tailWord_1862010, baseEnd_1862010] using wordTrace_append hprefix tailTrace_1862010
  have hstable : (prefixWord ++ tailWord_1862010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862010).length < 2 ^ (prefixWord ++ tailWord_1862010).sum := by decide
  have hdescent : baseEnd_1862010 < baseStart_1862010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862018 : List Nat := [3, 4, 2, 1, 2, 1, 1, 2, 3, 3]
def baseStart_1862018 : Nat := 118140960795 + 1862018 * 2 ^ 59
def prefixEnd_1862018 : Nat := 4983230072969 + 3 ^ 40 * 1862018 * 2
def baseEnd_1862018 : Nat := 637406814215734053141161

theorem tailTrace_1862018 : CollatzResearch.WordTrace tailWord_1862018 prefixEnd_1862018 637406814215734053141161 := by
  unfold tailWord_1862018
  simp only [CollatzResearch.WordTrace]
  refine ⟨16978343942058567050412677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45275583845489512134433805 16978343942058567050412677)
  ·
    refine ⟨3183439489135981321952377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16978343942058567050412677 3183439489135981321952377)
    ·
      refine ⟨2387579616851985991464283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3183439489135981321952377 2387579616851985991464283)
      ·
        refine ⟨3581369425277978987196425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2387579616851985991464283 3581369425277978987196425)
        ·
          refine ⟨2686027068958484240397319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3581369425277978987196425 2686027068958484240397319)
          ·
            refine ⟨4029040603437726360595979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2686027068958484240397319 4029040603437726360595979)
            ·
              refine ⟨6043560905156589540893969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4029040603437726360595979 6043560905156589540893969)
              ·
                refine ⟨4532670678867442155670477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6043560905156589540893969 4532670678867442155670477)
                ·
                  refine ⟨1699751504575290808376429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4532670678867442155670477 1699751504575290808376429)
                  ·
                    refine ⟨637406814215734053141161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1699751504575290808376429 637406814215734053141161)
                    ·
                      rfl

theorem cell22_1862018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_1862018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1862018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1862018 prefixEnd_1862018 := by exact prefixLift 1862018
  have htrace : WordTrace (prefixWord ++ tailWord_1862018) baseStart_1862018 baseEnd_1862018 := by
    simpa [prefixWord, tailWord_1862018, baseEnd_1862018] using wordTrace_append hprefix tailTrace_1862018
  have hstable : (prefixWord ++ tailWord_1862018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862018).length < 2 ^ (prefixWord ++ tailWord_1862018).sum := by decide
  have hdescent : baseEnd_1862018 < baseStart_1862018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862027 : List Nat := [1, 1, 1, 1, 4, 4, 2, 1, 3, 4]
def baseStart_1862027 : Nat := 118140960795 + 1862027 * 2 ^ 59
def prefixEnd_1862027 : Nat := 4983230072969 + 3 ^ 40 * 1862027 * 2
def baseEnd_1862027 : Nat := 637409895099661029666133

theorem tailTrace_1862027 : CollatzResearch.WordTrace tailWord_1862027 prefixEnd_1862027 637409895099661029666133 := by
  unfold tailWord_1862027
  simp only [CollatzResearch.WordTrace]
  refine ⟨67913704025201662738728335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45275802683467775159152223 67913704025201662738728335)
  ·
    refine ⟨101870556037802494108092503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67913704025201662738728335 101870556037802494108092503)
    ·
      refine ⟨152805834056703741162138755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101870556037802494108092503 152805834056703741162138755)
      ·
        refine ⟨229208751085055611743208133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152805834056703741162138755 229208751085055611743208133)
        ·
          refine ⟨42976640828447927201851525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229208751085055611743208133 42976640828447927201851525)
          ·
            refine ⟨8058120155333986350347161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42976640828447927201851525 8058120155333986350347161)
            ·
              refine ⟨6043590116500489762760371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8058120155333986350347161 6043590116500489762760371)
              ·
                refine ⟨9065385174750734644140557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6043590116500489762760371 9065385174750734644140557)
                ·
                  refine ⟨3399519440531525491552709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9065385174750734644140557 3399519440531525491552709)
                  ·
                    refine ⟨637409895099661029666133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3399519440531525491552709 637409895099661029666133)
                    ·
                      rfl

theorem cell22_1862027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 4].length) (baseStart_1862027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1862027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1862027 prefixEnd_1862027 := by exact prefixLift 1862027
  have htrace : WordTrace (prefixWord ++ tailWord_1862027) baseStart_1862027 baseEnd_1862027 := by
    simpa [prefixWord, tailWord_1862027, baseEnd_1862027] using wordTrace_append hprefix tailTrace_1862027
  have hstable : (prefixWord ++ tailWord_1862027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862027).length < 2 ^ (prefixWord ++ tailWord_1862027).sum := by decide
  have hdescent : baseEnd_1862027 < baseStart_1862027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862074 : List Nat := [3, 1, 1, 1, 2, 1, 1, 7, 2, 3]
def baseStart_1862074 : Nat := 118140960795 + 1862074 * 2 ^ 59
def prefixEnd_1862074 : Nat := 4983230072969 + 3 ^ 40 * 1862074 * 2
def baseEnd_1862074 : Nat := 637425984160168573740989

theorem tailTrace_1862074 : CollatzResearch.WordTrace tailWord_1862074 prefixEnd_1862074 637425984160168573740989 := by
  unfold tailWord_1862074
  simp only [CollatzResearch.WordTrace]
  refine ⟨16978854564007847441422319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45276945504020926510459517 16978854564007847441422319)
  ·
    refine ⟨25468281846011771162133479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16978854564007847441422319 25468281846011771162133479)
    ·
      refine ⟨38202422769017656743200219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25468281846011771162133479 38202422769017656743200219)
      ·
        refine ⟨57303634153526485114800329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38202422769017656743200219 57303634153526485114800329)
        ·
          refine ⟨42977725615144863836100247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57303634153526485114800329 42977725615144863836100247)
          ·
            refine ⟨64466588422717295754150371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42977725615144863836100247 64466588422717295754150371)
            ·
              refine ⟨96699882634075943631225557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64466588422717295754150371 96699882634075943631225557)
              ·
                refine ⟨2266403499236154928856849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 96699882634075943631225557 2266403499236154928856849)
                ·
                  refine ⟨1699802624427116196642637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2266403499236154928856849 1699802624427116196642637)
                  ·
                    refine ⟨637425984160168573740989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1699802624427116196642637 637425984160168573740989)
                    ·
                      rfl

theorem cell22_1862074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 2, 3].length) (baseStart_1862074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1862074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1862074 prefixEnd_1862074 := by exact prefixLift 1862074
  have htrace : WordTrace (prefixWord ++ tailWord_1862074) baseStart_1862074 baseEnd_1862074 := by
    simpa [prefixWord, tailWord_1862074, baseEnd_1862074] using wordTrace_append hprefix tailTrace_1862074
  have hstable : (prefixWord ++ tailWord_1862074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862074).length < 2 ^ (prefixWord ++ tailWord_1862074).sum := by decide
  have hdescent : baseEnd_1862074 < baseStart_1862074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862087 : List Nat := [1, 1, 4, 1, 1, 5, 1, 8]
def baseStart_1862087 : Nat := 118140960795 + 1862087 * 2 ^ 59
def prefixEnd_1862087 : Nat := 4983230072969 + 3 ^ 40 * 1862087 * 2
def baseEnd_1862087 : Nat := 70825603813982319240661

theorem tailTrace_1862087 : CollatzResearch.WordTrace tailWord_1862087 prefixEnd_1862087 70825603813982319240661 := by
  unfold tailWord_1862087
  simp only [CollatzResearch.WordTrace]
  refine ⟨67915892404984292985912515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45277261603322861990608343 67915892404984292985912515)
  ·
    refine ⟨101873838607476439478868773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67915892404984292985912515 101873838607476439478868773)
    ·
      refine ⟨19101344738901832402287895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101873838607476439478868773 19101344738901832402287895)
      ·
        refine ⟨28652017108352748603431843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19101344738901832402287895 28652017108352748603431843)
        ·
          refine ⟨42978025662529122905147765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28652017108352748603431843 42978025662529122905147765)
          ·
            refine ⟨4029189905862105272357603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42978025662529122905147765 4029189905862105272357603)
            ·
              refine ⟨6043784858793157908536405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4029189905862105272357603 6043784858793157908536405)
              ·
                refine ⟨70825603813982319240661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6043784858793157908536405 70825603813982319240661)
                ·
                  rfl

theorem cell22_1862087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 8].length) (baseStart_1862087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1862087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1862087 prefixEnd_1862087 := by exact prefixLift 1862087
  have htrace : WordTrace (prefixWord ++ tailWord_1862087) baseStart_1862087 baseEnd_1862087 := by
    simpa [prefixWord, tailWord_1862087, baseEnd_1862087] using wordTrace_append hprefix tailTrace_1862087
  have hstable : (prefixWord ++ tailWord_1862087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862087).length < 2 ^ (prefixWord ++ tailWord_1862087).sum := by decide
  have hdescent : baseEnd_1862087 < baseStart_1862087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862125 : List Nat := [1, 5, 1, 3, 1, 3, 2, 1, 2, 3]
def baseStart_1862125 : Nat := 118140960795 + 1862125 * 2 ^ 59
def prefixEnd_1862125 : Nat := 4983230072969 + 3 ^ 40 * 1862125 * 2
def baseEnd_1862125 : Nat := 637443442502421440715833

theorem tailTrace_1862125 : CollatzResearch.WordTrace tailWord_1862125 prefixEnd_1862125 637443442502421440715833 := by
  unfold tailWord_1862125
  simp only [CollatzResearch.WordTrace]
  refine ⟨67917278378846625475795829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45278185585897750317197219 67917278378846625475795829)
  ·
    refine ⟨6367244848016871138355859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67917278378846625475795829 6367244848016871138355859)
    ·
      refine ⟨9550867272025306707533789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6367244848016871138355859 9550867272025306707533789)
      ·
        refine ⟨3581575227009490015325171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9550867272025306707533789 3581575227009490015325171)
        ·
          refine ⟨5372362840514235022987757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3581575227009490015325171 5372362840514235022987757)
          ·
            refine ⟨2014636065192838133620409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5372362840514235022987757 2014636065192838133620409)
            ·
              refine ⟨1510977048894628600215307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2014636065192838133620409 1510977048894628600215307)
              ·
                refine ⟨2266465573341942900322961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1510977048894628600215307 2266465573341942900322961)
                ·
                  refine ⟨1699849180006457175242221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2266465573341942900322961 1699849180006457175242221)
                  ·
                    refine ⟨637443442502421440715833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1699849180006457175242221 637443442502421440715833)
                    ·
                      rfl

theorem cell22_1862125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_1862125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1862125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1862125 prefixEnd_1862125 := by exact prefixLift 1862125
  have htrace : WordTrace (prefixWord ++ tailWord_1862125) baseStart_1862125 baseEnd_1862125 := by
    simpa [prefixWord, tailWord_1862125, baseEnd_1862125] using wordTrace_append hprefix tailTrace_1862125
  have hstable : (prefixWord ++ tailWord_1862125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862125).length < 2 ^ (prefixWord ++ tailWord_1862125).sum := by decide
  have hdescent : baseEnd_1862125 < baseStart_1862125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862179 : List Nat := [1, 1, 1, 4, 4, 1, 1, 2, 3, 4]
def baseStart_1862179 : Nat := 118140960795 + 1862179 * 2 ^ 59
def prefixEnd_1862179 : Nat := 4983230072969 + 3 ^ 40 * 1862179 * 2
def baseEnd_1862179 : Nat := 637461927805983299865667

theorem tailTrace_1862179 : CollatzResearch.WordTrace tailWord_1862179 prefixEnd_1862179 637461927805983299865667 := by
  unfold tailWord_1862179
  simp only [CollatzResearch.WordTrace]
  refine ⟨67919247920650992698261591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45279498613767328465507727 67919247920650992698261591)
  ·
    refine ⟨101878871880976489047392387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67919247920650992698261591 101878871880976489047392387)
    ·
      refine ⟨152818307821464733571088581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101878871880976489047392387 152818307821464733571088581)
      ·
        refine ⟨28653432716524637544579109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152818307821464733571088581 28653432716524637544579109)
        ·
          refine ⟨5372518634348369539608583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28653432716524637544579109 5372518634348369539608583)
          ·
            refine ⟨8058777951522554309412875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5372518634348369539608583 8058777951522554309412875)
            ·
              refine ⟨12088166927283831464119313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8058777951522554309412875 12088166927283831464119313)
              ·
                refine ⟨9066125195462873598089485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12088166927283831464119313 9066125195462873598089485)
                ·
                  refine ⟨3399796948298577599283557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9066125195462873598089485 3399796948298577599283557)
                  ·
                    refine ⟨637461927805983299865667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3399796948298577599283557 637461927805983299865667)
                    ·
                      rfl

theorem cell22_1862179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 4].length) (baseStart_1862179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1862179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1862179 prefixEnd_1862179 := by exact prefixLift 1862179
  have htrace : WordTrace (prefixWord ++ tailWord_1862179) baseStart_1862179 baseEnd_1862179 := by
    simpa [prefixWord, tailWord_1862179, baseEnd_1862179] using wordTrace_append hprefix tailTrace_1862179
  have hstable : (prefixWord ++ tailWord_1862179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862179).length < 2 ^ (prefixWord ++ tailWord_1862179).sum := by decide
  have hdescent : baseEnd_1862179 < baseStart_1862179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862213 : List Nat := [1, 3, 1, 1, 1, 7, 2, 1, 1, 4]
def baseStart_1862213 : Nat := 118140960795 + 1862213 * 2 ^ 59
def prefixEnd_1862213 : Nat := 4983230072969 + 3 ^ 40 * 1862213 * 2
def baseEnd_1862213 : Nat := 637473566700818544515563

theorem tailTrace_1862213 : CollatzResearch.WordTrace tailWord_1862213 prefixEnd_1862213 637473566700818544515563 := by
  unfold tailWord_1862213
  simp only [CollatzResearch.WordTrace]
  refine ⟨67920488002527816504999293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45280325335018544336666195 67920488002527816504999293)
  ·
    refine ⟨25470183000947931189374735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67920488002527816504999293 25470183000947931189374735)
    ·
      refine ⟨38205274501421896784062103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25470183000947931189374735 38205274501421896784062103)
      ·
        refine ⟨57307911752132845176093155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38205274501421896784062103 57307911752132845176093155)
        ·
          refine ⟨85961867628199267764139733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57307911752132845176093155 85961867628199267764139733)
          ·
            refine ⟨2014731272535920338222025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 85961867628199267764139733 2014731272535920338222025)
            ·
              refine ⟨1511048454401940253666519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2014731272535920338222025 1511048454401940253666519)
              ·
                refine ⟨2266572681602910380499779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1511048454401940253666519 2266572681602910380499779)
                ·
                  refine ⟨3399859022404365570749669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2266572681602910380499779 3399859022404365570749669)
                  ·
                    refine ⟨637473566700818544515563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3399859022404365570749669 637473566700818544515563)
                    ·
                      rfl

theorem cell22_1862213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 1, 4].length) (baseStart_1862213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1862213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1862213 prefixEnd_1862213 := by exact prefixLift 1862213
  have htrace : WordTrace (prefixWord ++ tailWord_1862213) baseStart_1862213 baseEnd_1862213 := by
    simpa [prefixWord, tailWord_1862213, baseEnd_1862213] using wordTrace_append hprefix tailTrace_1862213
  have hstable : (prefixWord ++ tailWord_1862213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862213).length < 2 ^ (prefixWord ++ tailWord_1862213).sum := by decide
  have hdescent : baseEnd_1862213 < baseStart_1862213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862226 : List Nat := [3, 2, 2, 1, 2, 1, 3, 1, 4, 3]
def baseStart_1862226 : Nat := 118140960795 + 1862226 * 2 ^ 59
def prefixEnd_1862226 : Nat := 4983230072969 + 3 ^ 40 * 1862226 * 2
def baseEnd_1862226 : Nat := 637478016866490843940523

theorem tailTrace_1862226 : CollatzResearch.WordTrace tailWord_1862226 prefixEnd_1862226 637478016866490843940523 := by
  unfold tailWord_1862226
  simp only [CollatzResearch.WordTrace]
  refine ⟨16980240537870179931305633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45280641434320479816815021 16980240537870179931305633)
  ·
    refine ⟨12735180403402634948479225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16980240537870179931305633 12735180403402634948479225)
    ·
      refine ⟨9551385302551976211359419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12735180403402634948479225 9551385302551976211359419)
      ·
        refine ⟨14327077953827964317039129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9551385302551976211359419 14327077953827964317039129)
        ·
          refine ⟨10745308465370973237779347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14327077953827964317039129 10745308465370973237779347)
          ·
            refine ⟨16117962698056459856669021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10745308465370973237779347 16117962698056459856669021)
            ·
              refine ⟨6044236011771172446250883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16117962698056459856669021 6044236011771172446250883)
              ·
                refine ⟨9066354017656758669376325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6044236011771172446250883 9066354017656758669376325)
                ·
                  refine ⟨1699941378310642250508061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9066354017656758669376325 1699941378310642250508061)
                  ·
                    refine ⟨637478016866490843940523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1699941378310642250508061 637478016866490843940523)
                    ·
                      rfl

theorem cell22_1862226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_1862226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1862226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1862226 prefixEnd_1862226 := by exact prefixLift 1862226
  have htrace : WordTrace (prefixWord ++ tailWord_1862226) baseStart_1862226 baseEnd_1862226 := by
    simpa [prefixWord, tailWord_1862226, baseEnd_1862226] using wordTrace_append hprefix tailTrace_1862226
  have hstable : (prefixWord ++ tailWord_1862226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862226).length < 2 ^ (prefixWord ++ tailWord_1862226).sum := by decide
  have hdescent : baseEnd_1862226 < baseStart_1862226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862243 : List Nat := [1, 1, 1, 5, 1, 2, 5, 1, 2, 3]
def baseStart_1862243 : Nat := 118140960795 + 1862243 * 2 ^ 59
def prefixEnd_1862243 : Nat := 4983230072969 + 3 ^ 40 * 1862243 * 2
def baseEnd_1862243 : Nat := 637483836313908466265471

theorem tailTrace_1862243 : CollatzResearch.WordTrace tailWord_1862243 prefixEnd_1862243 637483836313908466265471 := by
  unfold tailWord_1862243
  simp only [CollatzResearch.WordTrace]
  refine ⟨67921582192419131628591383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45281054794946087752394255 67921582192419131628591383)
  ·
    refine ⟨101882373288628697442887075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67921582192419131628591383 101882373288628697442887075)
    ·
      refine ⟨152823559932943046164330613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101882373288628697442887075 152823559932943046164330613)
      ·
        refine ⟨14327208743713410577905995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152823559932943046164330613 14327208743713410577905995)
        ·
          refine ⟨21490813115570115866858993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14327208743713410577905995 21490813115570115866858993)
          ·
            refine ⟨16118109836677586900144245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21490813115570115866858993 16118109836677586900144245)
            ·
              refine ⟨1511072797188523771888523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16118109836677586900144245 1511072797188523771888523)
              ·
                refine ⟨2266609195782785657832785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1511072797188523771888523 2266609195782785657832785)
                ·
                  refine ⟨1699956896837089243374589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2266609195782785657832785 1699956896837089243374589)
                  ·
                    refine ⟨637483836313908466265471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1699956896837089243374589 637483836313908466265471)
                    ·
                      rfl

theorem cell22_1862243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 2, 3].length) (baseStart_1862243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1862243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1862243 prefixEnd_1862243 := by exact prefixLift 1862243
  have htrace : WordTrace (prefixWord ++ tailWord_1862243) baseStart_1862243 baseEnd_1862243 := by
    simpa [prefixWord, tailWord_1862243, baseEnd_1862243] using wordTrace_append hprefix tailTrace_1862243
  have hstable : (prefixWord ++ tailWord_1862243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862243).length < 2 ^ (prefixWord ++ tailWord_1862243).sum := by decide
  have hdescent : baseEnd_1862243 < baseStart_1862243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862262 : List Nat := [5, 1, 1, 2, 4, 1, 1, 3, 4]
def baseStart_1862262 : Nat := 118140960795 + 1862262 * 2 ^ 59
def prefixEnd_1862262 : Nat := 4983230072969 + 3 ^ 40 * 1862262 * 2
def baseEnd_1862262 : Nat := 212496780134066250013471

theorem tailTrace_1862262 : CollatzResearch.WordTrace tailWord_1862262 prefixEnd_1862262 212496780134066250013471 := by
  unfold tailWord_1862262
  simp only [CollatzResearch.WordTrace]
  refine ⟨4245142198709393617095815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45281516786233531915688693 4245142198709393617095815)
  ·
    refine ⟨6367713298064090425643723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4245142198709393617095815 6367713298064090425643723)
    ·
      refine ⟨9551569947096135638465585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6367713298064090425643723 9551569947096135638465585)
      ·
        refine ⟨7163677460322101728849189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9551569947096135638465585 7163677460322101728849189)
        ·
          refine ⟨1343189523810394074159223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7163677460322101728849189 1343189523810394074159223)
          ·
            refine ⟨2014784285715591111238835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1343189523810394074159223 2014784285715591111238835)
            ·
              refine ⟨3022176428573386666858253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2014784285715591111238835 3022176428573386666858253)
              ·
                refine ⟨1133316160715020000071845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3022176428573386666858253 1133316160715020000071845)
                ·
                  refine ⟨212496780134066250013471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1133316160715020000071845 212496780134066250013471)
                  ·
                    rfl

theorem cell22_1862262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_1862262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1862262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1862262 prefixEnd_1862262 := by exact prefixLift 1862262
  have htrace : WordTrace (prefixWord ++ tailWord_1862262) baseStart_1862262 baseEnd_1862262 := by
    simpa [prefixWord, tailWord_1862262, baseEnd_1862262] using wordTrace_append hprefix tailTrace_1862262
  have hstable : (prefixWord ++ tailWord_1862262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862262).length < 2 ^ (prefixWord ++ tailWord_1862262).sum := by decide
  have hdescent : baseEnd_1862262 < baseStart_1862262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862361 : List Nat := [1, 2, 1, 2, 3, 2, 4, 1, 1, 5]
def baseStart_1862361 : Nat := 118140960795 + 1862361 * 2 ^ 59
def prefixEnd_1862361 : Nat := 4983230072969 + 3 ^ 40 * 1862361 * 2
def baseEnd_1862361 : Nat := 637524230125395491815109

theorem tailTrace_1862361 : CollatzResearch.WordTrace tailWord_1862361 prefixEnd_1862361 637524230125395491815109 := by
  unfold tailWord_1862361
  simp only [CollatzResearch.WordTrace]
  refine ⟨67925886005991637781386937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45283924003994425187591291 67925886005991637781386937)
  ·
    refine ⟨50944414504493728336040203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67925886005991637781386937 50944414504493728336040203)
    ·
      refine ⟨76416621756740592504060305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50944414504493728336040203 76416621756740592504060305)
      ·
        refine ⟨57312466317555444378045229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76416621756740592504060305 57312466317555444378045229)
        ·
          refine ⟨21492174869083291641766961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57312466317555444378045229 21492174869083291641766961)
          ·
            refine ⟨16119131151812468731325221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21492174869083291641766961 16119131151812468731325221)
            ·
              refine ⟨3022337090964837887123479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16119131151812468731325221 3022337090964837887123479)
              ·
                refine ⟨4533505636447256830685219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3022337090964837887123479 4533505636447256830685219)
                ·
                  refine ⟨6800258454670885246027829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4533505636447256830685219 6800258454670885246027829)
                  ·
                    refine ⟨637524230125395491815109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6800258454670885246027829 637524230125395491815109)
                    ·
                      rfl

theorem cell22_1862361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 5].length) (baseStart_1862361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1862361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1862361 prefixEnd_1862361 := by exact prefixLift 1862361
  have htrace : WordTrace (prefixWord ++ tailWord_1862361) baseStart_1862361 baseEnd_1862361 := by
    simpa [prefixWord, tailWord_1862361, baseEnd_1862361] using wordTrace_append hprefix tailTrace_1862361
  have hstable : (prefixWord ++ tailWord_1862361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862361).length < 2 ^ (prefixWord ++ tailWord_1862361).sum := by decide
  have hdescent : baseEnd_1862361 < baseStart_1862361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862515 : List Nat := [1, 1, 1, 2, 2, 1, 8, 2, 4]
def baseStart_1862515 : Nat := 118140960795 + 1862515 * 2 ^ 59
def prefixEnd_1862515 : Nat := 4983230072969 + 3 ^ 40 * 1862515 * 2
def baseEnd_1862515 : Nat := 212525649157530141154879

theorem tailTrace_1862515 : CollatzResearch.WordTrace tailWord_1862515 prefixEnd_1862515 212525649157530141154879 := by
  unfold tailWord_1862515
  simp only [CollatzResearch.WordTrace]
  refine ⟨67931502847433722082492999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45287668564955814721661999 67931502847433722082492999)
  ·
    refine ⟨101897254271150583123739499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67931502847433722082492999 101897254271150583123739499)
    ·
      refine ⟨152845881406725874685609249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101897254271150583123739499 152845881406725874685609249)
      ·
        refine ⟨114634411055044406014206937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152845881406725874685609249 114634411055044406014206937)
        ·
          refine ⟨85975808291283304510655203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114634411055044406014206937 85975808291283304510655203)
          ·
            refine ⟨128963712436924956765982805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85975808291283304510655203 128963712436924956765982805)
            ·
              refine ⟨1511293505120214337101361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 128963712436924956765982805 1511293505120214337101361)
              ·
                refine ⟨1133470128840160752826021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1511293505120214337101361 1133470128840160752826021)
                ·
                  refine ⟨212525649157530141154879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1133470128840160752826021 212525649157530141154879)
                  ·
                    rfl

theorem cell22_1862515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 2, 4].length) (baseStart_1862515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1862515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1862515 prefixEnd_1862515 := by exact prefixLift 1862515
  have htrace : WordTrace (prefixWord ++ tailWord_1862515) baseStart_1862515 baseEnd_1862515 := by
    simpa [prefixWord, tailWord_1862515, baseEnd_1862515] using wordTrace_append hprefix tailTrace_1862515
  have hstable : (prefixWord ++ tailWord_1862515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862515).length < 2 ^ (prefixWord ++ tailWord_1862515).sum := by decide
  have hdescent : baseEnd_1862515 < baseStart_1862515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862571 : List Nat := [1, 1, 1, 1, 2, 1, 1, 7, 7]
def baseStart_1862571 : Nat := 118140960795 + 1862571 * 2 ^ 59
def prefixEnd_1862571 : Nat := 4983230072969 + 3 ^ 40 * 1862571 * 2
def baseEnd_1862571 : Nat := 212532039139008314688155

theorem tailTrace_1862571 : CollatzResearch.WordTrace tailWord_1862571 prefixEnd_1862571 212532039139008314688155 := by
  unfold tailWord_1862571
  simp only [CollatzResearch.WordTrace]
  refine ⟨67933545335230843646531567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45289030223487229097687711 67933545335230843646531567)
  ·
    refine ⟨101900318002846265469797351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67933545335230843646531567 101900318002846265469797351)
    ·
      refine ⟨152850477004269398204696027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101900318002846265469797351 152850477004269398204696027)
      ·
        refine ⟨229275715506404097307044041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152850477004269398204696027 229275715506404097307044041)
        ·
          refine ⟨171956786629803072980283031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229275715506404097307044041 171956786629803072980283031)
          ·
            refine ⟨257935179944704609470424547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171956786629803072980283031 257935179944704609470424547)
            ·
              refine ⟨386902769917056914205636821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257935179944704609470424547 386902769917056914205636821)
              ·
                refine ⟨9068033669931021426694613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 386902769917056914205636821 9068033669931021426694613)
                ·
                  refine ⟨212532039139008314688155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9068033669931021426694613 212532039139008314688155)
                  ·
                    rfl

theorem cell22_1862571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 7].length) (baseStart_1862571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1862571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1862571 prefixEnd_1862571 := by exact prefixLift 1862571
  have htrace : WordTrace (prefixWord ++ tailWord_1862571) baseStart_1862571 baseEnd_1862571 := by
    simpa [prefixWord, tailWord_1862571, baseEnd_1862571] using wordTrace_append hprefix tailTrace_1862571
  have hstable : (prefixWord ++ tailWord_1862571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862571).length < 2 ^ (prefixWord ++ tailWord_1862571).sum := by decide
  have hdescent : baseEnd_1862571 < baseStart_1862571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862648 : List Nat := [2, 1, 2, 1, 1, 3, 1, 5, 1, 5]
def baseStart_1862648 : Nat := 118140960795 + 1862648 * 2 ^ 59
def prefixEnd_1862648 : Nat := 4983230072969 + 3 ^ 40 * 1862648 * 2
def baseEnd_1862648 : Nat := 637622476090622409889229

theorem tailTrace_1862648 : CollatzResearch.WordTrace tailWord_1862648 prefixEnd_1862648 637622476090622409889229 := by
  unfold tailWord_1862648
  simp only [CollatzResearch.WordTrace]
  refine ⟨33968176877975942898542299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45290902503967923864723065 33968176877975942898542299)
  ·
    refine ⟨50952265316963914347813449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33968176877975942898542299 50952265316963914347813449)
    ·
      refine ⟨38214198987722935760860087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50952265316963914347813449 38214198987722935760860087)
      ·
        refine ⟨57321298481584403641290131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38214198987722935760860087 57321298481584403641290131)
        ·
          refine ⟨85981947722376605461935197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57321298481584403641290131 85981947722376605461935197)
          ·
            refine ⟨32243230395891227048225699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85981947722376605461935197 32243230395891227048225699)
            ·
              refine ⟨48364845593836840572338549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32243230395891227048225699 48364845593836840572338549)
              ·
                refine ⟨4534204274422203803656739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48364845593836840572338549 4534204274422203803656739)
                ·
                  refine ⟨6801306411633305705485109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4534204274422203803656739 6801306411633305705485109)
                  ·
                    refine ⟨637622476090622409889229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6801306411633305705485109 637622476090622409889229)
                    ·
                      rfl

theorem cell22_1862648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_1862648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1862648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1862648 prefixEnd_1862648 := by exact prefixLift 1862648
  have htrace : WordTrace (prefixWord ++ tailWord_1862648) baseStart_1862648 baseEnd_1862648 := by
    simpa [prefixWord, tailWord_1862648, baseEnd_1862648] using wordTrace_append hprefix tailTrace_1862648
  have hstable : (prefixWord ++ tailWord_1862648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862648).length < 2 ^ (prefixWord ++ tailWord_1862648).sum := by decide
  have hdescent : baseEnd_1862648 < baseStart_1862648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862652 : List Nat := [2, 2, 2, 1, 2, 5, 1, 2, 1, 4]
def baseStart_1862652 : Nat := 118140960795 + 1862652 * 2 ^ 59
def prefixEnd_1862652 : Nat := 4983230072969 + 3 ^ 40 * 1862652 * 2
def baseEnd_1862652 : Nat := 637623845372367732789217

theorem tailTrace_1862652 : CollatzResearch.WordTrace tailWord_1862652 prefixEnd_1862652 637623845372367732789217 := by
  unfold tailWord_1862652
  simp only [CollatzResearch.WordTrace]
  refine ⟨33968249823968697240115105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45290999765291596320153473 33968249823968697240115105)
  ·
    refine ⟨25476187367976522930086329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33968249823968697240115105 25476187367976522930086329)
    ·
      refine ⟨19107140525982392197564747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25476187367976522930086329 19107140525982392197564747)
      ·
        refine ⟨28660710788973588296347121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19107140525982392197564747 28660710788973588296347121)
        ·
          refine ⟨21495533091730191222260341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28660710788973588296347121 21495533091730191222260341)
          ·
            refine ⟨2015206227349705427086907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21495533091730191222260341 2015206227349705427086907)
            ·
              refine ⟨3022809341024558140630361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2015206227349705427086907 3022809341024558140630361)
              ·
                refine ⟨2267107005768418605472771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3022809341024558140630361 2267107005768418605472771)
                ·
                  refine ⟨3400660508652627908209157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2267107005768418605472771 3400660508652627908209157)
                  ·
                    refine ⟨637623845372367732789217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3400660508652627908209157 637623845372367732789217)
                    ·
                      rfl

theorem cell22_1862652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_1862652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1862652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1862652 prefixEnd_1862652 := by exact prefixLift 1862652
  have htrace : WordTrace (prefixWord ++ tailWord_1862652) baseStart_1862652 baseEnd_1862652 := by
    simpa [prefixWord, tailWord_1862652, baseEnd_1862652] using wordTrace_append hprefix tailTrace_1862652
  have hstable : (prefixWord ++ tailWord_1862652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862652).length < 2 ^ (prefixWord ++ tailWord_1862652).sum := by decide
  have hdescent : baseEnd_1862652 < baseStart_1862652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862680 : List Nat := [2, 1, 2, 3, 2, 2, 2, 2, 2, 4]
def baseStart_1862680 : Nat := 118140960795 + 1862680 * 2 ^ 59
def prefixEnd_1862680 : Nat := 4983230072969 + 3 ^ 40 * 1862680 * 2
def baseEnd_1862680 : Nat := 637633430344584993089131

theorem tailTrace_1862680 : CollatzResearch.WordTrace tailWord_1862680 prefixEnd_1862680 637633430344584993089131 := by
  unfold tailWord_1862680
  simp only [CollatzResearch.WordTrace]
  refine ⟨33968760445917977631124747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45291680594557303508166329 33968760445917977631124747)
  ·
    refine ⟨50953140668876966446687121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33968760445917977631124747 50953140668876966446687121)
    ·
      refine ⟨38214855501657724835015341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50953140668876966446687121 38214855501657724835015341)
      ·
        refine ⟨14330570813121646813130753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38214855501657724835015341 14330570813121646813130753)
        ·
          refine ⟨10747928109841235109848065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14330570813121646813130753 10747928109841235109848065)
          ·
            refine ⟨8060946082380926332386049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10747928109841235109848065 8060946082380926332386049)
            ·
              refine ⟨6045709561785694749289537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8060946082380926332386049 6045709561785694749289537)
              ·
                refine ⟨4534282171339271061967153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6045709561785694749289537 4534282171339271061967153)
                ·
                  refine ⟨3400711628504453296475365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4534282171339271061967153 3400711628504453296475365)
                  ·
                    refine ⟨637633430344584993089131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3400711628504453296475365 637633430344584993089131)
                    ·
                      rfl

theorem cell22_1862680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_1862680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1862680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1862680 prefixEnd_1862680 := by exact prefixLift 1862680
  have htrace : WordTrace (prefixWord ++ tailWord_1862680) baseStart_1862680 baseEnd_1862680 := by
    simpa [prefixWord, tailWord_1862680, baseEnd_1862680] using wordTrace_append hprefix tailTrace_1862680
  have hstable : (prefixWord ++ tailWord_1862680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862680).length < 2 ^ (prefixWord ++ tailWord_1862680).sum := by decide
  have hdescent : baseEnd_1862680 < baseStart_1862680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862682 : List Nat := [3, 1, 1, 3, 1, 2, 4, 2, 2, 3]
def baseStart_1862682 : Nat := 118140960795 + 1862682 * 2 ^ 59
def prefixEnd_1862682 : Nat := 4983230072969 + 3 ^ 40 * 1862682 * 2
def baseEnd_1862682 : Nat := 637634114985457654539125

theorem tailTrace_1862682 : CollatzResearch.WordTrace tailWord_1862682 prefixEnd_1862682 637634114985457654539125 := by
  unfold tailWord_1862682
  simp only [CollatzResearch.WordTrace]
  refine ⟨16984398459457177400955575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45291729225219139735881533 16984398459457177400955575)
  ·
    refine ⟨25476597689185766101433363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16984398459457177400955575 25476597689185766101433363)
    ·
      refine ⟨38214896533778649152150045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25476597689185766101433363 38214896533778649152150045)
      ·
        refine ⟨14330586200166993432056267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38214896533778649152150045 14330586200166993432056267)
        ·
          refine ⟨21495879300250490148084401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14330586200166993432056267 21495879300250490148084401)
          ·
            refine ⟨16121909475187867611063301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21495879300250490148084401 16121909475187867611063301)
            ·
              refine ⟨3022858026597725177074369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16121909475187867611063301 3022858026597725177074369)
              ·
                refine ⟨2267143519948293882805777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3022858026597725177074369 2267143519948293882805777)
                ·
                  refine ⟨1700357639961220412104333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2267143519948293882805777 1700357639961220412104333)
                  ·
                    refine ⟨637634114985457654539125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1700357639961220412104333 637634114985457654539125)
                    ·
                      rfl

theorem cell22_1862682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 2, 3].length) (baseStart_1862682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1862682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1862682 prefixEnd_1862682 := by exact prefixLift 1862682
  have htrace : WordTrace (prefixWord ++ tailWord_1862682) baseStart_1862682 baseEnd_1862682 := by
    simpa [prefixWord, tailWord_1862682, baseEnd_1862682] using wordTrace_append hprefix tailTrace_1862682
  have hstable : (prefixWord ++ tailWord_1862682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862682).length < 2 ^ (prefixWord ++ tailWord_1862682).sum := by decide
  have hdescent : baseEnd_1862682 < baseStart_1862682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862723 : List Nat := [1, 1, 1, 3, 1, 2, 4, 2, 7]
def baseStart_1862723 : Nat := 118140960795 + 1862723 * 2 ^ 59
def prefixEnd_1862723 : Nat := 4983230072969 + 3 ^ 40 * 1862723 * 2
def baseEnd_1862723 : Nat := 212549383374449071421333

theorem tailTrace_1862723 : CollatzResearch.WordTrace tailWord_1862723 prefixEnd_1862723 212549383374449071421333 := by
  unfold tailWord_1862723
  simp only [CollatzResearch.WordTrace]
  refine ⟨67939089230680173606064823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45292726153786782404043215 67939089230680173606064823)
  ·
    refine ⟨101908633846020260409097235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67939089230680173606064823 101908633846020260409097235)
    ·
      refine ⟨152862950769030390613645853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101908633846020260409097235 152862950769030390613645853)
      ·
        refine ⟨57323606538386396480117195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152862950769030390613645853 57323606538386396480117195)
        ·
          refine ⟨85985409807579594720175793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57323606538386396480117195 85985409807579594720175793)
          ·
            refine ⟨64489057355684696040131845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85985409807579594720175793 64489057355684696040131845)
            ·
              refine ⟨12091698254190880507524721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64489057355684696040131845 12091698254190880507524721)
              ·
                refine ⟨9068773690643160380643541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12091698254190880507524721 9068773690643160380643541)
                ·
                  refine ⟨212549383374449071421333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9068773690643160380643541 212549383374449071421333)
                  ·
                    rfl

theorem cell22_1862723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 7].length) (baseStart_1862723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1862723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1862723 prefixEnd_1862723 := by exact prefixLift 1862723
  have htrace : WordTrace (prefixWord ++ tailWord_1862723) baseStart_1862723 baseEnd_1862723 := by
    simpa [prefixWord, tailWord_1862723, baseEnd_1862723] using wordTrace_append hprefix tailTrace_1862723
  have hstable : (prefixWord ++ tailWord_1862723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862723).length < 2 ^ (prefixWord ++ tailWord_1862723).sum := by decide
  have hdescent : baseEnd_1862723 < baseStart_1862723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862757 : List Nat := [1, 3, 1, 3, 2, 1, 5, 1, 5]
def baseStart_1862757 : Nat := 118140960795 + 1862757 * 2 ^ 59
def prefixEnd_1862757 : Nat := 4983230072969 + 3 ^ 40 * 1862757 * 2
def baseEnd_1862757 : Nat := 212553263006060819637965

theorem tailTrace_1862757 : CollatzResearch.WordTrace tailWord_1862757 prefixEnd_1862757 212553263006060819637965 := by
  unfold tailWord_1862757
  simp only [CollatzResearch.WordTrace]
  refine ⟨67940329312556997412802525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45293552875037998275201683 67940329312556997412802525)
  ·
    refine ⟨25477623492208874029800947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67940329312556997412802525 25477623492208874029800947)
    ·
      refine ⟨38216435238313311044701421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25477623492208874029800947 38216435238313311044701421)
      ·
        refine ⟨14331163214367491641763033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38216435238313311044701421 14331163214367491641763033)
        ·
          refine ⟨10748372410775618731322275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14331163214367491641763033 10748372410775618731322275)
          ·
            refine ⟨16122558616163428096983413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10748372410775618731322275 16122558616163428096983413)
            ·
              refine ⟨1511489870265321384092195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16122558616163428096983413 1511489870265321384092195)
              ·
                refine ⟨2267234805397982076138293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1511489870265321384092195 2267234805397982076138293)
                ·
                  refine ⟨212553263006060819637965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2267234805397982076138293 212553263006060819637965)
                  ·
                    rfl

theorem cell22_1862757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 5].length) (baseStart_1862757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1862757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1862757 prefixEnd_1862757 := by exact prefixLift 1862757
  have htrace : WordTrace (prefixWord ++ tailWord_1862757) baseStart_1862757 baseEnd_1862757 := by
    simpa [prefixWord, tailWord_1862757, baseEnd_1862757] using wordTrace_append hprefix tailTrace_1862757
  have hstable : (prefixWord ++ tailWord_1862757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862757).length < 2 ^ (prefixWord ++ tailWord_1862757).sum := by decide
  have hdescent : baseEnd_1862757 < baseStart_1862757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862802 : List Nat := [3, 2, 3, 1, 1, 2, 3, 1, 6]
def baseStart_1862802 : Nat := 118140960795 + 1862802 * 2 ^ 59
def prefixEnd_1862802 : Nat := 4983230072969 + 3 ^ 40 * 1862802 * 2
def baseEnd_1862802 : Nat := 212558397812605780512919

theorem tailTrace_1862802 : CollatzResearch.WordTrace tailWord_1862802 prefixEnd_1862802 212558397812605780512919 := by
  unfold tailWord_1862802
  simp only [CollatzResearch.WordTrace]
  refine ⟨16985492649348492524547665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45294647064929313398793773 16985492649348492524547665)
  ·
    refine ⟨12739119487011369393410749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16985492649348492524547665 12739119487011369393410749)
    ·
      refine ⟨4777169807629263522529031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12739119487011369393410749 4777169807629263522529031)
      ·
        refine ⟨7165754711443895283793547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4777169807629263522529031 7165754711443895283793547)
        ·
          refine ⟨10748632067165842925690321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7165754711443895283793547 10748632067165842925690321)
          ·
            refine ⟨8061474050374382194267741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10748632067165842925690321 8061474050374382194267741)
            ·
              refine ⟨3023052768890393322850403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8061474050374382194267741 3023052768890393322850403)
              ·
                refine ⟨4534579153335589984275605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3023052768890393322850403 4534579153335589984275605)
                ·
                  refine ⟨212558397812605780512919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4534579153335589984275605 212558397812605780512919)
                  ·
                    rfl

theorem cell22_1862802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_1862802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1862802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1862802 prefixEnd_1862802 := by exact prefixLift 1862802
  have htrace : WordTrace (prefixWord ++ tailWord_1862802) baseStart_1862802 baseEnd_1862802 := by
    simpa [prefixWord, tailWord_1862802, baseEnd_1862802] using wordTrace_append hprefix tailTrace_1862802
  have hstable : (prefixWord ++ tailWord_1862802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862802).length < 2 ^ (prefixWord ++ tailWord_1862802).sum := by decide
  have hdescent : baseEnd_1862802 < baseStart_1862802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862849 : List Nat := [1, 2, 6, 1, 1, 1, 2, 2, 2, 4]
def baseStart_1862849 : Nat := 118140960795 + 1862849 * 2 ^ 59
def prefixEnd_1862849 : Nat := 4983230072969 + 3 ^ 40 * 1862849 * 2
def baseEnd_1862849 : Nat := 637691282498324885613613

theorem tailTrace_1862849 : CollatzResearch.WordTrace tailWord_1862849 prefixEnd_1862849 637691282498324885613613 := by
  unfold tailWord_1862849
  simp only [CollatzResearch.WordTrace]
  refine ⟨67943684828223697125151601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45295789885482464750101067 67943684828223697125151601)
  ·
    refine ⟨50957763621167772843863701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67943684828223697125151601 50957763621167772843863701)
    ·
      refine ⟨2388645169742239352056111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50957763621167772843863701 2388645169742239352056111)
      ·
        refine ⟨3582967754613359028084167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2388645169742239352056111 3582967754613359028084167)
        ·
          refine ⟨5374451631920038542126251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3582967754613359028084167 5374451631920038542126251)
          ·
            refine ⟨8061677447880057813189377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5374451631920038542126251 8061677447880057813189377)
            ·
              refine ⟨6046258085910043359892033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8061677447880057813189377 6046258085910043359892033)
              ·
                refine ⟨4534693564432532519919025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6046258085910043359892033 4534693564432532519919025)
                ·
                  refine ⟨3401020173324399389939269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4534693564432532519919025 3401020173324399389939269)
                  ·
                    refine ⟨637691282498324885613613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3401020173324399389939269 637691282498324885613613)
                    ·
                      rfl

theorem cell22_1862849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_1862849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1862849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1862849 prefixEnd_1862849 := by exact prefixLift 1862849
  have htrace : WordTrace (prefixWord ++ tailWord_1862849) baseStart_1862849 baseEnd_1862849 := by
    simpa [prefixWord, tailWord_1862849, baseEnd_1862849] using wordTrace_append hprefix tailTrace_1862849
  have hstable : (prefixWord ++ tailWord_1862849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862849).length < 2 ^ (prefixWord ++ tailWord_1862849).sum := by decide
  have hdescent : baseEnd_1862849 < baseStart_1862849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863022 : List Nat := [4, 1, 2, 4, 2, 1, 2, 2, 4]
def baseStart_1863022 : Nat := 118140960795 + 1863022 * 2 ^ 59
def prefixEnd_1863022 : Nat := 4983230072969 + 3 ^ 40 * 1863022 * 2
def baseEnd_1863022 : Nat := 212583501311270033679361

theorem tailTrace_1863022 : CollatzResearch.WordTrace tailWord_1863022 prefixEnd_1863022 212583501311270033679361 := by
  unfold tailWord_1863022
  simp only [CollatzResearch.WordTrace]
  refine ⟨8493749332074618458899915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45299996437731298447466213 8493749332074618458899915)
  ·
    refine ⟨12740623998111927688349873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8493749332074618458899915 12740623998111927688349873)
    ·
      refine ⟨9555467998583945766262405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12740623998111927688349873 9555467998583945766262405)
      ·
        refine ⟨1791650249734489831174201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9555467998583945766262405 1791650249734489831174201)
        ·
          refine ⟨1343737687300867373380651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1791650249734489831174201 1343737687300867373380651)
          ·
            refine ⟨2015606530951301060070977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1343737687300867373380651 2015606530951301060070977)
            ·
              refine ⟨1511704898213475795053233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2015606530951301060070977 1511704898213475795053233)
              ·
                refine ⟨1133778673660106846289925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1511704898213475795053233 1133778673660106846289925)
                ·
                  refine ⟨212583501311270033679361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1133778673660106846289925 212583501311270033679361)
                  ·
                    rfl

theorem cell22_1863022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_1863022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863022 prefixEnd_1863022 := by exact prefixLift 1863022
  have htrace : WordTrace (prefixWord ++ tailWord_1863022) baseStart_1863022 baseEnd_1863022 := by
    simpa [prefixWord, tailWord_1863022, baseEnd_1863022] using wordTrace_append hprefix tailTrace_1863022
  have hstable : (prefixWord ++ tailWord_1863022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863022).length < 2 ^ (prefixWord ++ tailWord_1863022).sum := by decide
  have hdescent : baseEnd_1863022 < baseStart_1863022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863031 : List Nat := [1, 1, 3, 1, 1, 2, 5, 4, 1, 3]
def baseStart_1863031 : Nat := 118140960795 + 1863031 * 2 ^ 59
def prefixEnd_1863031 : Nat := 4983230072969 + 3 ^ 40 * 1863031 * 2
def baseEnd_1863031 : Nat := 637753584817737077563055

theorem tailTrace_1863031 : CollatzResearch.WordTrace tailWord_1863031 prefixEnd_1863031 637753584817737077563055 := by
  unfold tailWord_1863031
  simp only [CollatzResearch.WordTrace]
  refine ⟨67950322913564342208276947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45300215275709561472184631 67950322913564342208276947)
  ·
    refine ⟨101925484370346513312415421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67950322913564342208276947 101925484370346513312415421)
    ·
      refine ⟨38222056638879942492155783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101925484370346513312415421 38222056638879942492155783)
      ·
        refine ⟨57333084958319913738233675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38222056638879942492155783 57333084958319913738233675)
        ·
          refine ⟨85999627437479870607350513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57333084958319913738233675 85999627437479870607350513)
          ·
            refine ⟨64499720578109902955512885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85999627437479870607350513 64499720578109902955512885)
            ·
              refine ⟨6046848804197803402079333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64499720578109902955512885 6046848804197803402079333)
              ·
                refine ⟨1133784150787088137889875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6046848804197803402079333 1133784150787088137889875)
                ·
                  refine ⟨1700676226180632206834813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1133784150787088137889875 1700676226180632206834813)
                  ·
                    refine ⟨637753584817737077563055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1700676226180632206834813 637753584817737077563055)
                    ·
                      rfl

theorem cell22_1863031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 4, 1, 3].length) (baseStart_1863031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863031 prefixEnd_1863031 := by exact prefixLift 1863031
  have htrace : WordTrace (prefixWord ++ tailWord_1863031) baseStart_1863031 baseEnd_1863031 := by
    simpa [prefixWord, tailWord_1863031, baseEnd_1863031] using wordTrace_append hprefix tailTrace_1863031
  have hstable : (prefixWord ++ tailWord_1863031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863031).length < 2 ^ (prefixWord ++ tailWord_1863031).sum := by decide
  have hdescent : baseEnd_1863031 < baseStart_1863031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863044 : List Nat := [2, 3, 2, 1, 1, 3, 2, 3, 5]
def baseStart_1863044 : Nat := 118140960795 + 1863044 * 2 ^ 59
def prefixEnd_1863044 : Nat := 4983230072969 + 3 ^ 40 * 1863044 * 2
def baseEnd_1863044 : Nat := 212586011661136458996005

theorem tailTrace_1863044 : CollatzResearch.WordTrace tailWord_1863044 prefixEnd_1863044 212586011661136458996005 := by
  unfold tailWord_1863044
  simp only [CollatzResearch.WordTrace]
  refine ⟨33975398531258622714250093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45300531375011496952333457 33975398531258622714250093)
  ·
    refine ⟨12740774449221983517843785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33975398531258622714250093 12740774449221983517843785)
    ·
      refine ⟨9555580836916487638382839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12740774449221983517843785 9555580836916487638382839)
      ·
        refine ⟨14333371255374731457574259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9555580836916487638382839 14333371255374731457574259)
        ·
          refine ⟨21500056883062097186361389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14333371255374731457574259 21500056883062097186361389)
          ·
            refine ⟨8062521331148286444885521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21500056883062097186361389 8062521331148286444885521)
            ·
              refine ⟨6046890998361214833664141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8062521331148286444885521 6046890998361214833664141)
              ·
                refine ⟨2267584124385455562624053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6046890998361214833664141 2267584124385455562624053)
                ·
                  refine ⟨212586011661136458996005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2267584124385455562624053 212586011661136458996005)
                  ·
                    rfl

theorem cell22_1863044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_1863044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863044 prefixEnd_1863044 := by exact prefixLift 1863044
  have htrace : WordTrace (prefixWord ++ tailWord_1863044) baseStart_1863044 baseEnd_1863044 := by
    simpa [prefixWord, tailWord_1863044, baseEnd_1863044] using wordTrace_append hprefix tailTrace_1863044
  have hstable : (prefixWord ++ tailWord_1863044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863044).length < 2 ^ (prefixWord ++ tailWord_1863044).sum := by decide
  have hdescent : baseEnd_1863044 < baseStart_1863044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863072 : List Nat := [2, 1, 1, 4, 1, 2, 1, 2, 8]
def baseStart_1863072 : Nat := 118140960795 + 1863072 * 2 ^ 59
def prefixEnd_1863072 : Nat := 4983230072969 + 3 ^ 40 * 1863072 * 2
def baseEnd_1863072 : Nat := 212589206651875545762643

theorem tailTrace_1863072 : CollatzResearch.WordTrace tailWord_1863072 prefixEnd_1863072 212589206651875545762643 := by
  unfold tailWord_1863072
  simp only [CollatzResearch.WordTrace]
  refine ⟨33975909153207903105259735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45301212204277204140346313 33975909153207903105259735)
  ·
    refine ⟨50963863729811854657889603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33975909153207903105259735 50963863729811854657889603)
    ·
      refine ⟨76445795594717781986834405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50963863729811854657889603 76445795594717781986834405)
      ·
        refine ⟨14333586674009584122531451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76445795594717781986834405 14333586674009584122531451)
        ·
          refine ⟨21500380011014376183797177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14333586674009584122531451 21500380011014376183797177)
          ·
            refine ⟨16125285008260782137847883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21500380011014376183797177 16125285008260782137847883)
            ·
              refine ⟨24187927512391173206771825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16125285008260782137847883 24187927512391173206771825)
              ·
                refine ⟨18140945634293379905078869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24187927512391173206771825 18140945634293379905078869)
                ·
                  refine ⟨212589206651875545762643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18140945634293379905078869 212589206651875545762643)
                  ·
                    rfl

theorem cell22_1863072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 8].length) (baseStart_1863072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863072 prefixEnd_1863072 := by exact prefixLift 1863072
  have htrace : WordTrace (prefixWord ++ tailWord_1863072) baseStart_1863072 baseEnd_1863072 := by
    simpa [prefixWord, tailWord_1863072, baseEnd_1863072] using wordTrace_append hprefix tailTrace_1863072
  have hstable : (prefixWord ++ tailWord_1863072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863072).length < 2 ^ (prefixWord ++ tailWord_1863072).sum := by decide
  have hdescent : baseEnd_1863072 < baseStart_1863072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863087 : List Nat := [1, 1, 2, 1, 2, 2, 1, 4, 3, 5]
def baseStart_1863087 : Nat := 118140960795 + 1863087 * 2 ^ 59
def prefixEnd_1863087 : Nat := 4983230072969 + 3 ^ 40 * 1863087 * 2
def baseEnd_1863087 : Nat := 637772754762171598162883

theorem tailTrace_1863087 : CollatzResearch.WordTrace tailWord_1863087 prefixEnd_1863087 637772754762171598162883 := by
  unfold tailWord_1863087
  simp only [CollatzResearch.WordTrace]
  refine ⟨67952365401361463772315515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45301576934240975848210343 67952365401361463772315515)
  ·
    refine ⟨101928548102042195658473273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67952365401361463772315515 101928548102042195658473273)
    ·
      refine ⟨76446411076531646743854955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101928548102042195658473273 76446411076531646743854955)
      ·
        refine ⟨114669616614797470115782433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76446411076531646743854955 114669616614797470115782433)
        ·
          refine ⟨86002212461098102586836825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114669616614797470115782433 86002212461098102586836825)
          ·
            refine ⟨64501659345823576940127619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86002212461098102586836825 64501659345823576940127619)
            ·
              refine ⟨96752489018735365410191429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64501659345823576940127619 96752489018735365410191429)
              ·
                refine ⟨18141091691012881014410893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96752489018735365410191429 18141091691012881014410893)
                ·
                  refine ⟨6802909384129830380404085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18141091691012881014410893 6802909384129830380404085)
                  ·
                    refine ⟨637772754762171598162883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6802909384129830380404085 637772754762171598162883)
                    ·
                      rfl

theorem cell22_1863087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 5].length) (baseStart_1863087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863087 prefixEnd_1863087 := by exact prefixLift 1863087
  have htrace : WordTrace (prefixWord ++ tailWord_1863087) baseStart_1863087 baseEnd_1863087 := by
    simpa [prefixWord, tailWord_1863087, baseEnd_1863087] using wordTrace_append hprefix tailTrace_1863087
  have hstable : (prefixWord ++ tailWord_1863087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863087).length < 2 ^ (prefixWord ++ tailWord_1863087).sum := by decide
  have hdescent : baseEnd_1863087 < baseStart_1863087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863089 : List Nat := [1, 2, 2, 4, 1, 1, 4, 1, 6]
def baseStart_1863089 : Nat := 118140960795 + 1863089 * 2 ^ 59
def prefixEnd_1863089 : Nat := 4983230072969 + 3 ^ 40 * 1863089 * 2
def baseEnd_1863089 : Nat := 212591146467681419870959

theorem tailTrace_1863089 : CollatzResearch.WordTrace tailWord_1863089 prefixEnd_1863089 212591146467681419870959 := by
  unfold tailWord_1863089
  simp only [CollatzResearch.WordTrace]
  refine ⟨67952438347354218113888321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45301625564902812075925547 67952438347354218113888321)
  ·
    refine ⟨50964328760515663585416241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67952438347354218113888321 50964328760515663585416241)
    ·
      refine ⟨38223246570386747689062181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50964328760515663585416241 38223246570386747689062181)
      ·
        refine ⟨7166858731947515191699159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38223246570386747689062181 7166858731947515191699159)
        ·
          refine ⟨10750288097921272787548739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7166858731947515191699159 10750288097921272787548739)
          ·
            refine ⟨16125432146881909181323109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10750288097921272787548739 16125432146881909181323109)
            ·
              refine ⟨3023518527540357971498083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16125432146881909181323109 3023518527540357971498083)
              ·
                refine ⟨4535277791310536957247125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3023518527540357971498083 4535277791310536957247125)
                ·
                  refine ⟨212591146467681419870959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4535277791310536957247125 212591146467681419870959)
                  ·
                    rfl

theorem cell22_1863089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 6].length) (baseStart_1863089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863089 prefixEnd_1863089 := by exact prefixLift 1863089
  have htrace : WordTrace (prefixWord ++ tailWord_1863089) baseStart_1863089 baseEnd_1863089 := by
    simpa [prefixWord, tailWord_1863089, baseEnd_1863089] using wordTrace_append hprefix tailTrace_1863089
  have hstable : (prefixWord ++ tailWord_1863089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863089).length < 2 ^ (prefixWord ++ tailWord_1863089).sum := by decide
  have hdescent : baseEnd_1863089 < baseStart_1863089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863104 : List Nat := [2, 1, 1, 2, 3, 1, 5, 1, 1, 5]
def baseStart_1863104 : Nat := 118140960795 + 1863104 * 2 ^ 59
def prefixEnd_1863104 : Nat := 4983230072969 + 3 ^ 40 * 1863104 * 2
def baseEnd_1863104 : Nat := 637778574209589220487831

theorem tailTrace_1863104 : CollatzResearch.WordTrace tailWord_1863104 prefixEnd_1863104 637778574209589220487831 := by
  unfold tailWord_1863104
  simp only [CollatzResearch.WordTrace]
  refine ⟨33976492721149937837842183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45301990294866583783789577 33976492721149937837842183)
  ·
    refine ⟨50964739081724906756763275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33976492721149937837842183 50964739081724906756763275)
    ·
      refine ⟨76447108622587360135144913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50964739081724906756763275 76447108622587360135144913)
      ·
        refine ⟨57335331466940520101358685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76447108622587360135144913 57335331466940520101358685)
        ·
          refine ⟨21500749300102695038009507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57335331466940520101358685 21500749300102695038009507)
          ·
            refine ⟨32251123950154042557014261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21500749300102695038009507 32251123950154042557014261)
            ·
              refine ⟨3023542870326941489720087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32251123950154042557014261 3023542870326941489720087)
              ·
                refine ⟨4535314305490412234580131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3023542870326941489720087 4535314305490412234580131)
                ·
                  refine ⟨6802971458235618351870197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4535314305490412234580131 6802971458235618351870197)
                  ·
                    refine ⟨637778574209589220487831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6802971458235618351870197 637778574209589220487831)
                    ·
                      rfl

theorem cell22_1863104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 1, 5].length) (baseStart_1863104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863104 prefixEnd_1863104 := by exact prefixLift 1863104
  have htrace : WordTrace (prefixWord ++ tailWord_1863104) baseStart_1863104 baseEnd_1863104 := by
    simpa [prefixWord, tailWord_1863104, baseEnd_1863104] using wordTrace_append hprefix tailTrace_1863104
  have hstable : (prefixWord ++ tailWord_1863104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863104).length < 2 ^ (prefixWord ++ tailWord_1863104).sum := by decide
  have hdescent : baseEnd_1863104 < baseStart_1863104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863108 : List Nat := [2, 3, 3, 2, 1, 2, 2, 2, 1, 4]
def baseStart_1863108 : Nat := 118140960795 + 1863108 * 2 ^ 59
def prefixEnd_1863108 : Nat := 4983230072969 + 3 ^ 40 * 1863108 * 2
def baseEnd_1863108 : Nat := 637779943491334543387819

theorem tailTrace_1863108 : CollatzResearch.WordTrace tailWord_1863108 prefixEnd_1863108 637779943491334543387819 := by
  unfold tailWord_1863108
  simp only [CollatzResearch.WordTrace]
  refine ⟨33976565667142692179414989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45302087556190256239219985 33976565667142692179414989)
  ·
    refine ⟨12741212125178509567280621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33976565667142692179414989 12741212125178509567280621)
    ·
      refine ⟨4777954546941941087730233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12741212125178509567280621 4777954546941941087730233)
      ·
        refine ⟨3583465910206455815797675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4777954546941941087730233 3583465910206455815797675)
        ·
          refine ⟨5375198865309683723696513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3583465910206455815797675 5375198865309683723696513)
          ·
            refine ⟨4031399148982262792772385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5375198865309683723696513 4031399148982262792772385)
            ·
              refine ⟨3023549361736697094579289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4031399148982262792772385 3023549361736697094579289)
              ·
                refine ⟨2267662021302522820934467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3023549361736697094579289 2267662021302522820934467)
                ·
                  refine ⟨3401493031953784231401701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2267662021302522820934467 3401493031953784231401701)
                  ·
                    refine ⟨637779943491334543387819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3401493031953784231401701 637779943491334543387819)
                    ·
                      rfl

theorem cell22_1863108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_1863108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863108 prefixEnd_1863108 := by exact prefixLift 1863108
  have htrace : WordTrace (prefixWord ++ tailWord_1863108) baseStart_1863108 baseEnd_1863108 := by
    simpa [prefixWord, tailWord_1863108, baseEnd_1863108] using wordTrace_append hprefix tailTrace_1863108
  have hstable : (prefixWord ++ tailWord_1863108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863108).length < 2 ^ (prefixWord ++ tailWord_1863108).sum := by decide
  have hdescent : baseEnd_1863108 < baseStart_1863108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863194 : List Nat := [3, 1, 1, 3, 1, 1, 1, 4, 2, 5]
def baseStart_1863194 : Nat := 118140960795 + 1863194 * 2 ^ 59
def prefixEnd_1863194 : Nat := 4983230072969 + 3 ^ 40 * 1863194 * 2
def baseEnd_1863194 : Nat := 637809383048858985737555

theorem tailTrace_1863194 : CollatzResearch.WordTrace tailWord_1863194 prefixEnd_1863194 637809383048858985737555 := by
  unfold tailWord_1863194
  simp only [CollatzResearch.WordTrace]
  refine ⟨16989067002993455261615159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45304178674649214030973757 16989067002993455261615159)
  ·
    refine ⟨25483600504490182892422739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16989067002993455261615159 25483600504490182892422739)
    ·
      refine ⟨38225400756735274338634109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25483600504490182892422739 38225400756735274338634109)
      ·
        refine ⟨14334525283775727876987791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38225400756735274338634109 14334525283775727876987791)
        ·
          refine ⟨21501787925663591815481687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14334525283775727876987791 21501787925663591815481687)
          ·
            refine ⟨32252681888495387723222531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21501787925663591815481687 32252681888495387723222531)
            ·
              refine ⟨48379022832743081584833797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32252681888495387723222531 48379022832743081584833797)
              ·
                refine ⟨9071066781139327797156337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48379022832743081584833797 9071066781139327797156337)
                ·
                  refine ⟨6803300085854495847867253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9071066781139327797156337 6803300085854495847867253)
                  ·
                    refine ⟨637809383048858985737555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6803300085854495847867253 637809383048858985737555)
                    ·
                      rfl

theorem cell22_1863194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_1863194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863194 prefixEnd_1863194 := by exact prefixLift 1863194
  have htrace : WordTrace (prefixWord ++ tailWord_1863194) baseStart_1863194 baseEnd_1863194 := by
    simpa [prefixWord, tailWord_1863194, baseEnd_1863194] using wordTrace_append hprefix tailTrace_1863194
  have hstable : (prefixWord ++ tailWord_1863194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863194).length < 2 ^ (prefixWord ++ tailWord_1863194).sum := by decide
  have hdescent : baseEnd_1863194 < baseStart_1863194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863196 : List Nat := [2, 2, 3, 1, 2, 1, 4, 2, 5]
def baseStart_1863196 : Nat := 118140960795 + 1863196 * 2 ^ 59
def prefixEnd_1863196 : Nat := 4983230072969 + 3 ^ 40 * 1863196 * 2
def baseEnd_1863196 : Nat := 212603355896577215729183

theorem tailTrace_1863196 : CollatzResearch.WordTrace tailWord_1863196 prefixEnd_1863196 212603355896577215729183 := by
  unfold tailWord_1863196
  simp only [CollatzResearch.WordTrace]
  refine ⟨33978170478983287694016721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45304227305311050258688961 33978170478983287694016721)
  ·
    refine ⟨25483627859237465770512541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33978170478983287694016721 25483627859237465770512541)
    ·
      refine ⟨9556360447214049663942203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25483627859237465770512541 9556360447214049663942203)
      ·
        refine ⟨14334540670821074495913305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9556360447214049663942203 14334540670821074495913305)
        ·
          refine ⟨10750905503115805871934979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14334540670821074495913305 10750905503115805871934979)
          ·
            refine ⟨16126358254673708807902469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10750905503115805871934979 16126358254673708807902469)
            ·
              refine ⟨3023692172751320401481713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16126358254673708807902469 3023692172751320401481713)
              ·
                refine ⟨2267769129563490301111285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3023692172751320401481713 2267769129563490301111285)
                ·
                  refine ⟨212603355896577215729183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2267769129563490301111285 212603355896577215729183)
                  ·
                    rfl

theorem cell22_1863196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 5].length) (baseStart_1863196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863196 prefixEnd_1863196 := by exact prefixLift 1863196
  have htrace : WordTrace (prefixWord ++ tailWord_1863196) baseStart_1863196 baseEnd_1863196 := by
    simpa [prefixWord, tailWord_1863196, baseEnd_1863196] using wordTrace_append hprefix tailTrace_1863196
  have hstable : (prefixWord ++ tailWord_1863196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863196).length < 2 ^ (prefixWord ++ tailWord_1863196).sum := by decide
  have hdescent : baseEnd_1863196 < baseStart_1863196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863200 : List Nat := [2, 1, 1, 6, 1, 2, 1, 4, 1, 3]
def baseStart_1863200 : Nat := 118140960795 + 1863200 * 2 ^ 59
def prefixEnd_1863200 : Nat := 4983230072969 + 3 ^ 40 * 1863200 * 2
def baseEnd_1863200 : Nat := 637811436971476970087537

theorem tailTrace_1863200 : CollatzResearch.WordTrace tailWord_1863200 prefixEnd_1863200 637811436971476970087537 := by
  unfold tailWord_1863200
  simp only [CollatzResearch.WordTrace]
  refine ⟨33978243424976042035589527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45304324566634722714119369 33978243424976042035589527)
  ·
    refine ⟨50967365137464063053384291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33978243424976042035589527 50967365137464063053384291)
    ·
      refine ⟨76451047706196094580076437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50967365137464063053384291 76451047706196094580076437)
      ·
        refine ⟨3583642861227941933441083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 76451047706196094580076437 3583642861227941933441083)
        ·
          refine ⟨5375464291841912900161625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3583642861227941933441083 5375464291841912900161625)
          ·
            refine ⟨4031598218881434675121219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5375464291841912900161625 4031598218881434675121219)
            ·
              refine ⟨6047397328322152012681829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4031598218881434675121219 6047397328322152012681829)
              ·
                refine ⟨1133886999060403502377843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6047397328322152012681829 1133886999060403502377843)
                ·
                  refine ⟨1700830498590605253566765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1133886999060403502377843 1700830498590605253566765)
                  ·
                    refine ⟨637811436971476970087537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1700830498590605253566765 637811436971476970087537)
                    ·
                      rfl

theorem cell22_1863200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 4, 1, 3].length) (baseStart_1863200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863200 prefixEnd_1863200 := by exact prefixLift 1863200
  have htrace : WordTrace (prefixWord ++ tailWord_1863200) baseStart_1863200 baseEnd_1863200 := by
    simpa [prefixWord, tailWord_1863200, baseEnd_1863200] using wordTrace_append hprefix tailTrace_1863200
  have hstable : (prefixWord ++ tailWord_1863200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863200).length < 2 ^ (prefixWord ++ tailWord_1863200).sum := by decide
  have hdescent : baseEnd_1863200 < baseStart_1863200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863224 : List Nat := [2, 1, 2, 1, 4, 2, 1, 1, 8]
def baseStart_1863224 : Nat := 118140960795 + 1863224 * 2 ^ 59
def prefixEnd_1863224 : Nat := 4983230072969 + 3 ^ 40 * 1863224 * 2
def baseEnd_1863224 : Nat := 212606550887316302495821

theorem tailTrace_1863224 : CollatzResearch.WordTrace tailWord_1863224 prefixEnd_1863224 212606550887316302495821 := by
  unfold tailWord_1863224
  simp only [CollatzResearch.WordTrace]
  refine ⟨33978681100932568085026363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45304908134576757446701817 33978681100932568085026363)
  ·
    refine ⟨50968021651398852127539545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33978681100932568085026363 50968021651398852127539545)
    ·
      refine ⟨38226016238549139095654659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50968021651398852127539545 38226016238549139095654659)
      ·
        refine ⟨57339024357823708643481989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38226016238549139095654659 57339024357823708643481989)
        ·
          refine ⟨10751067067091945370652873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57339024357823708643481989 10751067067091945370652873)
          ·
            refine ⟨8063300300318959027989655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10751067067091945370652873 8063300300318959027989655)
            ·
              refine ⟨12094950450478438541984483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8063300300318959027989655 12094950450478438541984483)
              ·
                refine ⟨18142425675717657812976725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12094950450478438541984483 18142425675717657812976725)
                ·
                  refine ⟨212606550887316302495821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18142425675717657812976725 212606550887316302495821)
                  ·
                    rfl

theorem cell22_1863224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 8].length) (baseStart_1863224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863224 prefixEnd_1863224 := by exact prefixLift 1863224
  have htrace : WordTrace (prefixWord ++ tailWord_1863224) baseStart_1863224 baseEnd_1863224 := by
    simpa [prefixWord, tailWord_1863224, baseEnd_1863224] using wordTrace_append hprefix tailTrace_1863224
  have hstable : (prefixWord ++ tailWord_1863224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863224).length < 2 ^ (prefixWord ++ tailWord_1863224).sum := by decide
  have hdescent : baseEnd_1863224 < baseStart_1863224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863226 : List Nat := [3, 1, 1, 1, 3, 2, 2, 4, 1, 4]
def baseStart_1863226 : Nat := 118140960795 + 1863226 * 2 ^ 59
def prefixEnd_1863226 : Nat := 4983230072969 + 3 ^ 40 * 1863226 * 2
def baseEnd_1863226 : Nat := 637820337302821568937457

theorem tailTrace_1863226 : CollatzResearch.WordTrace tailWord_1863226 prefixEnd_1863226 637820337302821568937457 := by
  unfold tailWord_1863226
  simp only [CollatzResearch.WordTrace]
  refine ⟨16989358786964472627906383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45304956765238593674417021 16989358786964472627906383)
  ·
    refine ⟨25484038180446708941859575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16989358786964472627906383 25484038180446708941859575)
    ·
      refine ⟨38226057270670063412789363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25484038180446708941859575 38226057270670063412789363)
      ·
        refine ⟨57339085906005095119184045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38226057270670063412789363 57339085906005095119184045)
        ·
          refine ⟨21502157214751910669694017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57339085906005095119184045 21502157214751910669694017)
          ·
            refine ⟨16126617911063933002270513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21502157214751910669694017 16126617911063933002270513)
            ·
              refine ⟨12094963433297949751702885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16126617911063933002270513 12094963433297949751702885)
              ·
                refine ⟨2267805643743365578444291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12094963433297949751702885 2267805643743365578444291)
                ·
                  refine ⟨3401708465615048367666437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2267805643743365578444291 3401708465615048367666437)
                  ·
                    refine ⟨637820337302821568937457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3401708465615048367666437 637820337302821568937457)
                    ·
                      rfl

theorem cell22_1863226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 1, 4].length) (baseStart_1863226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863226 prefixEnd_1863226 := by exact prefixLift 1863226
  have htrace : WordTrace (prefixWord ++ tailWord_1863226) baseStart_1863226 baseEnd_1863226 := by
    simpa [prefixWord, tailWord_1863226, baseEnd_1863226] using wordTrace_append hprefix tailTrace_1863226
  have hstable : (prefixWord ++ tailWord_1863226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863226).length < 2 ^ (prefixWord ++ tailWord_1863226).sum := by decide
  have hdescent : baseEnd_1863226 < baseStart_1863226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863299 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 1, 8]
def baseStart_1863299 : Nat := 118140960795 + 1863299 * 2 ^ 59
def prefixEnd_1863299 : Nat := 4983230072969 + 3 ^ 40 * 1863299 * 2
def baseEnd_1863299 : Nat := 637845326694673711862233

theorem tailTrace_1863299 : CollatzResearch.WordTrace tailWord_1863299 prefixEnd_1863299 637845326694673711862233 := by
  unfold tailWord_1863299
  simp only [CollatzResearch.WordTrace]
  refine ⟨67960097676593423979032951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45306731784395615986021967 67960097676593423979032951)
  ·
    refine ⟨101940146514890135968549427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67960097676593423979032951 101940146514890135968549427)
    ·
      refine ⟨152910219772335203952824141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101940146514890135968549427 152910219772335203952824141)
      ·
        refine ⟨57341332414625701482309053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152910219772335203952824141 57341332414625701482309053)
        ·
          refine ⟨21502999655484638055865895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57341332414625701482309053 21502999655484638055865895)
          ·
            refine ⟨32254499483226957083798843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21502999655484638055865895 32254499483226957083798843)
            ·
              refine ⟨48381749224840435625698265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32254499483226957083798843 48381749224840435625698265)
              ·
                refine ⟨36286311918630326719273699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48381749224840435625698265 36286311918630326719273699)
                ·
                  refine ⟨54429467877945490078910549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36286311918630326719273699 54429467877945490078910549)
                  ·
                    refine ⟨637845326694673711862233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54429467877945490078910549 637845326694673711862233)
                    ·
                      rfl

theorem cell22_1863299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 8].length) (baseStart_1863299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863299 prefixEnd_1863299 := by exact prefixLift 1863299
  have htrace : WordTrace (prefixWord ++ tailWord_1863299) baseStart_1863299 baseEnd_1863299 := by
    simpa [prefixWord, tailWord_1863299, baseEnd_1863299] using wordTrace_append hprefix tailTrace_1863299
  have hstable : (prefixWord ++ tailWord_1863299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863299).length < 2 ^ (prefixWord ++ tailWord_1863299).sum := by decide
  have hdescent : baseEnd_1863299 < baseStart_1863299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863324 : List Nat := [2, 2, 3, 2, 4, 1, 2, 1, 2, 3]
def baseStart_1863324 : Nat := 118140960795 + 1863324 * 2 ^ 59
def prefixEnd_1863324 : Nat := 4983230072969 + 3 ^ 40 * 1863324 * 2
def baseEnd_1863324 : Nat := 637853884705581979987157

theorem tailTrace_1863324 : CollatzResearch.WordTrace tailWord_1863324 prefixEnd_1863324 637853884705581979987157 := by
  unfold tailWord_1863324
  simp only [CollatzResearch.WordTrace]
  refine ⟨33980504750751426624346513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45307339667668568832462017 33980504750751426624346513)
  ·
    refine ⟨25485378563063569968259885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33980504750751426624346513 25485378563063569968259885)
    ·
      refine ⟨9557016961148838738097457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25485378563063569968259885 9557016961148838738097457)
      ·
        refine ⟨7167762720861629053573093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9557016961148838738097457 7167762720861629053573093)
        ·
          refine ⟨1343955510161555447544955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7167762720861629053573093 1343955510161555447544955)
          ·
            refine ⟨2015933265242333171317433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1343955510161555447544955 2015933265242333171317433)
            ·
              refine ⟨1511949948931749878488075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2015933265242333171317433 1511949948931749878488075)
              ·
                refine ⟨2267924923397624817732113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1511949948931749878488075 2267924923397624817732113)
                ·
                  refine ⟨1700943692548218613299085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2267924923397624817732113 1700943692548218613299085)
                  ·
                    refine ⟨637853884705581979987157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1700943692548218613299085 637853884705581979987157)
                    ·
                      rfl

theorem cell22_1863324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_1863324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863324 prefixEnd_1863324 := by exact prefixLift 1863324
  have htrace : WordTrace (prefixWord ++ tailWord_1863324) baseStart_1863324 baseEnd_1863324 := by
    simpa [prefixWord, tailWord_1863324, baseEnd_1863324] using wordTrace_append hprefix tailTrace_1863324
  have hstable : (prefixWord ++ tailWord_1863324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863324).length < 2 ^ (prefixWord ++ tailWord_1863324).sum := by decide
  have hdescent : baseEnd_1863324 < baseStart_1863324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863331 : List Nat := [1, 1, 1, 4, 1, 1, 5, 3, 5]
def baseStart_1863331 : Nat := 118140960795 + 1863331 * 2 ^ 59
def prefixEnd_1863331 : Nat := 4983230072969 + 3 ^ 40 * 1863331 * 2
def baseEnd_1863331 : Nat := 212618760316212098354045

theorem tailTrace_1863331 : CollatzResearch.WordTrace tailWord_1863331 prefixEnd_1863331 212618760316212098354045 := by
  unfold tailWord_1863331
  simp only [CollatzResearch.WordTrace]
  refine ⟨67961264812477493444197847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45307509874984995629465231 67961264812477493444197847)
  ·
    refine ⟨101941897218716240166296771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67961264812477493444197847 101941897218716240166296771)
    ·
      refine ⟨152912845828074360249445157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101941897218716240166296771 152912845828074360249445157)
      ·
        refine ⟨28671158592763942546770967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152912845828074360249445157 28671158592763942546770967)
        ·
          refine ⟨43006737889145913820156451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28671158592763942546770967 43006737889145913820156451)
          ·
            refine ⟨64510106833718870730234677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43006737889145913820156451 64510106833718870730234677)
            ·
              refine ⟨6047822515661144130959501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64510106833718870730234677 6047822515661144130959501)
              ·
                refine ⟨2267933443372929049109813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6047822515661144130959501 2267933443372929049109813)
                ·
                  refine ⟨212618760316212098354045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2267933443372929049109813 212618760316212098354045)
                  ·
                    rfl

theorem cell22_1863331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 5].length) (baseStart_1863331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863331 prefixEnd_1863331 := by exact prefixLift 1863331
  have htrace : WordTrace (prefixWord ++ tailWord_1863331) baseStart_1863331 baseEnd_1863331 := by
    simpa [prefixWord, tailWord_1863331, baseEnd_1863331] using wordTrace_append hprefix tailTrace_1863331
  have hstable : (prefixWord ++ tailWord_1863331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863331).length < 2 ^ (prefixWord ++ tailWord_1863331).sum := by decide
  have hdescent : baseEnd_1863331 < baseStart_1863331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863378 : List Nat := [3, 2, 2, 2, 2, 1, 1, 2, 3, 4]
def baseStart_1863378 : Nat := 118140960795 + 1863378 * 2 ^ 59
def prefixEnd_1863378 : Nat := 4983230072969 + 3 ^ 40 * 1863378 * 2
def baseEnd_1863378 : Nat := 637872370009143839136991

theorem tailTrace_1863378 : CollatzResearch.WordTrace tailWord_1863378 prefixEnd_1863378 637872370009143839136991 := by
  unfold tailWord_1863378
  simp only [CollatzResearch.WordTrace]
  refine ⟨16990744760826805117789697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45308652695538146980772525 16990744760826805117789697)
  ·
    refine ⟨12743058570620103838342273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16990744760826805117789697 12743058570620103838342273)
    ·
      refine ⟨9557293927965077878756705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12743058570620103838342273 9557293927965077878756705)
      ·
        refine ⟨7167970445973808409067529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9557293927965077878756705 7167970445973808409067529)
        ·
          refine ⟨5375977834480356306800647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7167970445973808409067529 5375977834480356306800647)
          ·
            refine ⟨8063966751720534460200971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5375977834480356306800647 8063966751720534460200971)
            ·
              refine ⟨12095950127580801690301457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8063966751720534460200971 12095950127580801690301457)
              ·
                refine ⟨9071962595685601267726093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12095950127580801690301457 9071962595685601267726093)
                ·
                  refine ⟨3401985973382100475397285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9071962595685601267726093 3401985973382100475397285)
                  ·
                    refine ⟨637872370009143839136991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3401985973382100475397285 637872370009143839136991)
                    ·
                      rfl

theorem cell22_1863378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_1863378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863378 prefixEnd_1863378 := by exact prefixLift 1863378
  have htrace : WordTrace (prefixWord ++ tailWord_1863378) baseStart_1863378 baseEnd_1863378 := by
    simpa [prefixWord, tailWord_1863378, baseEnd_1863378] using wordTrace_append hprefix tailTrace_1863378
  have hstable : (prefixWord ++ tailWord_1863378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863378).length < 2 ^ (prefixWord ++ tailWord_1863378).sum := by decide
  have hdescent : baseEnd_1863378 < baseStart_1863378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863393 : List Nat := [1, 2, 3, 1, 5, 1, 1, 2, 6]
def baseStart_1863393 : Nat := 118140960795 + 1863393 * 2 ^ 59
def prefixEnd_1863393 : Nat := 4983230072969 + 3 ^ 40 * 1863393 * 2
def baseEnd_1863393 : Nat := 212625834938562933337315

theorem tailTrace_1863393 : CollatzResearch.WordTrace tailWord_1863393 prefixEnd_1863393 212625834938562933337315 := by
  unfold tailWord_1863393
  simp only [CollatzResearch.WordTrace]
  refine ⟨67963526138252878032954833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45309017425501918688636555 67963526138252878032954833)
  ·
    refine ⟨50972644603689658524716125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67963526138252878032954833 50972644603689658524716125)
    ·
      refine ⟨19114741726383621946768547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50972644603689658524716125 19114741726383621946768547)
      ·
        refine ⟨28672112589575432920152821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19114741726383621946768547 28672112589575432920152821)
        ·
          refine ⟨2688010555272696836264327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28672112589575432920152821 2688010555272696836264327)
          ·
            refine ⟨4032015832909045254396491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2688010555272696836264327 4032015832909045254396491)
            ·
              refine ⟨6048023749363567881594737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4032015832909045254396491 6048023749363567881594737)
              ·
                refine ⟨4536017812022675911196053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6048023749363567881594737 4536017812022675911196053)
                ·
                  refine ⟨212625834938562933337315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4536017812022675911196053 212625834938562933337315)
                  ·
                    rfl

theorem cell22_1863393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 6].length) (baseStart_1863393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863393 prefixEnd_1863393 := by exact prefixLift 1863393
  have htrace : WordTrace (prefixWord ++ tailWord_1863393) baseStart_1863393 baseEnd_1863393 := by
    simpa [prefixWord, tailWord_1863393, baseEnd_1863393] using wordTrace_append hprefix tailTrace_1863393
  have hstable : (prefixWord ++ tailWord_1863393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863393).length < 2 ^ (prefixWord ++ tailWord_1863393).sum := by decide
  have hdescent : baseEnd_1863393 < baseStart_1863393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863410 : List Nat := [3, 2, 1, 3, 1, 1, 4, 3, 4]
def baseStart_1863410 : Nat := 118140960795 + 1863410 * 2 ^ 59
def prefixEnd_1863410 : Nat := 4983230072969 + 3 ^ 40 * 1863410 * 2
def baseEnd_1863410 : Nat := 212627774754368807445631

theorem tailTrace_1863410 : CollatzResearch.WordTrace tailWord_1863410 prefixEnd_1863410 212627774754368807445631 := by
  unfold tailWord_1863410
  simp only [CollatzResearch.WordTrace]
  refine ⟨16991036544797822484080921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45309430786127526624215789 16991036544797822484080921)
  ·
    refine ⟨12743277408598366863060691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16991036544797822484080921 12743277408598366863060691)
    ·
      refine ⟨19114916112897550294591037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12743277408598366863060691 19114916112897550294591037)
      ·
        refine ⟨7168093542336581360471639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19114916112897550294591037 7168093542336581360471639)
        ·
          refine ⟨10752140313504872040707459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7168093542336581360471639 10752140313504872040707459)
          ·
            refine ⟨16128210470257308061061189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10752140313504872040707459 16128210470257308061061189)
            ·
              refine ⟨3024039463173245261448973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16128210470257308061061189 3024039463173245261448973)
              ·
                refine ⟨1134014798689966973043365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3024039463173245261448973 1134014798689966973043365)
                ·
                  refine ⟨212627774754368807445631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1134014798689966973043365 212627774754368807445631)
                  ·
                    rfl

theorem cell22_1863410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_1863410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863410 prefixEnd_1863410 := by exact prefixLift 1863410
  have htrace : WordTrace (prefixWord ++ tailWord_1863410) baseStart_1863410 baseEnd_1863410 := by
    simpa [prefixWord, tailWord_1863410, baseEnd_1863410] using wordTrace_append hprefix tailTrace_1863410
  have hstable : (prefixWord ++ tailWord_1863410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863410).length < 2 ^ (prefixWord ++ tailWord_1863410).sum := by decide
  have hdescent : baseEnd_1863410 < baseStart_1863410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863425 : List Nat := [1, 2, 4, 1, 1, 1, 5, 2, 2, 3]
def baseStart_1863425 : Nat := 118140960795 + 1863425 * 2 ^ 59
def prefixEnd_1863425 : Nat := 4983230072969 + 3 ^ 40 * 1863425 * 2
def baseEnd_1863425 : Nat := 637888459069651383211847

theorem tailTrace_1863425 : CollatzResearch.WordTrace tailWord_1863425 prefixEnd_1863425 637888459069651383211847 := by
  unfold tailWord_1863425
  simp only [CollatzResearch.WordTrace]
  refine ⟨67964693274136947498119729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45309795516091298332079819 67964693274136947498119729)
  ·
    refine ⟨50973519955602710623589797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67964693274136947498119729 50973519955602710623589797)
    ·
      refine ⟨9557534991675508241923087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50973519955602710623589797 9557534991675508241923087)
      ·
        refine ⟨14336302487513262362884631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9557534991675508241923087 14336302487513262362884631)
        ·
          refine ⟨21504453731269893544326947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14336302487513262362884631 21504453731269893544326947)
          ·
            refine ⟨32256680596904840316490421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21504453731269893544326947 32256680596904840316490421)
            ·
              refine ⟨3024063805959828779670977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32256680596904840316490421 3024063805959828779670977)
              ·
                refine ⟨2268047854469871584753233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3024063805959828779670977 2268047854469871584753233)
                ·
                  refine ⟨1701035890852403688564925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2268047854469871584753233 1701035890852403688564925)
                  ·
                    refine ⟨637888459069651383211847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1701035890852403688564925 637888459069651383211847)
                    ·
                      rfl

theorem cell22_1863425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_1863425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863425 prefixEnd_1863425 := by exact prefixLift 1863425
  have htrace : WordTrace (prefixWord ++ tailWord_1863425) baseStart_1863425 baseEnd_1863425 := by
    simpa [prefixWord, tailWord_1863425, baseEnd_1863425] using wordTrace_append hprefix tailTrace_1863425
  have hstable : (prefixWord ++ tailWord_1863425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863425).length < 2 ^ (prefixWord ++ tailWord_1863425).sum := by decide
  have hdescent : baseEnd_1863425 < baseStart_1863425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863442 : List Nat := [3, 2, 4, 1, 1, 3, 1, 1, 1, 5]
def baseStart_1863442 : Nat := 118140960795 + 1863442 * 2 ^ 59
def prefixEnd_1863442 : Nat := 4983230072969 + 3 ^ 40 * 1863442 * 2
def baseEnd_1863442 : Nat := 637894278517069005536795

theorem tailTrace_1863442 : CollatzResearch.WordTrace tailWord_1863442 prefixEnd_1863442 637894278517069005536795 := by
  unfold tailWord_1863442
  simp only [CollatzResearch.WordTrace]
  refine ⟨16991328328768839850372145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45310208876716906267659053 16991328328768839850372145)
  ·
    refine ⟨12743496246576629887779109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16991328328768839850372145 12743496246576629887779109)
    ·
      refine ⟨2389405546233118103958583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12743496246576629887779109 2389405546233118103958583)
      ·
        refine ⟨3584108319349677155937875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2389405546233118103958583 3584108319349677155937875)
        ·
          refine ⟨5376162479024515733906813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3584108319349677155937875 5376162479024515733906813)
          ·
            refine ⟨2016060929634193400215055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5376162479024515733906813 2016060929634193400215055)
            ·
              refine ⟨3024091394451290100322583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2016060929634193400215055 3024091394451290100322583)
              ·
                refine ⟨4536137091676935150483875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3024091394451290100322583 4536137091676935150483875)
                ·
                  refine ⟨6804205637515402725725813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4536137091676935150483875 6804205637515402725725813)
                  ·
                    refine ⟨637894278517069005536795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6804205637515402725725813 637894278517069005536795)
                    ·
                      rfl

theorem cell22_1863442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_1863442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863442 prefixEnd_1863442 := by exact prefixLift 1863442
  have htrace : WordTrace (prefixWord ++ tailWord_1863442) baseStart_1863442 baseEnd_1863442 := by
    simpa [prefixWord, tailWord_1863442, baseEnd_1863442] using wordTrace_append hprefix tailTrace_1863442
  have hstable : (prefixWord ++ tailWord_1863442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863442).length < 2 ^ (prefixWord ++ tailWord_1863442).sum := by decide
  have hdescent : baseEnd_1863442 < baseStart_1863442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863487 : List Nat := [1, 1, 2, 2, 6, 2, 1, 1, 3, 3]
def baseStart_1863487 : Nat := 118140960795 + 1863487 * 2 ^ 59
def prefixEnd_1863487 : Nat := 4983230072969 + 3 ^ 40 * 1863487 * 2
def baseEnd_1863487 : Nat := 637909682936703888161657

theorem tailTrace_1863487 : CollatzResearch.WordTrace tailWord_1863487 prefixEnd_1863487 637909682936703888161657 := by
  unfold tailWord_1863487
  simp only [CollatzResearch.WordTrace]
  refine ⟨67966954599912332086876715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45311303066608221391251143 67966954599912332086876715)
  ·
    refine ⟨101950431899868498130315073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67966954599912332086876715 101950431899868498130315073)
    ·
      refine ⟨76462823924901373597736305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101950431899868498130315073 76462823924901373597736305)
      ·
        refine ⟨57347117943676030198302229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76462823924901373597736305 57347117943676030198302229)
        ·
          refine ⟨2688146153609813915545417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 57347117943676030198302229 2688146153609813915545417)
          ·
            refine ⟨2016109615207360436659063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2688146153609813915545417 2016109615207360436659063)
            ·
              refine ⟨3024164422811040654988595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2016109615207360436659063 3024164422811040654988595)
              ·
                refine ⟨4536246634216560982482893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3024164422811040654988595 4536246634216560982482893)
                ·
                  refine ⟨1701092487831210368431085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4536246634216560982482893 1701092487831210368431085)
                  ·
                    refine ⟨637909682936703888161657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1701092487831210368431085 637909682936703888161657)
                    ·
                      rfl

theorem cell22_1863487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 3, 3].length) (baseStart_1863487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863487 prefixEnd_1863487 := by exact prefixLift 1863487
  have htrace : WordTrace (prefixWord ++ tailWord_1863487) baseStart_1863487 baseEnd_1863487 := by
    simpa [prefixWord, tailWord_1863487, baseEnd_1863487] using wordTrace_append hprefix tailTrace_1863487
  have hstable : (prefixWord ++ tailWord_1863487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863487).length < 2 ^ (prefixWord ++ tailWord_1863487).sum := by decide
  have hdescent : baseEnd_1863487 < baseStart_1863487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863500 : List Nat := [2, 2, 1, 3, 4, 1, 1, 3, 5]
def baseStart_1863500 : Nat := 118140960795 + 1863500 * 2 ^ 59
def prefixEnd_1863500 : Nat := 4983230072969 + 3 ^ 40 * 1863500 * 2
def baseEnd_1863500 : Nat := 212638044367458729195539

theorem tailTrace_1863500 : CollatzResearch.WordTrace tailWord_1863500 prefixEnd_1863500 212638044367458729195539 := by
  unfold tailWord_1863500
  simp only [CollatzResearch.WordTrace]
  refine ⟨33983714374432617653549977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45311619165910156871399969 33983714374432617653549977)
  ·
    refine ⟨25487785780824463240162483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33983714374432617653549977 25487785780824463240162483)
    ·
      refine ⟨38231678671236694860243725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25487785780824463240162483 38231678671236694860243725)
      ·
        refine ⟨14336879501713760572591397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38231678671236694860243725 14336879501713760572591397)
        ·
          refine ⟨2688164906571330107360887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14336879501713760572591397 2688164906571330107360887)
          ·
            refine ⟨4032247359856995161041331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2688164906571330107360887 4032247359856995161041331)
            ·
              refine ⟨6048371039785492741561997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4032247359856995161041331 6048371039785492741561997)
              ·
                refine ⟨2268139139919559778085749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6048371039785492741561997 2268139139919559778085749)
                ·
                  refine ⟨212638044367458729195539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2268139139919559778085749 212638044367458729195539)
                  ·
                    rfl

theorem cell22_1863500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 5].length) (baseStart_1863500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863500 prefixEnd_1863500 := by exact prefixLift 1863500
  have htrace : WordTrace (prefixWord ++ tailWord_1863500) baseStart_1863500 baseEnd_1863500 := by
    simpa [prefixWord, tailWord_1863500, baseEnd_1863500] using wordTrace_append hprefix tailTrace_1863500
  have hstable : (prefixWord ++ tailWord_1863500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863500).length < 2 ^ (prefixWord ++ tailWord_1863500).sum := by decide
  have hdescent : baseEnd_1863500 < baseStart_1863500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863513 : List Nat := [1, 2, 1, 2, 2, 3, 3, 1, 3, 4]
def baseStart_1863513 : Nat := 118140960795 + 1863513 * 2 ^ 59
def prefixEnd_1863513 : Nat := 4983230072969 + 3 ^ 40 * 1863513 * 2
def baseEnd_1863513 : Nat := 637918583268048487011577

theorem tailTrace_1863513 : CollatzResearch.WordTrace tailWord_1863513 prefixEnd_1863513 637918583268048487011577 := by
  unfold tailWord_1863513
  simp only [CollatzResearch.WordTrace]
  refine ⟨67967902897818138527323193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45311935265212092351548795 67967902897818138527323193)
  ·
    refine ⟨50975927173363603895492395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67967902897818138527323193 50975927173363603895492395)
    ·
      refine ⟨76463890760045405843238593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50975927173363603895492395 76463890760045405843238593)
      ·
        refine ⟨57347918070034054382428945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76463890760045405843238593 57347918070034054382428945)
        ·
          refine ⟨43010938552525540786821709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57347918070034054382428945 43010938552525540786821709)
          ·
            refine ⟨16129101957197077795058141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43010938552525540786821709 16129101957197077795058141)
            ·
              refine ⟨6048413233948904173146803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16129101957197077795058141 6048413233948904173146803)
              ·
                refine ⟨9072619850923356259720205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6048413233948904173146803 9072619850923356259720205)
                ·
                  refine ⟨3402232444096258597395077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9072619850923356259720205 3402232444096258597395077)
                  ·
                    refine ⟨637918583268048487011577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3402232444096258597395077 637918583268048487011577)
                    ·
                      rfl

theorem cell22_1863513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 4].length) (baseStart_1863513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863513 prefixEnd_1863513 := by exact prefixLift 1863513
  have htrace : WordTrace (prefixWord ++ tailWord_1863513) baseStart_1863513 baseEnd_1863513 := by
    simpa [prefixWord, tailWord_1863513, baseEnd_1863513] using wordTrace_append hprefix tailTrace_1863513
  have hstable : (prefixWord ++ tailWord_1863513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863513).length < 2 ^ (prefixWord ++ tailWord_1863513).sum := by decide
  have hdescent : baseEnd_1863513 < baseStart_1863513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863545 : List Nat := [1, 2, 1, 3, 2, 2, 3, 4, 4]
def baseStart_1863545 : Nat := 118140960795 + 1863545 * 2 ^ 59
def prefixEnd_1863545 : Nat := 4983230072969 + 3 ^ 40 * 1863545 * 2
def baseEnd_1863545 : Nat := 212643179174003690070493

theorem tailTrace_1863545 : CollatzResearch.WordTrace tailWord_1863545 prefixEnd_1863545 212643179174003690070493 := by
  unfold tailWord_1863545
  simp only [CollatzResearch.WordTrace]
  refine ⟨67969070033702207992488089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45312713355801471994992059 67969070033702207992488089)
  ·
    refine ⟨50976802525276655994366067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67969070033702207992488089 50976802525276655994366067)
    ·
      refine ⟨76465203787914983991549101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50976802525276655994366067 76465203787914983991549101)
      ·
        refine ⟨28674451420468118996830913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76465203787914983991549101 28674451420468118996830913)
        ·
          refine ⟨21505838565351089247623185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28674451420468118996830913 21505838565351089247623185)
          ·
            refine ⟨16129378924013316935717389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21505838565351089247623185 16129378924013316935717389)
            ·
              refine ⟨6048517096504993850894021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16129378924013316935717389 6048517096504993850894021)
              ·
                refine ⟨1134096955594686347042629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6048517096504993850894021 1134096955594686347042629)
                ·
                  refine ⟨212643179174003690070493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1134096955594686347042629 212643179174003690070493)
                  ·
                    rfl

theorem cell22_1863545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 4, 4].length) (baseStart_1863545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863545 prefixEnd_1863545 := by exact prefixLift 1863545
  have htrace : WordTrace (prefixWord ++ tailWord_1863545) baseStart_1863545 baseEnd_1863545 := by
    simpa [prefixWord, tailWord_1863545, baseEnd_1863545] using wordTrace_append hprefix tailTrace_1863545
  have hstable : (prefixWord ++ tailWord_1863545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863545).length < 2 ^ (prefixWord ++ tailWord_1863545).sum := by decide
  have hdescent : baseEnd_1863545 < baseStart_1863545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863575 : List Nat := [1, 1, 3, 3, 1, 3, 3, 1, 2, 4]
def baseStart_1863575 : Nat := 118140960795 + 1863575 * 2 ^ 59
def prefixEnd_1863575 : Nat := 4983230072969 + 3 ^ 40 * 1863575 * 2
def baseEnd_1863575 : Nat := 637939807135100991961387

theorem tailTrace_1863575 : CollatzResearch.WordTrace tailWord_1863575 prefixEnd_1863575 637939807135100991961387 := by
  unfold tailWord_1863575
  simp only [CollatzResearch.WordTrace]
  refine ⟨67970164223593523116080179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45313442815729015410720119 67970164223593523116080179)
  ·
    refine ⟨101955246335390284674120269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67970164223593523116080179 101955246335390284674120269)
    ·
      refine ⟨38233217375771356752795101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101955246335390284674120269 38233217375771356752795101)
      ·
        refine ⟨14337456515914258782298163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38233217375771356752795101 14337456515914258782298163)
        ·
          refine ⟨21506184773871388173447245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14337456515914258782298163 21506184773871388173447245)
          ·
            refine ⟨8064819290201770565042717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21506184773871388173447245 8064819290201770565042717)
            ·
              refine ⟨3024307233825663961891019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8064819290201770565042717 3024307233825663961891019)
              ·
                refine ⟨4536460850738495942836529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3024307233825663961891019 4536460850738495942836529)
                ·
                  refine ⟨3402345638053871957127397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4536460850738495942836529 3402345638053871957127397)
                  ·
                    refine ⟨637939807135100991961387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3402345638053871957127397 637939807135100991961387)
                    ·
                      rfl

theorem cell22_1863575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 4].length) (baseStart_1863575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863575 prefixEnd_1863575 := by exact prefixLift 1863575
  have htrace : WordTrace (prefixWord ++ tailWord_1863575) baseStart_1863575 baseEnd_1863575 := by
    simpa [prefixWord, tailWord_1863575, baseEnd_1863575] using wordTrace_append hprefix tailTrace_1863575
  have hstable : (prefixWord ++ tailWord_1863575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863575).length < 2 ^ (prefixWord ++ tailWord_1863575).sum := by decide
  have hdescent : baseEnd_1863575 < baseStart_1863575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863633 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 4, 5]
def baseStart_1863633 : Nat := 118140960795 + 1863633 * 2 ^ 59
def prefixEnd_1863633 : Nat := 4983230072969 + 3 ^ 40 * 1863633 * 2
def baseEnd_1863633 : Nat := 637959661720408174011209

theorem tailTrace_1863633 : CollatzResearch.WordTrace tailWord_1863633 prefixEnd_1863633 637959661720408174011209 := by
  unfold tailWord_1863633
  simp only [CollatzResearch.WordTrace]
  refine ⟨67972279657383399021691553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45314853104922266014461035 67972279657383399021691553)
  ·
    refine ⟨50979209743037549266268665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67972279657383399021691553 50979209743037549266268665)
    ·
      refine ⟨38234407307278161949701499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50979209743037549266268665 38234407307278161949701499)
      ·
        refine ⟨57351610960917242924552249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38234407307278161949701499 57351610960917242924552249)
        ·
          refine ⟨43013708220687932193414187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57351610960917242924552249 43013708220687932193414187)
          ·
            refine ⟨64520562331031898290121281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43013708220687932193414187 64520562331031898290121281)
            ·
              refine ⟨48390421748273923717590961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64520562331031898290121281 48390421748273923717590961)
              ·
                refine ⟨36292816311205442788193221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48390421748273923717590961 36292816311205442788193221)
                ·
                  refine ⟨6804903058351020522786229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36292816311205442788193221 6804903058351020522786229)
                  ·
                    refine ⟨637959661720408174011209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6804903058351020522786229 637959661720408174011209)
                    ·
                      rfl

theorem cell22_1863633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_1863633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863633 prefixEnd_1863633 := by exact prefixLift 1863633
  have htrace : WordTrace (prefixWord ++ tailWord_1863633) baseStart_1863633 baseEnd_1863633 := by
    simpa [prefixWord, tailWord_1863633, baseEnd_1863633] using wordTrace_append hprefix tailTrace_1863633
  have hstable : (prefixWord ++ tailWord_1863633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863633).length < 2 ^ (prefixWord ++ tailWord_1863633).sum := by decide
  have hdescent : baseEnd_1863633 < baseStart_1863633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863770 : List Nat := [3, 1, 1, 2, 1, 1, 5, 1, 7]
def baseStart_1863770 : Nat := 118140960795 + 1863770 * 2 ^ 59
def prefixEnd_1863770 : Nat := 4983230072969 + 3 ^ 40 * 1863770 * 2
def baseEnd_1863770 : Nat := 212668853206728494445263

theorem tailTrace_1863770 : CollatzResearch.WordTrace tailWord_1863770 prefixEnd_1863770 212668853206728494445263 := by
  unfold tailWord_1863770
  simp only [CollatzResearch.WordTrace]
  refine ⟨16994319114471767854857191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45318184305258047612952509 16994319114471767854857191)
  ·
    refine ⟨25491478671707651782285787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16994319114471767854857191 25491478671707651782285787)
    ·
      refine ⟨38237218007561477673428681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25491478671707651782285787 38237218007561477673428681)
      ·
        refine ⟨28677913505671108255071511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38237218007561477673428681 28677913505671108255071511)
        ·
          refine ⟨43016870258506662382607267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28677913505671108255071511 43016870258506662382607267)
          ·
            refine ⟨64525305387759993573910901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43016870258506662382607267 64525305387759993573910901)
            ·
              refine ⟨6049247380102499397554147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64525305387759993573910901 6049247380102499397554147)
              ·
                refine ⟨9073871070153749096331221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6049247380102499397554147 9073871070153749096331221)
                ·
                  refine ⟨212668853206728494445263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9073871070153749096331221 212668853206728494445263)
                  ·
                    rfl

theorem cell22_1863770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 7].length) (baseStart_1863770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863770 prefixEnd_1863770 := by exact prefixLift 1863770
  have htrace : WordTrace (prefixWord ++ tailWord_1863770) baseStart_1863770 baseEnd_1863770 := by
    simpa [prefixWord, tailWord_1863770, baseEnd_1863770] using wordTrace_append hprefix tailTrace_1863770
  have hstable : (prefixWord ++ tailWord_1863770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863770).length < 2 ^ (prefixWord ++ tailWord_1863770).sum := by decide
  have hdescent : baseEnd_1863770 < baseStart_1863770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863785 : List Nat := [1, 2, 1, 1, 1, 5, 1, 3, 2, 5]
def baseStart_1863785 : Nat := 118140960795 + 1863785 * 2 ^ 59
def prefixEnd_1863785 : Nat := 4983230072969 + 3 ^ 40 * 1863785 * 2
def baseEnd_1863785 : Nat := 638011694426730444210743

theorem tailTrace_1863785 : CollatzResearch.WordTrace tailWord_1863785 prefixEnd_1863785 638011694426730444210743 := by
  unfold tailWord_1863785
  simp only [CollatzResearch.WordTrace]
  refine ⟨67977823552832728981224809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45318549035221819320816539 67977823552832728981224809)
  ·
    refine ⟨50983367664624546735918607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67977823552832728981224809 50983367664624546735918607)
    ·
      refine ⟨76475051496936820103877911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50983367664624546735918607 76475051496936820103877911)
      ·
        refine ⟨114712577245405230155816867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76475051496936820103877911 114712577245405230155816867)
        ·
          refine ⟨172068865868107845233725301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114712577245405230155816867 172068865868107845233725301)
          ·
            refine ⟨16131456175135110490661747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 172068865868107845233725301 16131456175135110490661747)
            ·
              refine ⟨24197184262702665735992621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16131456175135110490661747 24197184262702665735992621)
              ·
                refine ⟨9073944098513499650997233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24197184262702665735992621 9073944098513499650997233)
                ·
                  refine ⟨6805458073885124738247925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9073944098513499650997233 6805458073885124738247925)
                  ·
                    refine ⟨638011694426730444210743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6805458073885124738247925 638011694426730444210743)
                    ·
                      rfl

theorem cell22_1863785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 5].length) (baseStart_1863785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863785 prefixEnd_1863785 := by exact prefixLift 1863785
  have htrace : WordTrace (prefixWord ++ tailWord_1863785) baseStart_1863785 baseEnd_1863785 := by
    simpa [prefixWord, tailWord_1863785, baseEnd_1863785] using wordTrace_append hprefix tailTrace_1863785
  have hstable : (prefixWord ++ tailWord_1863785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863785).length < 2 ^ (prefixWord ++ tailWord_1863785).sum := by decide
  have hdescent : baseEnd_1863785 < baseStart_1863785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863815 : List Nat := [1, 1, 4, 2, 1, 1, 2, 2, 8]
def baseStart_1863815 : Nat := 118140960795 + 1863815 * 2 ^ 59
def prefixEnd_1863815 : Nat := 4983230072969 + 3 ^ 40 * 1863815 * 2
def baseEnd_1863815 : Nat := 212673988013273455320217

theorem tailTrace_1863815 : CollatzResearch.WordTrace tailWord_1863815 prefixEnd_1863815 212673988013273455320217 := by
  unfold tailWord_1863815
  simp only [CollatzResearch.WordTrace]
  refine ⟨67978917742724044104816899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45319278495149362736544599 67978917742724044104816899)
  ·
    refine ⟨101968376614086066157225349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67978917742724044104816899 101968376614086066157225349)
    ·
      refine ⟨19119070615141137404479753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101968376614086066157225349 19119070615141137404479753)
      ·
        refine ⟨14339302961355853053359815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19119070615141137404479753 14339302961355853053359815)
        ·
          refine ⟨21508954442033779580039723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14339302961355853053359815 21508954442033779580039723)
          ·
            refine ⟨32263431663050669370059585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21508954442033779580039723 32263431663050669370059585)
            ·
              refine ⟨24197573747288002027544689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32263431663050669370059585 24197573747288002027544689)
              ·
                refine ⟨18148180310466001520658517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24197573747288002027544689 18148180310466001520658517)
                ·
                  refine ⟨212673988013273455320217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18148180310466001520658517 212673988013273455320217)
                  ·
                    rfl

theorem cell22_1863815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 8].length) (baseStart_1863815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863815 prefixEnd_1863815 := by exact prefixLift 1863815
  have htrace : WordTrace (prefixWord ++ tailWord_1863815) baseStart_1863815 baseEnd_1863815 := by
    simpa [prefixWord, tailWord_1863815, baseEnd_1863815] using wordTrace_append hprefix tailTrace_1863815
  have hstable : (prefixWord ++ tailWord_1863815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863815).length < 2 ^ (prefixWord ++ tailWord_1863815).sum := by decide
  have hdescent : baseEnd_1863815 < baseStart_1863815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863817 : List Nat := [1, 2, 1, 1, 4, 2, 1, 5, 1, 4]
def baseStart_1863817 : Nat := 118140960795 + 1863817 * 2 ^ 59
def prefixEnd_1863817 : Nat := 4983230072969 + 3 ^ 40 * 1863817 * 2
def baseEnd_1863817 : Nat := 638022648680693027410645

theorem tailTrace_1863817 : CollatzResearch.WordTrace tailWord_1863817 prefixEnd_1863817 638022648680693027410645 := by
  unfold tailWord_1863817
  simp only [CollatzResearch.WordTrace]
  refine ⟨67978990688716798446389705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45319327125811198964259803 67978990688716798446389705)
  ·
    refine ⟨50984243016537598834792279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67978990688716798446389705 50984243016537598834792279)
    ·
      refine ⟨76476364524806398252188419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50984243016537598834792279 76476364524806398252188419)
      ·
        refine ⟨114714546787209597378282629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76476364524806398252188419 114714546787209597378282629)
        ·
          refine ⟨21508977522601799508427993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114714546787209597378282629 21508977522601799508427993)
          ·
            refine ⟨16131733141951349631320995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21508977522601799508427993 16131733141951349631320995)
            ·
              refine ⟨24197599712927024446981493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16131733141951349631320995 24197599712927024446981493)
              ·
                refine ⟨2268524973086908541904515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24197599712927024446981493 2268524973086908541904515)
                ·
                  refine ⟨3402787459630362812856773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2268524973086908541904515 3402787459630362812856773)
                  ·
                    refine ⟨638022648680693027410645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3402787459630362812856773 638022648680693027410645)
                    ·
                      rfl

theorem cell22_1863817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 4].length) (baseStart_1863817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863817 prefixEnd_1863817 := by exact prefixLift 1863817
  have htrace : WordTrace (prefixWord ++ tailWord_1863817) baseStart_1863817 baseEnd_1863817 := by
    simpa [prefixWord, tailWord_1863817, baseEnd_1863817] using wordTrace_append hprefix tailTrace_1863817
  have hstable : (prefixWord ++ tailWord_1863817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863817).length < 2 ^ (prefixWord ++ tailWord_1863817).sum := by decide
  have hdescent : baseEnd_1863817 < baseStart_1863817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863838 : List Nat := [4, 3, 1, 1, 3, 2, 2, 1, 5]
def baseStart_1863838 : Nat := 118140960795 + 1863838 * 2 ^ 59
def prefixEnd_1863838 : Nat := 4983230072969 + 3 ^ 40 * 1863838 * 2
def baseEnd_1863838 : Nat := 212676612469951990878527

theorem tailTrace_1863838 : CollatzResearch.WordTrace tailWord_1863838 prefixEnd_1863838 212676612469951990878527 := by
  unfold tailWord_1863838
  simp only [CollatzResearch.WordTrace]
  refine ⟨8497469577705089879113021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45319837747760479355269445 8497469577705089879113021)
  ·
    refine ⟨3186551091639408704667383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8497469577705089879113021 3186551091639408704667383)
    ·
      refine ⟨4779826637459113057001075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3186551091639408704667383 4779826637459113057001075)
      ·
        refine ⟨7169739956188669585501613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4779826637459113057001075 7169739956188669585501613)
        ·
          refine ⟨2688652483570751094563105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7169739956188669585501613 2688652483570751094563105)
          ·
            refine ⟨2016489362678063320922329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2688652483570751094563105 2016489362678063320922329)
            ·
              refine ⟨1512367022008547490691747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2016489362678063320922329 1512367022008547490691747)
              ·
                refine ⟨2268550533012821236037621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1512367022008547490691747 2268550533012821236037621)
                ·
                  refine ⟨212676612469951990878527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2268550533012821236037621 212676612469951990878527)
                  ·
                    rfl

theorem cell22_1863838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_1863838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863838 prefixEnd_1863838 := by exact prefixLift 1863838
  have htrace : WordTrace (prefixWord ++ tailWord_1863838) baseStart_1863838 baseEnd_1863838 := by
    simpa [prefixWord, tailWord_1863838, baseEnd_1863838] using wordTrace_append hprefix tailTrace_1863838
  have hstable : (prefixWord ++ tailWord_1863838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863838).length < 2 ^ (prefixWord ++ tailWord_1863838).sum := by decide
  have hdescent : baseEnd_1863838 < baseStart_1863838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863875 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 4, 7]
def baseStart_1863875 : Nat := 118140960795 + 1863875 * 2 ^ 59
def prefixEnd_1863875 : Nat := 4983230072969 + 3 ^ 40 * 1863875 * 2
def baseEnd_1863875 : Nat := 638042503266000209460467

theorem tailTrace_1863875 : CollatzResearch.WordTrace tailWord_1863875 prefixEnd_1863875 638042503266000209460467 := by
  unfold tailWord_1863875
  simp only [CollatzResearch.WordTrace]
  refine ⟨67981106122506674352001079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45320737415004449568000719 67981106122506674352001079)
  ·
    refine ⟨101971659183760011528001619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67981106122506674352001079 101971659183760011528001619)
    ·
      refine ⟨152957488775640017292002429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101971659183760011528001619 152957488775640017292002429)
      ·
        refine ⟨57359058290865006484500911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152957488775640017292002429 57359058290865006484500911)
        ·
          refine ⟨86038587436297509726751367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57359058290865006484500911 86038587436297509726751367)
          ·
            refine ⟨129057881154446264590127051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86038587436297509726751367 129057881154446264590127051)
            ·
              refine ⟨193586821731669396885190577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129057881154446264590127051 193586821731669396885190577)
              ·
                refine ⟨145190116298752047663892933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193586821731669396885190577 145190116298752047663892933)
                ·
                  refine ⟨27223146806016008936979925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145190116298752047663892933 27223146806016008936979925)
                  ·
                    refine ⟨638042503266000209460467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27223146806016008936979925 638042503266000209460467)
                    ·
                      rfl

theorem cell22_1863875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 7].length) (baseStart_1863875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863875 prefixEnd_1863875 := by exact prefixLift 1863875
  have htrace : WordTrace (prefixWord ++ tailWord_1863875) baseStart_1863875 baseEnd_1863875 := by
    simpa [prefixWord, tailWord_1863875, baseEnd_1863875] using wordTrace_append hprefix tailTrace_1863875
  have hstable : (prefixWord ++ tailWord_1863875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863875).length < 2 ^ (prefixWord ++ tailWord_1863875).sum := by decide
  have hdescent : baseEnd_1863875 < baseStart_1863875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863909 : List Nat := [1, 3, 1, 4, 2, 1, 1, 1, 5, 3]
def baseStart_1863909 : Nat := 118140960795 + 1863909 * 2 ^ 59
def prefixEnd_1863909 : Nat := 4983230072969 + 3 ^ 40 * 1863909 * 2
def baseEnd_1863909 : Nat := 638054142160835454110363

theorem tailTrace_1863909 : CollatzResearch.WordTrace tailWord_1863909 prefixEnd_1863909 638054142160835454110363 := by
  unfold tailWord_1863909
  simp only [CollatzResearch.WordTrace]
  refine ⟨67982346204383498158738781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45321564136255665439159187 67982346204383498158738781)
  ·
    refine ⟨25493379826643811809527043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67982346204383498158738781 25493379826643811809527043)
    ·
      refine ⟨38240069739965717714290565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25493379826643811809527043 38240069739965717714290565)
      ·
        refine ⟨7170013076243572071429481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38240069739965717714290565 7170013076243572071429481)
        ·
          refine ⟨5377509807182679053572111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7170013076243572071429481 5377509807182679053572111)
          ·
            refine ⟨8066264710774018580358167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5377509807182679053572111 8066264710774018580358167)
            ·
              refine ⟨12099397066161027870537251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8066264710774018580358167 12099397066161027870537251)
              ·
                refine ⟨18149095599241541805805877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12099397066161027870537251 18149095599241541805805877)
                ·
                  refine ⟨1701477712428894544294301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18149095599241541805805877 1701477712428894544294301)
                  ·
                    refine ⟨638054142160835454110363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1701477712428894544294301 638054142160835454110363)
                    ·
                      rfl

theorem cell22_1863909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 5, 3].length) (baseStart_1863909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863909 prefixEnd_1863909 := by exact prefixLift 1863909
  have htrace : WordTrace (prefixWord ++ tailWord_1863909) baseStart_1863909 baseEnd_1863909 := by
    simpa [prefixWord, tailWord_1863909, baseEnd_1863909] using wordTrace_append hprefix tailTrace_1863909
  have hstable : (prefixWord ++ tailWord_1863909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863909).length < 2 ^ (prefixWord ++ tailWord_1863909).sum := by decide
  have hdescent : baseEnd_1863909 < baseStart_1863909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863937 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 4, 5]
def baseStart_1863937 : Nat := 118140960795 + 1863937 * 2 ^ 59
def prefixEnd_1863937 : Nat := 4983230072969 + 3 ^ 40 * 1863937 * 2
def baseEnd_1863937 : Nat := 638063727133052714410277

theorem tailTrace_1863937 : CollatzResearch.WordTrace tailWord_1863937 prefixEnd_1863937 638063727133052714410277 := by
  unfold tailWord_1863937
  simp only [CollatzResearch.WordTrace]
  refine ⟨67983367448282058940758065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45322244965521372627172043 67983367448282058940758065)
  ·
    refine ⟨50987525586211544205568549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67983367448282058940758065 50987525586211544205568549)
    ·
      refine ⟨9560161047414664538544103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50987525586211544205568549 9560161047414664538544103)
      ·
        refine ⟨14340241571121996807816155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9560161047414664538544103 14340241571121996807816155)
        ·
          refine ⟨21510362356682995211724233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14340241571121996807816155 21510362356682995211724233)
          ·
            refine ⟨16132771767512246408793175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21510362356682995211724233 16132771767512246408793175)
            ·
              refine ⟨24199157651268369613189763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16132771767512246408793175 24199157651268369613189763)
              ·
                refine ⟨36298736476902554419784645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24199157651268369613189763 36298736476902554419784645)
                ·
                  refine ⟨6806013089419228953709621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36298736476902554419784645 6806013089419228953709621)
                  ·
                    refine ⟨638063727133052714410277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6806013089419228953709621 638063727133052714410277)
                    ·
                      rfl

theorem cell22_1863937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_1863937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863937 prefixEnd_1863937 := by exact prefixLift 1863937
  have htrace : WordTrace (prefixWord ++ tailWord_1863937) baseStart_1863937 baseEnd_1863937 := by
    simpa [prefixWord, tailWord_1863937, baseEnd_1863937] using wordTrace_append hprefix tailTrace_1863937
  have hstable : (prefixWord ++ tailWord_1863937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863937).length < 2 ^ (prefixWord ++ tailWord_1863937).sum := by decide
  have hdescent : baseEnd_1863937 < baseStart_1863937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863943 : List Nat := [1, 1, 4, 5, 1, 1, 2, 1, 3, 3]
def baseStart_1863943 : Nat := 118140960795 + 1863943 * 2 ^ 59
def prefixEnd_1863943 : Nat := 4983230072969 + 3 ^ 40 * 1863943 * 2
def baseEnd_1863943 : Nat := 638065781055670698760259

theorem tailTrace_1863943 : CollatzResearch.WordTrace tailWord_1863943 prefixEnd_1863943 638065781055670698760259 := by
  unfold tailWord_1863943
  simp only [CollatzResearch.WordTrace]
  refine ⟨67983586286260321965476483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45322390857506881310317655 67983586286260321965476483)
  ·
    refine ⟨101975379429390482948214725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67983586286260321965476483 101975379429390482948214725)
    ·
      refine ⟨19120383643010715552790261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101975379429390482948214725 19120383643010715552790261)
      ·
        refine ⟨1792535966532254583074087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19120383643010715552790261 1792535966532254583074087)
        ·
          refine ⟨2688803949798381874611131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1792535966532254583074087 2688803949798381874611131)
          ·
            refine ⟨4033205924697572811916697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2688803949798381874611131 4033205924697572811916697)
            ·
              refine ⟨3024904443523179608937523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4033205924697572811916697 3024904443523179608937523)
              ·
                refine ⟨4537356665284769413406285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3024904443523179608937523 4537356665284769413406285)
                ·
                  refine ⟨1701508749481788530027357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4537356665284769413406285 1701508749481788530027357)
                  ·
                    refine ⟨638065781055670698760259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1701508749481788530027357 638065781055670698760259)
                    ·
                      rfl

theorem cell22_1863943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_1863943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863943 prefixEnd_1863943 := by exact prefixLift 1863943
  have htrace : WordTrace (prefixWord ++ tailWord_1863943) baseStart_1863943 baseEnd_1863943 := by
    simpa [prefixWord, tailWord_1863943, baseEnd_1863943] using wordTrace_append hprefix tailTrace_1863943
  have hstable : (prefixWord ++ tailWord_1863943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863943).length < 2 ^ (prefixWord ++ tailWord_1863943).sum := by decide
  have hdescent : baseEnd_1863943 < baseStart_1863943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863969 : List Nat := [1, 2, 3, 2, 1, 1, 3, 4, 1, 4]
def baseStart_1863969 : Nat := 118140960795 + 1863969 * 2 ^ 59
def prefixEnd_1863969 : Nat := 4983230072969 + 3 ^ 40 * 1863969 * 2
def baseEnd_1863969 : Nat := 638074681387015297610179

theorem tailTrace_1863969 : CollatzResearch.WordTrace tailWord_1863969 prefixEnd_1863969 638074681387015297610179 := by
  unfold tailWord_1863969
  simp only [CollatzResearch.WordTrace]
  refine ⟨67984534584166128405922961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45323023056110752270615307 67984534584166128405922961)
  ·
    refine ⟨50988400938124596304442221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67984534584166128405922961 50988400938124596304442221)
    ·
      refine ⟨19120650351796723614165833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50988400938124596304442221 19120650351796723614165833)
      ·
        refine ⟨14340487763847542710624375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19120650351796723614165833 14340487763847542710624375)
        ·
          refine ⟨21510731645771314065936563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14340487763847542710624375 21510731645771314065936563)
          ·
            refine ⟨32266097468656971098904845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21510731645771314065936563 32266097468656971098904845)
            ·
              refine ⟨12099786550746364162089317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32266097468656971098904845 12099786550746364162089317)
              ·
                refine ⟨2268709978264943280391747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12099786550746364162089317 2268709978264943280391747)
                ·
                  refine ⟨3403064967397414920587621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2268709978264943280391747 3403064967397414920587621)
                  ·
                    refine ⟨638074681387015297610179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3403064967397414920587621 638074681387015297610179)
                    ·
                      rfl

theorem cell22_1863969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_1863969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863969 prefixEnd_1863969 := by exact prefixLift 1863969
  have htrace : WordTrace (prefixWord ++ tailWord_1863969) baseStart_1863969 baseEnd_1863969 := by
    simpa [prefixWord, tailWord_1863969, baseEnd_1863969] using wordTrace_append hprefix tailTrace_1863969
  have hstable : (prefixWord ++ tailWord_1863969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863969).length < 2 ^ (prefixWord ++ tailWord_1863969).sum := by decide
  have hdescent : baseEnd_1863969 < baseStart_1863969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863984 : List Nat := [2, 1, 1, 1, 2, 2, 2, 7, 4]
def baseStart_1863984 : Nat := 118140960795 + 1863984 * 2 ^ 59
def prefixEnd_1863984 : Nat := 4983230072969 + 3 ^ 40 * 1863984 * 2
def baseEnd_1863984 : Nat := 212693272064520086161711

theorem tailTrace_1863984 : CollatzResearch.WordTrace tailWord_1863984 prefixEnd_1863984 212693272064520086161711 := by
  unfold tailWord_1863984
  simp only [CollatzResearch.WordTrace]
  refine ⟨33992540839555892983859503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45323387786074523978479337 33992540839555892983859503)
  ·
    refine ⟨50988811259333839475789255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33992540839555892983859503 50988811259333839475789255)
    ·
      refine ⟨76483216889000759213683883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50988811259333839475789255 76483216889000759213683883)
      ·
        refine ⟨114724825333501138820525825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76483216889000759213683883 114724825333501138820525825)
        ·
          refine ⟨86043619000125854115394369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114724825333501138820525825 86043619000125854115394369)
          ·
            refine ⟨64532714250094390586545777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86043619000125854115394369 64532714250094390586545777)
            ·
              refine ⟨48399535687570792939909333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64532714250094390586545777 48399535687570792939909333)
              ·
                refine ⟨1134364117677440459529125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 48399535687570792939909333 1134364117677440459529125)
                ·
                  refine ⟨212693272064520086161711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1134364117677440459529125 212693272064520086161711)
                  ·
                    rfl

theorem cell22_1863984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 7, 4].length) (baseStart_1863984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863984 prefixEnd_1863984 := by exact prefixLift 1863984
  have htrace : WordTrace (prefixWord ++ tailWord_1863984) baseStart_1863984 baseEnd_1863984 := by
    simpa [prefixWord, tailWord_1863984, baseEnd_1863984] using wordTrace_append hprefix tailTrace_1863984
  have hstable : (prefixWord ++ tailWord_1863984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863984).length < 2 ^ (prefixWord ++ tailWord_1863984).sum := by decide
  have hdescent : baseEnd_1863984 < baseStart_1863984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863999 : List Nat := [1, 1, 2, 2, 4, 1, 1, 3, 4, 3]
def baseStart_1863999 : Nat := 118140960795 + 1863999 * 2 ^ 59
def prefixEnd_1863999 : Nat := 4983230072969 + 3 ^ 40 * 1863999 * 2
def baseEnd_1863999 : Nat := 638084951000105219360087

theorem tailTrace_1863999 : CollatzResearch.WordTrace tailWord_1863999 prefixEnd_1863999 638084951000105219360087 := by
  unfold tailWord_1863999
  simp only [CollatzResearch.WordTrace]
  refine ⟨67985628774057443529515051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45323752516038295686343367 67985628774057443529515051)
  ·
    refine ⟨101978443161086165294272577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67985628774057443529515051 101978443161086165294272577)
    ·
      refine ⟨76483832370814623970704433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101978443161086165294272577 76483832370814623970704433)
      ·
        refine ⟨57362874278110967978028325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76483832370814623970704433 57362874278110967978028325)
        ·
          refine ⟨10755538927145806495880311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57362874278110967978028325 10755538927145806495880311)
          ·
            refine ⟨16133308390718709743820467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10755538927145806495880311 16133308390718709743820467)
            ·
              refine ⟨24199962586078064615730701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16133308390718709743820467 24199962586078064615730701)
              ·
                refine ⟨9074985969779274230899013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24199962586078064615730701 9074985969779274230899013)
                ·
                  refine ⟨1701559869333613918293565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9074985969779274230899013 1701559869333613918293565)
                  ·
                    refine ⟨638084951000105219360087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1701559869333613918293565 638084951000105219360087)
                    ·
                      rfl

theorem cell22_1863999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 4, 3].length) (baseStart_1863999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1863999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1863999 prefixEnd_1863999 := by exact prefixLift 1863999
  have htrace : WordTrace (prefixWord ++ tailWord_1863999) baseStart_1863999 baseEnd_1863999 := by
    simpa [prefixWord, tailWord_1863999, baseEnd_1863999] using wordTrace_append hprefix tailTrace_1863999
  have hstable : (prefixWord ++ tailWord_1863999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863999).length < 2 ^ (prefixWord ++ tailWord_1863999).sum := by decide
  have hdescent : baseEnd_1863999 < baseStart_1863999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
