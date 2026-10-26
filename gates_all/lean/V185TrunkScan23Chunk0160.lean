import V185TrunkScan23Chunk0159

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_946177 : List Nat := [1, 2, 4, 1, 2, 1, 2, 1, 4, 5]
def baseStart_946177 : Nat := 118140960795 + 946177 * 2 ^ 59
def prefixEnd_946177 : Nat := 4983230072969 + 3 ^ 40 * 946177 * 2
def baseEnd_946177 : Nat := 161947861743083270612039

theorem tailTrace_946177 : CollatzResearch.WordTrace tailWord_946177 prefixEnd_946177 161947861743083270612039 := by
  unfold tailWord_946177
  simp only [CollatzResearch.WordTrace]
  refine ⟨34509910293169798011540785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23006606862113198674360523 34509910293169798011540785)
  ·
    refine ⟨25882432719877348508655589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34509910293169798011540785 25882432719877348508655589)
    ·
      refine ⟨4852956134977002845372923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25882432719877348508655589 4852956134977002845372923)
      ·
        refine ⟨7279434202465504268059385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4852956134977002845372923 7279434202465504268059385)
        ·
          refine ⟨5459575651849128201044539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7279434202465504268059385 5459575651849128201044539)
          ·
            refine ⟨8189363477773692301566809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5459575651849128201044539 8189363477773692301566809)
            ·
              refine ⟨6142022608330269226175107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8189363477773692301566809 6142022608330269226175107)
              ·
                refine ⟨9213033912495403839262661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6142022608330269226175107 9213033912495403839262661)
                ·
                  refine ⟨1727443858592888219861749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9213033912495403839262661 1727443858592888219861749)
                  ·
                    refine ⟨161947861743083270612039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1727443858592888219861749 161947861743083270612039)
                    ·
                      rfl

theorem cell23_946177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_946177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946177 prefixEnd_946177 := by exact prefixLift 946177
  have htrace : WordTrace (prefixWord ++ tailWord_946177) baseStart_946177 baseEnd_946177 := by
    simpa [prefixWord, tailWord_946177, baseEnd_946177] using wordTrace_append hprefix tailTrace_946177
  have hstable : (prefixWord ++ tailWord_946177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946177).length < 2 ^ (prefixWord ++ tailWord_946177).sum := by decide
  have hdescent : baseEnd_946177 < baseStart_946177 := by decide
  rcases family_descends (prefixWord ++ tailWord_946177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946215 : List Nat := [1, 1, 7, 1, 3, 1, 1, 3, 5]
def baseStart_946215 : Nat := 118140960795 + 946215 * 2 ^ 59
def prefixEnd_946215 : Nat := 4983230072969 + 3 ^ 40 * 946215 * 2
def baseEnd_946215 : Nat := 53984788610457851462327

theorem tailTrace_946215 : CollatzResearch.WordTrace tailWord_946215 prefixEnd_946215 53984788610457851462327 := by
  unfold tailWord_946215
  simp only [CollatzResearch.WordTrace]
  refine ⟨34511296267032130501424099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23007530844688087000949399 34511296267032130501424099)
  ·
    refine ⟨51766944400548195752136149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34511296267032130501424099 51766944400548195752136149)
    ·
      refine ⟨1213287759387848337940691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 51766944400548195752136149 1213287759387848337940691)
      ·
        refine ⟨1819931639081772506911037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1213287759387848337940691 1819931639081772506911037)
        ·
          refine ⟨682474364655664690091639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1819931639081772506911037 682474364655664690091639)
          ·
            refine ⟨1023711546983497035137459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 682474364655664690091639 1023711546983497035137459)
            ·
              refine ⟨1535567320475245552706189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1023711546983497035137459 1535567320475245552706189)
              ·
                refine ⟨575837745178217082264821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1535567320475245552706189 575837745178217082264821)
                ·
                  refine ⟨53984788610457851462327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 575837745178217082264821 53984788610457851462327)
                  ·
                    rfl

theorem cell23_946215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 3, 5].length) (baseStart_946215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946215 prefixEnd_946215 := by exact prefixLift 946215
  have htrace : WordTrace (prefixWord ++ tailWord_946215) baseStart_946215 baseEnd_946215 := by
    simpa [prefixWord, tailWord_946215, baseEnd_946215] using wordTrace_append hprefix tailTrace_946215
  have hstable : (prefixWord ++ tailWord_946215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946215).length < 2 ^ (prefixWord ++ tailWord_946215).sum := by decide
  have hdescent : baseEnd_946215 < baseStart_946215 := by decide
  rcases family_descends (prefixWord ++ tailWord_946215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946237 : List Nat := [1, 4, 1, 3, 1, 1, 1, 3, 8]
def baseStart_946237 : Nat := 118140960795 + 946237 * 2 ^ 59
def prefixEnd_946237 : Nat := 4983230072969 + 3 ^ 40 * 946237 * 2
def baseEnd_946237 : Nat := 53986043785391064120649

theorem tailTrace_946237 : CollatzResearch.WordTrace tailWord_946237 prefixEnd_946237 53986043785391064120649 := by
  unfold tailWord_946237
  simp only [CollatzResearch.WordTrace]
  refine ⟨34512098672952428258724965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23008065781968285505816643 34512098672952428258724965)
  ·
    refine ⟨6471018501178580298510931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34512098672952428258724965 6471018501178580298510931)
    ·
      refine ⟨9706527751767870447766397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6471018501178580298510931 9706527751767870447766397)
      ·
        refine ⟨3639947906912951417912399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9706527751767870447766397 3639947906912951417912399)
        ·
          refine ⟨5459921860369427126868599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3639947906912951417912399 5459921860369427126868599)
          ·
            refine ⟨8189882790554140690302899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5459921860369427126868599 8189882790554140690302899)
            ·
              refine ⟨12284824185831211035454349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8189882790554140690302899 12284824185831211035454349)
              ·
                refine ⟨4606809069686704138295381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12284824185831211035454349 4606809069686704138295381)
                ·
                  refine ⟨53986043785391064120649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4606809069686704138295381 53986043785391064120649)
                  ·
                    rfl

theorem cell23_946237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 8].length) (baseStart_946237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946237 prefixEnd_946237 := by exact prefixLift 946237
  have htrace : WordTrace (prefixWord ++ tailWord_946237) baseStart_946237 baseEnd_946237 := by
    simpa [prefixWord, tailWord_946237, baseEnd_946237] using wordTrace_append hprefix tailTrace_946237
  have hstable : (prefixWord ++ tailWord_946237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946237).length < 2 ^ (prefixWord ++ tailWord_946237).sum := by decide
  have hdescent : baseEnd_946237 < baseStart_946237 := by decide
  rcases family_descends (prefixWord ++ tailWord_946237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946241 : List Nat := [1, 2, 5, 1, 2, 1, 3, 1, 3, 4]
def baseStart_946241 : Nat := 118140960795 + 946241 * 2 ^ 59
def prefixEnd_946241 : Nat := 4983230072969 + 3 ^ 40 * 946241 * 2
def baseEnd_946241 : Nat := 161958815997045853811941

theorem tailTrace_946241 : CollatzResearch.WordTrace tailWord_946241 prefixEnd_946241 161958815997045853811941 := by
  unfold tailWord_946241
  simp only [CollatzResearch.WordTrace]
  refine ⟨34512244564937936941870577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23008163043291957961247051 34512244564937936941870577)
  ·
    refine ⟨25884183423703452706402933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34512244564937936941870577 25884183423703452706402933)
    ·
      refine ⟨2426642195972198691225275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25884183423703452706402933 2426642195972198691225275)
      ·
        refine ⟨3639963293958298036837913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2426642195972198691225275 3639963293958298036837913)
        ·
          refine ⟨2729972470468723527628435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3639963293958298036837913 2729972470468723527628435)
          ·
            refine ⟨4094958705703085291442653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2729972470468723527628435 4094958705703085291442653)
            ·
              refine ⟨1535609514638656984290995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4094958705703085291442653 1535609514638656984290995)
              ·
                refine ⟨2303414271957985476436493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1535609514638656984290995 2303414271957985476436493)
                ·
                  refine ⟨863780351984244553663685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2303414271957985476436493 863780351984244553663685)
                  ·
                    refine ⟨161958815997045853811941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 863780351984244553663685 161958815997045853811941)
                    ·
                      rfl

theorem cell23_946241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_946241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946241 prefixEnd_946241 := by exact prefixLift 946241
  have htrace : WordTrace (prefixWord ++ tailWord_946241) baseStart_946241 baseEnd_946241 := by
    simpa [prefixWord, tailWord_946241, baseEnd_946241] using wordTrace_append hprefix tailTrace_946241
  have hstable : (prefixWord ++ tailWord_946241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946241).length < 2 ^ (prefixWord ++ tailWord_946241).sum := by decide
  have hdescent : baseEnd_946241 < baseStart_946241 := by decide
  rcases family_descends (prefixWord ++ tailWord_946241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946254 : List Nat := [4, 1, 1, 1, 1, 5, 1, 3, 6]
def baseStart_946254 : Nat := 118140960795 + 946254 * 2 ^ 59
def prefixEnd_946254 : Nat := 4983230072969 + 3 ^ 40 * 946254 * 2
def baseEnd_946254 : Nat := 53987013693294001174807

theorem tailTrace_946254 : CollatzResearch.WordTrace tailWord_946254 prefixEnd_946254 53987013693294001174807 := by
  unfold tailWord_946254
  simp only [CollatzResearch.WordTrace]
  refine ⟨4314089839236355020261727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23008479142593893441395877 4314089839236355020261727)
  ·
    refine ⟨6471134758854532530392591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4314089839236355020261727 6471134758854532530392591)
    ·
      refine ⟨9706702138281798795588887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6471134758854532530392591 9706702138281798795588887)
      ·
        refine ⟨14560053207422698193383331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9706702138281798795588887 14560053207422698193383331)
        ·
          refine ⟨21840079811134047290074997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14560053207422698193383331 21840079811134047290074997)
          ·
            refine ⟨2047507482293816933444531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21840079811134047290074997 2047507482293816933444531)
            ·
              refine ⟨3071261223440725400166797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2047507482293816933444531 3071261223440725400166797)
              ·
                refine ⟨1151722958790272025062549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3071261223440725400166797 1151722958790272025062549)
                ·
                  refine ⟨53987013693294001174807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1151722958790272025062549 53987013693294001174807)
                  ·
                    rfl

theorem cell23_946254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 6].length) (baseStart_946254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946254 prefixEnd_946254 := by exact prefixLift 946254
  have htrace : WordTrace (prefixWord ++ tailWord_946254) baseStart_946254 baseEnd_946254 := by
    simpa [prefixWord, tailWord_946254, baseEnd_946254] using wordTrace_append hprefix tailTrace_946254
  have hstable : (prefixWord ++ tailWord_946254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946254).length < 2 ^ (prefixWord ++ tailWord_946254).sum := by decide
  have hdescent : baseEnd_946254 < baseStart_946254 := by decide
  rcases family_descends (prefixWord ++ tailWord_946254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946304 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 2, 6, 2]
def baseStart_946304 : Nat := 118140960795 + 946304 * 2 ^ 59
def prefixEnd_946304 : Nat := 4983230072969 + 3 ^ 40 * 946304 * 2
def baseEnd_946304 : Nat := 485908797272370814948033

theorem tailTrace_946304 : CollatzResearch.WordTrace tailWord_946304 prefixEnd_946304 485908797272370814948033 := by
  unfold tailWord_946304
  simp only [CollatzResearch.WordTrace]
  refine ⟨17257271181854849350706983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23009694909139799134275977 17257271181854849350706983)
  ·
    refine ⟨25885906772782274026060475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17257271181854849350706983 25885906772782274026060475)
    ·
      refine ⟨38828860159173411039090713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25885906772782274026060475 38828860159173411039090713)
      ·
        refine ⟨29121645119380058279318035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38828860159173411039090713 29121645119380058279318035)
        ·
          refine ⟨43682467679070087418977053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29121645119380058279318035 43682467679070087418977053)
          ·
            refine ⟨16380925379651282782116395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43682467679070087418977053 16380925379651282782116395)
            ·
              refine ⟨24571388069476924173174593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16380925379651282782116395 24571388069476924173174593)
              ·
                refine ⟨18428541052107693129880945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24571388069476924173174593 18428541052107693129880945)
                ·
                  refine ⟨13821405789080769847410709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18428541052107693129880945 13821405789080769847410709)
                  ·
                    refine ⟨647878396363161086597377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13821405789080769847410709 647878396363161086597377)
                    ·
                      refine ⟨485908797272370814948033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 647878396363161086597377 485908797272370814948033)
                      ·
                        rfl

theorem cell23_946304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 2, 6, 2].length) (baseStart_946304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946304 prefixEnd_946304 := by exact prefixLift 946304
  have htrace : WordTrace (prefixWord ++ tailWord_946304) baseStart_946304 baseEnd_946304 := by
    simpa [prefixWord, tailWord_946304, baseEnd_946304] using wordTrace_append hprefix tailTrace_946304
  have hstable : (prefixWord ++ tailWord_946304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946304).length < 2 ^ (prefixWord ++ tailWord_946304).sum := by decide
  have hdescent : baseEnd_946304 < baseStart_946304 := by decide
  rcases family_descends (prefixWord ++ tailWord_946304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946314 : List Nat := [3, 1, 2, 3, 1, 2, 1, 3, 1, 6]
def baseStart_946314 : Nat := 118140960795 + 946314 * 2 ^ 59
def prefixEnd_946314 : Nat := 4983230072969 + 3 ^ 40 * 946314 * 2
def baseEnd_946314 : Nat := 161971310692971925274329

theorem tailTrace_946314 : CollatzResearch.WordTrace tailWord_946314 prefixEnd_946314 161971310692971925274329 := by
  unfold tailWord_946314
  simp only [CollatzResearch.WordTrace]
  refine ⟨8628726773418367602319499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23009938062448980272851997 8628726773418367602319499)
  ·
    refine ⟨12943090160127551403479249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8628726773418367602319499 12943090160127551403479249)
    ·
      refine ⟨9707317620095663552609437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12943090160127551403479249 9707317620095663552609437)
      ·
        refine ⟨3640244107535873832228539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9707317620095663552609437 3640244107535873832228539)
        ·
          refine ⟨5460366161303810748342809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3640244107535873832228539 5460366161303810748342809)
          ·
            refine ⟨4095274620977858061257107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5460366161303810748342809 4095274620977858061257107)
            ·
              refine ⟨6142911931466787091885661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4095274620977858061257107 6142911931466787091885661)
              ·
                refine ⟨2303591974300045159457123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6142911931466787091885661 2303591974300045159457123)
                ·
                  refine ⟨3455387961450067739185685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2303591974300045159457123 3455387961450067739185685)
                  ·
                    refine ⟨161971310692971925274329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3455387961450067739185685 161971310692971925274329)
                    ·
                      rfl

theorem cell23_946314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_946314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946314 prefixEnd_946314 := by exact prefixLift 946314
  have htrace : WordTrace (prefixWord ++ tailWord_946314) baseStart_946314 baseEnd_946314 := by
    simpa [prefixWord, tailWord_946314, baseEnd_946314] using wordTrace_append hprefix tailTrace_946314
  have hstable : (prefixWord ++ tailWord_946314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946314).length < 2 ^ (prefixWord ++ tailWord_946314).sum := by decide
  have hdescent : baseEnd_946314 < baseStart_946314 := by decide
  rcases family_descends (prefixWord ++ tailWord_946314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946326 : List Nat := [5, 3, 2, 1, 1, 1, 2, 3, 1, 4]
def baseStart_946326 : Nat := 118140960795 + 946326 * 2 ^ 59
def prefixEnd_946326 : Nat := 4983230072969 + 3 ^ 40 * 946326 * 2
def baseEnd_946326 : Nat := 161973364615589909624311

theorem tailTrace_946326 : CollatzResearch.WordTrace tailWord_946326 prefixEnd_946326 161973364615589909624311 := by
  unfold tailWord_946326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2157209048101874778669677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23010229846419997639143221 2157209048101874778669677)
  ·
    refine ⟨808953393038203042001129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2157209048101874778669677 808953393038203042001129)
    ·
      refine ⟨606715044778652281500847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 808953393038203042001129 606715044778652281500847)
      ·
        refine ⟨910072567167978422251271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606715044778652281500847 910072567167978422251271)
        ·
          refine ⟨1365108850751967633376907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 910072567167978422251271 1365108850751967633376907)
          ·
            refine ⟨2047663276127951450065361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1365108850751967633376907 2047663276127951450065361)
            ·
              refine ⟨1535747457095963587549021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2047663276127951450065361 1535747457095963587549021)
              ·
                refine ⟨575905296410986345330883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1535747457095963587549021 575905296410986345330883)
                ·
                  refine ⟨863857944616479517996325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 575905296410986345330883 863857944616479517996325)
                  ·
                    refine ⟨161973364615589909624311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 863857944616479517996325 161973364615589909624311)
                    ·
                      rfl

theorem cell23_946326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_946326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946326 prefixEnd_946326 := by exact prefixLift 946326
  have htrace : WordTrace (prefixWord ++ tailWord_946326) baseStart_946326 baseEnd_946326 := by
    simpa [prefixWord, tailWord_946326, baseEnd_946326] using wordTrace_append hprefix tailTrace_946326
  have hstable : (prefixWord ++ tailWord_946326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946326).length < 2 ^ (prefixWord ++ tailWord_946326).sum := by decide
  have hdescent : baseEnd_946326 < baseStart_946326 := by decide
  rcases family_descends (prefixWord ++ tailWord_946326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946338 : List Nat := [3, 3, 1, 3, 1, 2, 1, 3, 1, 1, 4]
def baseStart_946338 : Nat := 118140960795 + 946338 * 2 ^ 59
def prefixEnd_946338 : Nat := 4983230072969 + 3 ^ 40 * 946338 * 2
def baseEnd_946338 : Nat := 485926255614623681922877

theorem tailTrace_946338 : CollatzResearch.WordTrace tailWord_946338 prefixEnd_946338 485926255614623681922877 := by
  unfold tailWord_946338
  simp only [CollatzResearch.WordTrace]
  refine ⟨8628945611396630627037917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23010521630391015005434445 8628945611396630627037917)
  ·
    refine ⟨3235854604273736485139219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8628945611396630627037917 3235854604273736485139219)
    ·
      refine ⟨4853781906410604727708829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3235854604273736485139219 4853781906410604727708829)
      ·
        refine ⟨1820168214903976772890811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4853781906410604727708829 1820168214903976772890811)
        ·
          refine ⟨2730252322355965159336217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1820168214903976772890811 2730252322355965159336217)
          ·
            refine ⟨2047689241766973869502163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2730252322355965159336217 2047689241766973869502163)
            ·
              refine ⟨3071533862650460804253245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2047689241766973869502163 3071533862650460804253245)
              ·
                refine ⟨1151825198493922801594967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3071533862650460804253245 1151825198493922801594967)
                ·
                  refine ⟨1727737797740884202392451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1151825198493922801594967 1727737797740884202392451)
                  ·
                    refine ⟨2591606696611326303588677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1727737797740884202392451 2591606696611326303588677)
                    ·
                      refine ⟨485926255614623681922877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2591606696611326303588677 485926255614623681922877)
                      ·
                        rfl

theorem cell23_946338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_946338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946338 prefixEnd_946338 := by exact prefixLift 946338
  have htrace : WordTrace (prefixWord ++ tailWord_946338) baseStart_946338 baseEnd_946338 := by
    simpa [prefixWord, tailWord_946338, baseEnd_946338] using wordTrace_append hprefix tailTrace_946338
  have hstable : (prefixWord ++ tailWord_946338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946338).length < 2 ^ (prefixWord ++ tailWord_946338).sum := by decide
  have hdescent : baseEnd_946338 < baseStart_946338 := by decide
  rcases family_descends (prefixWord ++ tailWord_946338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946341 : List Nat := [1, 3, 1, 2, 1, 3, 3, 3, 1, 2, 3]
def baseStart_946341 : Nat := 118140960795 + 946341 * 2 ^ 59
def prefixEnd_946341 : Nat := 4983230072969 + 3 ^ 40 * 946341 * 2
def baseEnd_946341 : Nat := 485927796056587170185363

theorem tailTrace_946341 : CollatzResearch.WordTrace tailWord_946341 prefixEnd_946341 485927796056587170185363 := by
  unfold tailWord_946341
  simp only [CollatzResearch.WordTrace]
  refine ⟨34515891864575654020510877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23010594576383769347007251 34515891864575654020510877)
  ·
    refine ⟨12943459449215870257691579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34515891864575654020510877 12943459449215870257691579)
    ·
      refine ⟨19415189173823805386537369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12943459449215870257691579 19415189173823805386537369)
      ·
        refine ⟨14561391880367854039903027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19415189173823805386537369 14561391880367854039903027)
        ·
          refine ⟨21842087820551781059854541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14561391880367854039903027 21842087820551781059854541)
          ·
            refine ⟨8190782932706917897445453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21842087820551781059854541 8190782932706917897445453)
            ·
              refine ⟨3071543599765094211542045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8190782932706917897445453 3071543599765094211542045)
              ·
                refine ⟨1151828849911910329328267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3071543599765094211542045 1151828849911910329328267)
                ·
                  refine ⟨1727743274867865493992401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1151828849911910329328267 1727743274867865493992401)
                  ·
                    refine ⟨1295807456150899120494301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1727743274867865493992401 1295807456150899120494301)
                    ·
                      refine ⟨485927796056587170185363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1295807456150899120494301 485927796056587170185363)
                      ·
                        rfl

theorem cell23_946341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 2, 3].length) (baseStart_946341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946341 prefixEnd_946341 := by exact prefixLift 946341
  have htrace : WordTrace (prefixWord ++ tailWord_946341) baseStart_946341 baseEnd_946341 := by
    simpa [prefixWord, tailWord_946341, baseEnd_946341] using wordTrace_append hprefix tailTrace_946341
  have hstable : (prefixWord ++ tailWord_946341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946341).length < 2 ^ (prefixWord ++ tailWord_946341).sum := by decide
  have hdescent : baseEnd_946341 < baseStart_946341 := by decide
  rcases family_descends (prefixWord ++ tailWord_946341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946377 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 1, 2, 8]
def baseStart_946377 : Nat := 118140960795 + 946377 * 2 ^ 59
def prefixEnd_946377 : Nat := 4983230072969 + 3 ^ 40 * 946377 * 2
def baseEnd_946377 : Nat := 485946281360149029335197

theorem tailTrace_946377 : CollatzResearch.WordTrace tailWord_946377 prefixEnd_946377 485946281360149029335197 := by
  unfold tailWord_946377
  simp only [CollatzResearch.WordTrace]
  refine ⟨34517204892445232168821385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23011469928296821445880923 34517204892445232168821385)
  ·
    refine ⟨25887903669333924126616039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34517204892445232168821385 25887903669333924126616039)
    ·
      refine ⟨38831855504000886189924059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25887903669333924126616039 38831855504000886189924059)
      ·
        refine ⟨58247783256001329284886089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38831855504000886189924059 58247783256001329284886089)
        ·
          refine ⟨43685837442000996963664567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58247783256001329284886089 43685837442000996963664567)
          ·
            refine ⟨65528756163001495445496851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43685837442000996963664567 65528756163001495445496851)
            ·
              refine ⟨98293134244502243168245277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65528756163001495445496851 98293134244502243168245277)
              ·
                refine ⟨36859925341688341188091979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98293134244502243168245277 36859925341688341188091979)
                ·
                  refine ⟨55289888012532511782137969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36859925341688341188091979 55289888012532511782137969)
                  ·
                    refine ⟨41467416009399383836603477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55289888012532511782137969 41467416009399383836603477)
                    ·
                      refine ⟨485946281360149029335197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 41467416009399383836603477 485946281360149029335197)
                      ·
                        rfl

theorem cell23_946377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 2, 8].length) (baseStart_946377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946377 prefixEnd_946377 := by exact prefixLift 946377
  have htrace : WordTrace (prefixWord ++ tailWord_946377) baseStart_946377 baseEnd_946377 := by
    simpa [prefixWord, tailWord_946377, baseEnd_946377] using wordTrace_append hprefix tailTrace_946377
  have hstable : (prefixWord ++ tailWord_946377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946377).length < 2 ^ (prefixWord ++ tailWord_946377).sum := by decide
  have hdescent : baseEnd_946377 < baseStart_946377 := by decide
  rcases family_descends (prefixWord ++ tailWord_946377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946389 : List Nat := [1, 3, 2, 4, 2, 2, 1, 3, 1, 2, 2]
def baseStart_946389 : Nat := 118140960795 + 946389 * 2 ^ 59
def prefixEnd_946389 : Nat := 4983230072969 + 3 ^ 40 * 946389 * 2
def baseEnd_946389 : Nat := 485952443128002982385143

theorem tailTrace_946389 : CollatzResearch.WordTrace tailWord_946389 prefixEnd_946389 485952443128002982385143 := by
  unfold tailWord_946389
  simp only [CollatzResearch.WordTrace]
  refine ⟨34517642568401758218258221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23011761712267838812172147 34517642568401758218258221)
  ·
    refine ⟨12944115963150659331846833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34517642568401758218258221 12944115963150659331846833)
    ·
      refine ⟨9708086972362994498885125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12944115963150659331846833 9708086972362994498885125)
      ·
        refine ⟨1820266307318061468540961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9708086972362994498885125 1820266307318061468540961)
        ·
          refine ⟨1365199730488546101405721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1820266307318061468540961 1365199730488546101405721)
          ·
            refine ⟨1023899797866409576054291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1365199730488546101405721 1023899797866409576054291)
            ·
              refine ⟨1535849696799614364081437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1023899797866409576054291 1535849696799614364081437)
              ·
                refine ⟨575943636299855386530539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1535849696799614364081437 575943636299855386530539)
                ·
                  refine ⟨863915454449783079795809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 575943636299855386530539 863915454449783079795809)
                  ·
                    refine ⟨647936590837337309846857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 863915454449783079795809 647936590837337309846857)
                    ·
                      refine ⟨485952443128002982385143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 647936590837337309846857 485952443128002982385143)
                      ·
                        rfl

theorem cell23_946389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_946389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946389 prefixEnd_946389 := by exact prefixLift 946389
  have htrace : WordTrace (prefixWord ++ tailWord_946389) baseStart_946389 baseEnd_946389 := by
    simpa [prefixWord, tailWord_946389, baseEnd_946389] using wordTrace_append hprefix tailTrace_946389
  have hstable : (prefixWord ++ tailWord_946389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946389).length < 2 ^ (prefixWord ++ tailWord_946389).sum := by decide
  have hdescent : baseEnd_946389 < baseStart_946389 := by decide
  rcases family_descends (prefixWord ++ tailWord_946389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946414 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 3, 3, 5]
def baseStart_946414 : Nat := 118140960795 + 946414 * 2 ^ 59
def prefixEnd_946414 : Nat := 4983230072969 + 3 ^ 40 * 946414 * 2
def baseEnd_946414 : Nat := 485965280144365384572527

theorem tailTrace_946414 : CollatzResearch.WordTrace tailWord_946414 prefixEnd_946414 485965280144365384572527 := by
  unfold tailWord_946414
  simp only [CollatzResearch.WordTrace]
  refine ⟨4314819299163898435989787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23012369595540791658612197 4314819299163898435989787)
  ·
    refine ⟨6472228948745847653984681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4314819299163898435989787 6472228948745847653984681)
    ·
      refine ⟨4854171711559385740488511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6472228948745847653984681 4854171711559385740488511)
      ·
        refine ⟨7281257567339078610732767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4854171711559385740488511 7281257567339078610732767)
        ·
          refine ⟨10921886351008617916099151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7281257567339078610732767 10921886351008617916099151)
          ·
            refine ⟨16382829526512926874148727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10921886351008617916099151 16382829526512926874148727)
            ·
              refine ⟨24574244289769390311223091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16382829526512926874148727 24574244289769390311223091)
              ·
                refine ⟨36861366434654085466834637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24574244289769390311223091 36861366434654085466834637)
                ·
                  refine ⟨13823012412995282050062989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36861366434654085466834637 13823012412995282050062989)
                  ·
                    refine ⟨5183629654873230768773621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13823012412995282050062989 5183629654873230768773621)
                    ·
                      refine ⟨485965280144365384572527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5183629654873230768773621 485965280144365384572527)
                      ·
                        rfl

theorem cell23_946414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_946414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946414 prefixEnd_946414 := by exact prefixLift 946414
  have htrace : WordTrace (prefixWord ++ tailWord_946414) baseStart_946414 baseEnd_946414 := by
    simpa [prefixWord, tailWord_946414, baseEnd_946414] using wordTrace_append hprefix tailTrace_946414
  have hstable : (prefixWord ++ tailWord_946414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946414).length < 2 ^ (prefixWord ++ tailWord_946414).sum := by decide
  have hdescent : baseEnd_946414 < baseStart_946414 := by decide
  rcases family_descends (prefixWord ++ tailWord_946414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946424 : List Nat := [2, 1, 2, 1, 1, 2, 1, 5, 2, 2, 4]
def baseStart_946424 : Nat := 118140960795 + 946424 * 2 ^ 59
def prefixEnd_946424 : Nat := 4983230072969 + 3 ^ 40 * 946424 * 2
def baseEnd_946424 : Nat := 485970414950910345447481

theorem tailTrace_946424 : CollatzResearch.WordTrace tailWord_946424 prefixEnd_946424 485970414950910345447481 := by
  unfold tailWord_946424
  simp only [CollatzResearch.WordTrace]
  refine ⟨17259459561637479597891163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23012612748849972797188217 17259459561637479597891163)
  ·
    refine ⟨25889189342456219396836745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17259459561637479597891163 25889189342456219396836745)
    ·
      refine ⟨19416892006842164547627559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25889189342456219396836745 19416892006842164547627559)
      ·
        refine ⟨29125338010263246821441339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19416892006842164547627559 29125338010263246821441339)
        ·
          refine ⟨43688007015394870232162009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29125338010263246821441339 43688007015394870232162009)
          ·
            refine ⟨32766005261546152674121507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43688007015394870232162009 32766005261546152674121507)
            ·
              refine ⟨49149007892319229011182261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32766005261546152674121507 49149007892319229011182261)
              ·
                refine ⟨4607719489904927719798337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49149007892319229011182261 4607719489904927719798337)
                ·
                  refine ⟨3455789617428695789848753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4607719489904927719798337 3455789617428695789848753)
                  ·
                    refine ⟨2591842213071521842386565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3455789617428695789848753 2591842213071521842386565)
                    ·
                      refine ⟨485970414950910345447481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2591842213071521842386565 485970414950910345447481)
                      ·
                        rfl

theorem cell23_946424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_946424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946424 prefixEnd_946424 := by exact prefixLift 946424
  have htrace : WordTrace (prefixWord ++ tailWord_946424) baseStart_946424 baseEnd_946424 := by
    simpa [prefixWord, tailWord_946424, baseEnd_946424] using wordTrace_append hprefix tailTrace_946424
  have hstable : (prefixWord ++ tailWord_946424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946424).length < 2 ^ (prefixWord ++ tailWord_946424).sum := by decide
  have hdescent : baseEnd_946424 < baseStart_946424 := by decide
  rcases family_descends (prefixWord ++ tailWord_946424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946468 : List Nat := [2, 3, 1, 3, 1, 3, 1, 4, 5]
def baseStart_946468 : Nat := 118140960795 + 946468 * 2 ^ 59
def prefixEnd_946468 : Nat := 4983230072969 + 3 ^ 40 * 946468 * 2
def baseEnd_946468 : Nat := 53999223122189797033031

theorem tailTrace_946468 : CollatzResearch.WordTrace tailWord_946468 prefixEnd_946468 53999223122189797033031 := by
  unfold tailWord_946468
  simp only [CollatzResearch.WordTrace]
  refine ⟨17260261967557777355192029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23013682623410369806922705 17260261967557777355192029)
  ·
    refine ⟨6472598237834166508197011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17260261967557777355192029 6472598237834166508197011)
    ·
      refine ⟨9708897356751249762295517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6472598237834166508197011 9708897356751249762295517)
      ·
        refine ⟨3640836508781718660860819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9708897356751249762295517 3640836508781718660860819)
        ·
          refine ⟨5461254763172577991291229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3640836508781718660860819 5461254763172577991291229)
          ·
            refine ⟨2047970536189716746734211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5461254763172577991291229 2047970536189716746734211)
            ·
              refine ⟨3071955804284575120101317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2047970536189716746734211 3071955804284575120101317)
              ·
                refine ⟨575991713303357835018997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3071955804284575120101317 575991713303357835018997)
                ·
                  refine ⟨53999223122189797033031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 575991713303357835018997 53999223122189797033031)
                  ·
                    rfl

theorem cell23_946468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 4, 5].length) (baseStart_946468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946468 prefixEnd_946468 := by exact prefixLift 946468
  have htrace : WordTrace (prefixWord ++ tailWord_946468) baseStart_946468 baseEnd_946468 := by
    simpa [prefixWord, tailWord_946468, baseEnd_946468] using wordTrace_append hprefix tailTrace_946468
  have hstable : (prefixWord ++ tailWord_946468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946468).length < 2 ^ (prefixWord ++ tailWord_946468).sum := by decide
  have hdescent : baseEnd_946468 < baseStart_946468 := by decide
  rcases family_descends (prefixWord ++ tailWord_946468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946521 : List Nat := [1, 2, 1, 2, 2, 2, 1, 3, 4, 2, 3]
def baseStart_946521 : Nat := 118140960795 + 946521 * 2 ^ 59
def prefixEnd_946521 : Nat := 4983230072969 + 3 ^ 40 * 946521 * 2
def baseEnd_946521 : Nat := 486020222574396465934535

theorem tailTrace_946521 : CollatzResearch.WordTrace tailWord_946521 prefixEnd_946521 486020222574396465934535 := by
  unfold tailWord_946521
  simp only [CollatzResearch.WordTrace]
  refine ⟨34522457003923544762063417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23014971335949029841375611 34522457003923544762063417)
  ·
    refine ⟨25891842752942658571547563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34522457003923544762063417 25891842752942658571547563)
    ·
      refine ⟨38837764129413987857321345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25891842752942658571547563 38837764129413987857321345)
      ·
        refine ⟨29128323097060490892991009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38837764129413987857321345 29128323097060490892991009)
        ·
          refine ⟨21846242322795368169743257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29128323097060490892991009 21846242322795368169743257)
          ·
            refine ⟨16384681742096526127307443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21846242322795368169743257 16384681742096526127307443)
            ·
              refine ⟨24577022613144789190961165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16384681742096526127307443 24577022613144789190961165)
              ·
                refine ⟨9216383479929295946610437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24577022613144789190961165 9216383479929295946610437)
                ·
                  refine ⟨1728071902486742989989457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9216383479929295946610437 1728071902486742989989457)
                  ·
                    refine ⟨1296053926865057242492093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1728071902486742989989457 1296053926865057242492093)
                    ·
                      refine ⟨486020222574396465934535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1296053926865057242492093 486020222574396465934535)
                      ·
                        rfl

theorem cell23_946521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 2, 3].length) (baseStart_946521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946521 prefixEnd_946521 := by exact prefixLift 946521
  have htrace : WordTrace (prefixWord ++ tailWord_946521) baseStart_946521 baseEnd_946521 := by
    simpa [prefixWord, tailWord_946521, baseEnd_946521] using wordTrace_append hprefix tailTrace_946521
  have hstable : (prefixWord ++ tailWord_946521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946521).length < 2 ^ (prefixWord ++ tailWord_946521).sum := by decide
  have hdescent : baseEnd_946521 < baseStart_946521 := by decide
  rcases family_descends (prefixWord ++ tailWord_946521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946538 : List Nat := [3, 1, 3, 3, 1, 1, 1, 2, 1, 4, 3]
def baseStart_946538 : Nat := 118140960795 + 946538 * 2 ^ 59
def prefixEnd_946538 : Nat := 4983230072969 + 3 ^ 40 * 946538 * 2
def baseEnd_946538 : Nat := 486028951745522899421957

theorem tailTrace_946538 : CollatzResearch.WordTrace tailWord_946538 prefixEnd_946538 486028951745522899421957 := by
  unfold tailWord_946538
  simp only [CollatzResearch.WordTrace]
  refine ⟨8630769261215489166358067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23015384696574637776954845 8630769261215489166358067)
  ·
    refine ⟨12946153891823233749537101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8630769261215489166358067 12946153891823233749537101)
    ·
      refine ⟨4854807709433712656076413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12946153891823233749537101 4854807709433712656076413)
      ·
        refine ⟨1820552891037642246028655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4854807709433712656076413 1820552891037642246028655)
        ·
          refine ⟨2730829336556463369042983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1820552891037642246028655 2730829336556463369042983)
          ·
            refine ⟨4096244004834695053564475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2730829336556463369042983 4096244004834695053564475)
            ·
              refine ⟨6144366007252042580346713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4096244004834695053564475 6144366007252042580346713)
              ·
                refine ⟨4608274505439031935260035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6144366007252042580346713 4608274505439031935260035)
                ·
                  refine ⟨6912411758158547902890053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4608274505439031935260035 6912411758158547902890053)
                  ·
                    refine ⟨1296077204654727731791885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6912411758158547902890053 1296077204654727731791885)
                    ·
                      refine ⟨486028951745522899421957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1296077204654727731791885 486028951745522899421957)
                      ·
                        rfl

theorem cell23_946538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_946538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946538 prefixEnd_946538 := by exact prefixLift 946538
  have htrace : WordTrace (prefixWord ++ tailWord_946538) baseStart_946538 baseEnd_946538 := by
    simpa [prefixWord, tailWord_946538, baseEnd_946538] using wordTrace_append hprefix tailTrace_946538
  have hstable : (prefixWord ++ tailWord_946538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946538).length < 2 ^ (prefixWord ++ tailWord_946538).sum := by decide
  have hdescent : baseEnd_946538 < baseStart_946538 := by decide
  rcases family_descends (prefixWord ++ tailWord_946538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946605 : List Nat := [1, 5, 2, 2, 2, 1, 1, 1, 3, 5]
def baseStart_946605 : Nat := 118140960795 + 946605 * 2 ^ 59
def prefixEnd_946605 : Nat := 4983230072969 + 3 ^ 40 * 946605 * 2
def baseEnd_946605 : Nat := 162021118316458045761383

theorem tailTrace_946605 : CollatzResearch.WordTrace tailWord_946605 prefixEnd_946605 162021118316458045761383 := by
  unfold tailWord_946605
  simp only [CollatzResearch.WordTrace]
  refine ⟨34525520735619227108121269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23017013823746151405414179 34525520735619227108121269)
  ·
    refine ⟨3236767568964302541386369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34525520735619227108121269 3236767568964302541386369)
    ·
      refine ⟨2427575676723226906039777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3236767568964302541386369 2427575676723226906039777)
      ·
        refine ⟨1820681757542420179529833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2427575676723226906039777 1820681757542420179529833)
        ·
          refine ⟨1365511318156815134647375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1820681757542420179529833 1365511318156815134647375)
          ·
            refine ⟨2048266977235222701971063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1365511318156815134647375 2048266977235222701971063)
            ·
              refine ⟨3072400465852834052956595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2048266977235222701971063 3072400465852834052956595)
              ·
                refine ⟨4608600698779251079434893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3072400465852834052956595 4608600698779251079434893)
                ·
                  refine ⟨1728225262042219154788085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4608600698779251079434893 1728225262042219154788085)
                  ·
                    refine ⟨162021118316458045761383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1728225262042219154788085 162021118316458045761383)
                    ·
                      rfl

theorem cell23_946605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_946605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946605 prefixEnd_946605 := by exact prefixLift 946605
  have htrace : WordTrace (prefixWord ++ tailWord_946605) baseStart_946605 baseEnd_946605 := by
    simpa [prefixWord, tailWord_946605, baseEnd_946605] using wordTrace_append hprefix tailTrace_946605
  have hstable : (prefixWord ++ tailWord_946605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946605).length < 2 ^ (prefixWord ++ tailWord_946605).sum := by decide
  have hdescent : baseEnd_946605 < baseStart_946605 := by decide
  rcases family_descends (prefixWord ++ tailWord_946605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946636 : List Nat := [2, 2, 1, 4, 3, 2, 2, 2, 1, 1, 3]
def baseStart_946636 : Nat := 118140960795 + 946636 * 2 ^ 59
def prefixEnd_946636 : Nat := 4983230072969 + 3 ^ 40 * 946636 * 2
def baseEnd_946636 : Nat := 486079272849663515996507

theorem tailTrace_946636 : CollatzResearch.WordTrace tailWord_946636 prefixEnd_946636 486079272849663515996507 := by
  unfold tailWord_946636
  simp only [CollatzResearch.WordTrace]
  refine ⟨17263325699253459701249881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23017767599004612934999841 17263325699253459701249881)
  ·
    refine ⟨12947494274440094775937411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17263325699253459701249881 12947494274440094775937411)
    ·
      refine ⟨19421241411660142163906117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12947494274440094775937411 19421241411660142163906117)
      ·
        refine ⟨3641482764686276655732397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19421241411660142163906117 3641482764686276655732397)
        ·
          refine ⟨1365556036757353745899649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3641482764686276655732397 1365556036757353745899649)
          ·
            refine ⟨1024167027568015309424737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1365556036757353745899649 1024167027568015309424737)
            ·
              refine ⟨768125270676011482068553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1024167027568015309424737 768125270676011482068553)
              ·
                refine ⟨576093953007008611551415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 768125270676011482068553 576093953007008611551415)
                ·
                  refine ⟨864140929510512917327123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 576093953007008611551415 864140929510512917327123)
                  ·
                    refine ⟨1296211394265769375990685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 864140929510512917327123 1296211394265769375990685)
                    ·
                      refine ⟨486079272849663515996507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1296211394265769375990685 486079272849663515996507)
                      ·
                        rfl

theorem cell23_946636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_946636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946636 prefixEnd_946636 := by exact prefixLift 946636
  have htrace : WordTrace (prefixWord ++ tailWord_946636) baseStart_946636 baseEnd_946636 := by
    simpa [prefixWord, tailWord_946636, baseEnd_946636] using wordTrace_append hprefix tailTrace_946636
  have hstable : (prefixWord ++ tailWord_946636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946636).length < 2 ^ (prefixWord ++ tailWord_946636).sum := by decide
  have hdescent : baseEnd_946636 < baseStart_946636 := by decide
  rcases family_descends (prefixWord ++ tailWord_946636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946671 : List Nat := [1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 5]
def baseStart_946671 : Nat := 118140960795 + 946671 * 2 ^ 59
def prefixEnd_946671 : Nat := 4983230072969 + 3 ^ 40 * 946671 * 2
def baseEnd_946671 : Nat := 486097244672570879058845

theorem tailTrace_946671 : CollatzResearch.WordTrace tailWord_946671 prefixEnd_946671 486097244672570879058845 := by
  unfold tailWord_946671
  simp only [CollatzResearch.WordTrace]
  refine ⟨34527927953380120380023867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23018618635586746920015911 34527927953380120380023867)
  ·
    refine ⟨51791891930070180570035801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34527927953380120380023867 51791891930070180570035801)
    ·
      refine ⟨38843918947552635427526851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51791891930070180570035801 38843918947552635427526851)
      ·
        refine ⟨58265878421328953141290277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38843918947552635427526851 58265878421328953141290277)
        ·
          refine ⟨10924852203999178713991927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58265878421328953141290277 10924852203999178713991927)
          ·
            refine ⟨16387278305998768070987891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10924852203999178713991927 16387278305998768070987891)
            ·
              refine ⟨24580917458998152106481837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16387278305998768070987891 24580917458998152106481837)
              ·
                refine ⟨9217844047124307039930689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24580917458998152106481837 9217844047124307039930689)
                ·
                  refine ⟨6913383035343230279948017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9217844047124307039930689 6913383035343230279948017)
                  ·
                    refine ⟨5185037276507422709961013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6913383035343230279948017 5185037276507422709961013)
                    ·
                      refine ⟨486097244672570879058845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5185037276507422709961013 486097244672570879058845)
                      ·
                        rfl

theorem cell23_946671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 5].length) (baseStart_946671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946671 prefixEnd_946671 := by exact prefixLift 946671
  have htrace : WordTrace (prefixWord ++ tailWord_946671) baseStart_946671 baseEnd_946671 := by
    simpa [prefixWord, tailWord_946671, baseEnd_946671] using wordTrace_append hprefix tailTrace_946671
  have hstable : (prefixWord ++ tailWord_946671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946671).length < 2 ^ (prefixWord ++ tailWord_946671).sum := by decide
  have hdescent : baseEnd_946671 < baseStart_946671 := by decide
  rcases family_descends (prefixWord ++ tailWord_946671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946691 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 4, 6]
def baseStart_946691 : Nat := 118140960795 + 946691 * 2 ^ 59
def prefixEnd_946691 : Nat := 4983230072969 + 3 ^ 40 * 946691 * 2
def baseEnd_946691 : Nat := 162035838095220266936251

theorem tailTrace_946691 : CollatzResearch.WordTrace tailWord_946691 prefixEnd_946691 162035838095220266936251 := by
  unfold tailWord_946691
  simp only [CollatzResearch.WordTrace]
  refine ⟨34528657413307663795751927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23019104942205109197167951 34528657413307663795751927)
  ·
    refine ⟨51792986119961495693627891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34528657413307663795751927 51792986119961495693627891)
    ·
      refine ⟨77689479179942243540441837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51792986119961495693627891 77689479179942243540441837)
      ·
        refine ⟨29133554692478341327665689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77689479179942243540441837 29133554692478341327665689)
        ·
          refine ⟨21850166019358755995749267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29133554692478341327665689 21850166019358755995749267)
          ·
            refine ⟨32775249029038133993623901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21850166019358755995749267 32775249029038133993623901)
            ·
              refine ⟨12290718385889300247608963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32775249029038133993623901 12290718385889300247608963)
              ·
                refine ⟨18436077578833950371413445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12290718385889300247608963 18436077578833950371413445)
                ·
                  refine ⟨3456764546031365694640021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18436077578833950371413445 3456764546031365694640021)
                  ·
                    refine ⟨162035838095220266936251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3456764546031365694640021 162035838095220266936251)
                    ·
                      rfl

theorem cell23_946691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 6].length) (baseStart_946691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946691 prefixEnd_946691 := by exact prefixLift 946691
  have htrace : WordTrace (prefixWord ++ tailWord_946691) baseStart_946691 baseEnd_946691 := by
    simpa [prefixWord, tailWord_946691, baseEnd_946691] using wordTrace_append hprefix tailTrace_946691
  have hstable : (prefixWord ++ tailWord_946691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946691).length < 2 ^ (prefixWord ++ tailWord_946691).sum := by decide
  have hdescent : baseEnd_946691 < baseStart_946691 := by decide
  rcases family_descends (prefixWord ++ tailWord_946691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946692 : List Nat := [2, 3, 2, 3, 1, 2, 1, 1, 4, 1, 3]
def baseStart_946692 : Nat := 118140960795 + 946692 * 2 ^ 59
def prefixEnd_946692 : Nat := 4983230072969 + 3 ^ 40 * 946692 * 2
def baseEnd_946692 : Nat := 486108027766315296896249

theorem tailTrace_946692 : CollatzResearch.WordTrace tailWord_946692 prefixEnd_946692 486108027766315296896249 := by
  unfold tailWord_946692
  simp only [CollatzResearch.WordTrace]
  refine ⟨17264346943152020483269165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23019129257536027311025553 17264346943152020483269165)
  ·
    refine ⟨6474130103682007681225937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17264346943152020483269165 6474130103682007681225937)
    ·
      refine ⟨4855597577761505760919453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6474130103682007681225937 4855597577761505760919453)
      ·
        refine ⟨1820849091660564660344795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4855597577761505760919453 1820849091660564660344795)
        ·
          refine ⟨2731273637490846990517193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1820849091660564660344795 2731273637490846990517193)
          ·
            refine ⟨2048455228118135242887895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2731273637490846990517193 2048455228118135242887895)
            ·
              refine ⟨3072682842177202864331843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2048455228118135242887895 3072682842177202864331843)
              ·
                refine ⟨4609024263265804296497765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3072682842177202864331843 4609024263265804296497765)
                ·
                  refine ⟨864192049362338305593331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4609024263265804296497765 864192049362338305593331)
                  ·
                    refine ⟨1296288074043507458389997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 864192049362338305593331 1296288074043507458389997)
                    ·
                      refine ⟨486108027766315296896249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1296288074043507458389997 486108027766315296896249)
                      ·
                        rfl

theorem cell23_946692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_946692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946692 prefixEnd_946692 := by exact prefixLift 946692
  have htrace : WordTrace (prefixWord ++ tailWord_946692) baseStart_946692 baseEnd_946692 := by
    simpa [prefixWord, tailWord_946692, baseEnd_946692] using wordTrace_append hprefix tailTrace_946692
  have hstable : (prefixWord ++ tailWord_946692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946692).length < 2 ^ (prefixWord ++ tailWord_946692).sum := by decide
  have hdescent : baseEnd_946692 < baseStart_946692 := by decide
  rcases family_descends (prefixWord ++ tailWord_946692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946785 : List Nat := [1, 2, 3, 1, 1, 5, 2, 1, 2, 5]
def baseStart_946785 : Nat := 118140960795 + 946785 * 2 ^ 59
def prefixEnd_946785 : Nat := 4983230072969 + 3 ^ 40 * 946785 * 2
def baseEnd_946785 : Nat := 162051927155727811011107

theorem tailTrace_946785 : CollatzResearch.WordTrace tailWord_946785 prefixEnd_946785 162051927155727811011107 := by
  unfold tailWord_946785
  simp only [CollatzResearch.WordTrace]
  refine ⟨34532085874967117849673809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23021390583311411899782539 34532085874967117849673809)
  ·
    refine ⟨25899064406225338387255357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34532085874967117849673809 25899064406225338387255357)
    ·
      refine ⟨9712149152334501895220759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25899064406225338387255357 9712149152334501895220759)
      ·
        refine ⟨14568223728501752842831139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9712149152334501895220759 14568223728501752842831139)
        ·
          refine ⟨21852335592752629264246709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14568223728501752842831139 21852335592752629264246709)
          ·
            refine ⟨2048656461820558993523129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21852335592752629264246709 2048656461820558993523129)
            ·
              refine ⟨1536492346365419245142347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2048656461820558993523129 1536492346365419245142347)
              ·
                refine ⟨2304738519548128867713521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1536492346365419245142347 2304738519548128867713521)
                ·
                  refine ⟨1728553889661096650785141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2304738519548128867713521 1728553889661096650785141)
                  ·
                    refine ⟨162051927155727811011107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1728553889661096650785141 162051927155727811011107)
                    ·
                      rfl

theorem cell23_946785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_946785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946785 prefixEnd_946785 := by exact prefixLift 946785
  have htrace : WordTrace (prefixWord ++ tailWord_946785) baseStart_946785 baseEnd_946785 := by
    simpa [prefixWord, tailWord_946785, baseEnd_946785] using wordTrace_append hprefix tailTrace_946785
  have hstable : (prefixWord ++ tailWord_946785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946785).length < 2 ^ (prefixWord ++ tailWord_946785).sum := by decide
  have hdescent : baseEnd_946785 < baseStart_946785 := by decide
  rcases family_descends (prefixWord ++ tailWord_946785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946806 : List Nat := [5, 1, 1, 2, 3, 2, 2, 2, 5]
def baseStart_946806 : Nat := 118140960795 + 946806 * 2 ^ 59
def prefixEnd_946806 : Nat := 4983230072969 + 3 ^ 40 * 946806 * 2
def baseEnd_946806 : Nat := 54018507173436427874525

theorem tailTrace_946806 : CollatzResearch.WordTrace tailWord_946806 prefixEnd_946806 54018507173436427874525 := by
  unfold tailWord_946806
  simp only [CollatzResearch.WordTrace]
  refine ⟨2158303237993189902261767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23021901205260692290792181 2158303237993189902261767)
  ·
    refine ⟨3237454856989784853392651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2158303237993189902261767 3237454856989784853392651)
    ·
      refine ⟨4856182285484677280088977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3237454856989784853392651 4856182285484677280088977)
      ·
        refine ⟨3642136714113507960066733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4856182285484677280088977 3642136714113507960066733)
        ·
          refine ⟨1365801267792565485025025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3642136714113507960066733 1365801267792565485025025)
          ·
            refine ⟨1024350950844424113768769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1365801267792565485025025 1024350950844424113768769)
            ·
              refine ⟨768263213133318085326577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1024350950844424113768769 768263213133318085326577)
              ·
                refine ⟨576197409849988563994933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 768263213133318085326577 576197409849988563994933)
                ·
                  refine ⟨54018507173436427874525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 576197409849988563994933 54018507173436427874525)
                  ·
                    rfl

theorem cell23_946806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_946806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946806 prefixEnd_946806 := by exact prefixLift 946806
  have htrace : WordTrace (prefixWord ++ tailWord_946806) baseStart_946806 baseEnd_946806 := by
    simpa [prefixWord, tailWord_946806, baseEnd_946806] using wordTrace_append hprefix tailTrace_946806
  have hstable : (prefixWord ++ tailWord_946806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946806).length < 2 ^ (prefixWord ++ tailWord_946806).sum := by decide
  have hdescent : baseEnd_946806 < baseStart_946806 := by decide
  rcases family_descends (prefixWord ++ tailWord_946806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946862 : List Nat := [4, 1, 4, 1, 1, 2, 1, 1, 8]
def baseStart_946862 : Nat := 118140960795 + 946862 * 2 ^ 59
def prefixEnd_946862 : Nat := 4983230072969 + 3 ^ 40 * 946862 * 2
def baseEnd_946862 : Nat := 54021702164175514641163

theorem tailTrace_946862 : CollatzResearch.WordTrace tailWord_946862 prefixEnd_946862 54021702164175514641163 := by
  unfold tailWord_946862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4316861786961020000028355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23023262863792106666817893 4316861786961020000028355)
  ·
    refine ⟨6475292680441530000042533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4316861786961020000028355 6475292680441530000042533)
    ·
      refine ⟨1214117377582786875007975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6475292680441530000042533 1214117377582786875007975)
      ·
        refine ⟨1821176066374180312511963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1214117377582786875007975 1821176066374180312511963)
        ·
          refine ⟨2731764099561270468767945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1821176066374180312511963 2731764099561270468767945)
          ·
            refine ⟨2048823074670952851575959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2731764099561270468767945 2048823074670952851575959)
            ·
              refine ⟨3073234612006429277363939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2048823074670952851575959 3073234612006429277363939)
              ·
                refine ⟨4609851918009643916045909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3073234612006429277363939 4609851918009643916045909)
                ·
                  refine ⟨54021702164175514641163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4609851918009643916045909 54021702164175514641163)
                  ·
                    rfl

theorem cell23_946862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 8].length) (baseStart_946862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946862 prefixEnd_946862 := by exact prefixLift 946862
  have htrace : WordTrace (prefixWord ++ tailWord_946862) baseStart_946862 baseEnd_946862 := by
    simpa [prefixWord, tailWord_946862, baseEnd_946862] using wordTrace_append hprefix tailTrace_946862
  have hstable : (prefixWord ++ tailWord_946862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946862).length < 2 ^ (prefixWord ++ tailWord_946862).sum := by decide
  have hdescent : baseEnd_946862 < baseStart_946862 := by decide
  rcases family_descends (prefixWord ++ tailWord_946862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946892 : List Nat := [2, 2, 1, 5, 1, 1, 1, 4, 1, 5]
def baseStart_946892 : Nat := 118140960795 + 946892 * 2 ^ 59
def prefixEnd_946892 : Nat := 4983230072969 + 3 ^ 40 * 946892 * 2
def baseEnd_946892 : Nat := 162070241299071504798443

theorem tailTrace_946892 : CollatzResearch.WordTrace tailWord_946892 prefixEnd_946892 162070241299071504798443 := by
  unfold tailWord_946892
  simp only [CollatzResearch.WordTrace]
  refine ⟨17267994242789737561909465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23023992323719650082545953 17267994242789737561909465)
  ·
    refine ⟨12950995682092303171432099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17267994242789737561909465 12950995682092303171432099)
    ·
      refine ⟨19426493523138454757148149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12950995682092303171432099 19426493523138454757148149)
      ·
        refine ⟨1821233767794230133482639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19426493523138454757148149 1821233767794230133482639)
        ·
          refine ⟨2731850651691345200223959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1821233767794230133482639 2731850651691345200223959)
          ·
            refine ⟨4097775977537017800335939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2731850651691345200223959 4097775977537017800335939)
            ·
              refine ⟨6146663966305526700503909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4097775977537017800335939 6146663966305526700503909)
              ·
                refine ⟨1152499493682286256344483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6146663966305526700503909 1152499493682286256344483)
                ·
                  refine ⟨1728749240523429384516725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1152499493682286256344483 1728749240523429384516725)
                  ·
                    refine ⟨162070241299071504798443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1728749240523429384516725 162070241299071504798443)
                    ·
                      rfl

theorem cell23_946892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 1, 5].length) (baseStart_946892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946892 prefixEnd_946892 := by exact prefixLift 946892
  have htrace : WordTrace (prefixWord ++ tailWord_946892) baseStart_946892 baseEnd_946892 := by
    simpa [prefixWord, tailWord_946892, baseEnd_946892] using wordTrace_append hprefix tailTrace_946892
  have hstable : (prefixWord ++ tailWord_946892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946892).length < 2 ^ (prefixWord ++ tailWord_946892).sum := by decide
  have hdescent : baseEnd_946892 < baseStart_946892 := by decide
  rcases family_descends (prefixWord ++ tailWord_946892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946905 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 6, 4]
def baseStart_946905 : Nat := 118140960795 + 946905 * 2 ^ 59
def prefixEnd_946905 : Nat := 4983230072969 + 3 ^ 40 * 946905 * 2
def baseEnd_946905 : Nat := 162072466381907654510923

theorem tailTrace_946905 : CollatzResearch.WordTrace tailWord_946905 prefixEnd_946905 162072466381907654510923 := by
  unfold tailWord_946905
  simp only [CollatzResearch.WordTrace]
  refine ⟨34536462634532378344042169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23024308423021585562694779 34536462634532378344042169)
  ·
    refine ⟨25902346975899283758031627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34536462634532378344042169 25902346975899283758031627)
    ·
      refine ⟨38853520463848925637047441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25902346975899283758031627 38853520463848925637047441)
      ·
        refine ⟨29140140347886694227785581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38853520463848925637047441 29140140347886694227785581)
        ·
          refine ⟨10927552630457510335419593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29140140347886694227785581 10927552630457510335419593)
          ·
            refine ⟨8195664472843132751564695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10927552630457510335419593 8195664472843132751564695)
            ·
              refine ⟨12293496709264699127347043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8195664472843132751564695 12293496709264699127347043)
              ·
                refine ⟨18440245063897048691020565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12293496709264699127347043 18440245063897048691020565)
                ·
                  refine ⟨864386487370174157391589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 18440245063897048691020565 864386487370174157391589)
                  ·
                    refine ⟨162072466381907654510923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 864386487370174157391589 162072466381907654510923)
                    ·
                      rfl

theorem cell23_946905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 6, 4].length) (baseStart_946905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946905 prefixEnd_946905 := by exact prefixLift 946905
  have htrace : WordTrace (prefixWord ++ tailWord_946905) baseStart_946905 baseEnd_946905 := by
    simpa [prefixWord, tailWord_946905, baseEnd_946905] using wordTrace_append hprefix tailTrace_946905
  have hstable : (prefixWord ++ tailWord_946905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946905).length < 2 ^ (prefixWord ++ tailWord_946905).sum := by decide
  have hdescent : baseEnd_946905 < baseStart_946905 := by decide
  rcases family_descends (prefixWord ++ tailWord_946905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946922 : List Nat := [3, 1, 3, 1, 1, 1, 1, 6, 2, 4]
def baseStart_946922 : Nat := 118140960795 + 946922 * 2 ^ 59
def prefixEnd_946922 : Nat := 4983230072969 + 3 ^ 40 * 946922 * 2
def baseEnd_946922 : Nat := 162075376105616465673397

theorem tailTrace_946922 : CollatzResearch.WordTrace tailWord_946922 prefixEnd_946922 162075376105616465673397 := by
  unfold tailWord_946922
  simp only [CollatzResearch.WordTrace]
  refine ⟨8634270668867697561852755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23024721783647193498274013 8634270668867697561852755)
  ·
    refine ⟨12951406003301546342779133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8634270668867697561852755 12951406003301546342779133)
    ·
      refine ⟨4856777251238079878542175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12951406003301546342779133 4856777251238079878542175)
      ·
        refine ⟨7285165876857119817813263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4856777251238079878542175 7285165876857119817813263)
        ·
          refine ⟨10927748815285679726719895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7285165876857119817813263 10927748815285679726719895)
          ·
            refine ⟨16391623222928519590079843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10927748815285679726719895 16391623222928519590079843)
            ·
              refine ⟨24587434834392779385119765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16391623222928519590079843 24587434834392779385119765)
              ·
                refine ⟨1152536007862161533677489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24587434834392779385119765 1152536007862161533677489)
                ·
                  refine ⟨864402005896621150258117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1152536007862161533677489 864402005896621150258117)
                  ·
                    refine ⟨162075376105616465673397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 864402005896621150258117 162075376105616465673397)
                    ·
                      rfl

theorem cell23_946922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_946922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946922 prefixEnd_946922 := by exact prefixLift 946922
  have htrace : WordTrace (prefixWord ++ tailWord_946922) baseStart_946922 baseEnd_946922 := by
    simpa [prefixWord, tailWord_946922, baseEnd_946922] using wordTrace_append hprefix tailTrace_946922
  have hstable : (prefixWord ++ tailWord_946922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946922).length < 2 ^ (prefixWord ++ tailWord_946922).sum := by decide
  have hdescent : baseEnd_946922 < baseStart_946922 := by decide
  rcases family_descends (prefixWord ++ tailWord_946922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946925 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 3, 1, 6]
def baseStart_946925 : Nat := 118140960795 + 946925 * 2 ^ 59
def prefixEnd_946925 : Nat := 4983230072969 + 3 ^ 40 * 946925 * 2
def baseEnd_946925 : Nat := 486227668758812885282677

theorem tailTrace_946925 : CollatzResearch.WordTrace tailWord_946925 prefixEnd_946925 486227668758812885282677 := by
  unfold tailWord_946925
  simp only [CollatzResearch.WordTrace]
  refine ⟨34537192094459921759770229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23024794729639947839846819 34537192094459921759770229)
  ·
    refine ⟨3237861758855617664978459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34537192094459921759770229 3237861758855617664978459)
    ·
      refine ⟨4856792638283426497467689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3237861758855617664978459 4856792638283426497467689)
      ·
        refine ⟨3642594478712569873100767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4856792638283426497467689 3642594478712569873100767)
        ·
          refine ⟨5463891718068854809651151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3642594478712569873100767 5463891718068854809651151)
          ·
            refine ⟨8195837577103282214476727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5463891718068854809651151 8195837577103282214476727)
            ·
              refine ⟨12293756365654923321715091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8195837577103282214476727 12293756365654923321715091)
              ·
                refine ⟨18440634548482384982572637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12293756365654923321715091 18440634548482384982572637)
                ·
                  refine ⟨6915237955680894368464739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18440634548482384982572637 6915237955680894368464739)
                  ·
                    refine ⟨10372856933521341552697109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6915237955680894368464739 10372856933521341552697109)
                    ·
                      refine ⟨486227668758812885282677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10372856933521341552697109 486227668758812885282677)
                      ·
                        rfl

theorem cell23_946925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_946925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946925 prefixEnd_946925 := by exact prefixLift 946925
  have htrace : WordTrace (prefixWord ++ tailWord_946925) baseStart_946925 baseEnd_946925 := by
    simpa [prefixWord, tailWord_946925, baseEnd_946925] using wordTrace_append hprefix tailTrace_946925
  have hstable : (prefixWord ++ tailWord_946925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946925).length < 2 ^ (prefixWord ++ tailWord_946925).sum := by decide
  have hdescent : baseEnd_946925 < baseStart_946925 := by decide
  rcases family_descends (prefixWord ++ tailWord_946925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946942 : List Nat := [4, 2, 2, 1, 2, 1, 2, 1, 1, 1, 6]
def baseStart_946942 : Nat := 118140960795 + 946942 * 2 ^ 59
def prefixEnd_946942 : Nat := 4983230072969 + 3 ^ 40 * 946942 * 2
def baseEnd_946942 : Nat := 486236397929939318770099

theorem tailTrace_946942 : CollatzResearch.WordTrace tailWord_946942 prefixEnd_946942 486236397929939318770099 := by
  unfold tailWord_946942
  simp only [CollatzResearch.WordTrace]
  refine ⟨4317226516924791707892385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23025208090265555775426053 4317226516924791707892385)
  ·
    refine ⟨3237919887693593780919289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4317226516924791707892385 3237919887693593780919289)
    ·
      refine ⟨2428439915770195335689467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3237919887693593780919289 2428439915770195335689467)
      ·
        refine ⟨3642659873655293003534201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2428439915770195335689467 3642659873655293003534201)
        ·
          refine ⟨2731994905241469752650651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3642659873655293003534201 2731994905241469752650651)
          ·
            refine ⟨4097992357862204628975977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2731994905241469752650651 4097992357862204628975977)
            ·
              refine ⟨3073494268396653471731983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4097992357862204628975977 3073494268396653471731983)
              ·
                refine ⟨4610241402594980207597975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3073494268396653471731983 4610241402594980207597975)
                ·
                  refine ⟨6915362103892470311396963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4610241402594980207597975 6915362103892470311396963)
                  ·
                    refine ⟨10373043155838705467095445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6915362103892470311396963 10373043155838705467095445)
                    ·
                      refine ⟨486236397929939318770099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10373043155838705467095445 486236397929939318770099)
                      ·
                        rfl

theorem cell23_946942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_946942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946942 prefixEnd_946942 := by exact prefixLift 946942
  have htrace : WordTrace (prefixWord ++ tailWord_946942) baseStart_946942 baseEnd_946942 := by
    simpa [prefixWord, tailWord_946942, baseEnd_946942] using wordTrace_append hprefix tailTrace_946942
  have hstable : (prefixWord ++ tailWord_946942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946942).length < 2 ^ (prefixWord ++ tailWord_946942).sum := by decide
  have hdescent : baseEnd_946942 < baseStart_946942 := by decide
  rcases family_descends (prefixWord ++ tailWord_946942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946946 : List Nat := [3, 4, 1, 1, 1, 4, 1, 2, 1, 1, 4]
def baseStart_946946 : Nat := 118140960795 + 946946 * 2 ^ 59
def prefixEnd_946946 : Nat := 4983230072969 + 3 ^ 40 * 946946 * 2
def baseEnd_946946 : Nat := 486238451852557303120081

theorem tailTrace_946946 : CollatzResearch.WordTrace tailWord_946946 prefixEnd_946946 486238451852557303120081 := by
  unfold tailWord_946946
  simp only [CollatzResearch.WordTrace]
  refine ⟨8634489506845960586571173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23025305351589228230856461 8634489506845960586571173)
  ·
    refine ⟨1618966782533617609982095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8634489506845960586571173 1618966782533617609982095)
    ·
      refine ⟨2428450173800426414973143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1618966782533617609982095 2428450173800426414973143)
      ·
        refine ⟨3642675260700639622459715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2428450173800426414973143 3642675260700639622459715)
        ·
          refine ⟨5464012891050959433689573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3642675260700639622459715 5464012891050959433689573)
          ·
            refine ⟨1024502417072054893816795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5464012891050959433689573 1024502417072054893816795)
            ·
              refine ⟨1536753625608082340725193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1024502417072054893816795 1536753625608082340725193)
              ·
                refine ⟨1152565219206061755543895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1536753625608082340725193 1152565219206061755543895)
                ·
                  refine ⟨1728847828809092633315843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1152565219206061755543895 1728847828809092633315843)
                  ·
                    refine ⟨2593271743213638949973765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1728847828809092633315843 2593271743213638949973765)
                    ·
                      refine ⟨486238451852557303120081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2593271743213638949973765 486238451852557303120081)
                      ·
                        rfl

theorem cell23_946946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_946946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946946 prefixEnd_946946 := by exact prefixLift 946946
  have htrace : WordTrace (prefixWord ++ tailWord_946946) baseStart_946946 baseEnd_946946 := by
    simpa [prefixWord, tailWord_946946, baseEnd_946946] using wordTrace_append hprefix tailTrace_946946
  have hstable : (prefixWord ++ tailWord_946946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946946).length < 2 ^ (prefixWord ++ tailWord_946946).sum := by decide
  have hdescent : baseEnd_946946 < baseStart_946946 := by decide
  rcases family_descends (prefixWord ++ tailWord_946946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946986 : List Nat := [3, 1, 4, 3, 2, 1, 1, 8]
def baseStart_946986 : Nat := 118140960795 + 946986 * 2 ^ 59
def prefixEnd_946986 : Nat := 4983230072969 + 3 ^ 40 * 946986 * 2
def baseEnd_946986 : Nat := 18009592262175449874811

theorem tailTrace_946986 : CollatzResearch.WordTrace tailWord_946986 prefixEnd_946986 18009592262175449874811 := by
  unfold tailWord_946986
  simp only [CollatzResearch.WordTrace]
  refine ⟨8634854236809732294435203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23026277964825952785160541 8634854236809732294435203)
  ·
    refine ⟨12952281355214598441652805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8634854236809732294435203 12952281355214598441652805)
    ·
      refine ⟨2428552754102737207809901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12952281355214598441652805 2428552754102737207809901)
      ·
        refine ⟨910707282788526452928713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2428552754102737207809901 910707282788526452928713)
        ·
          refine ⟨683030462091394839696535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 910707282788526452928713 683030462091394839696535)
          ·
            refine ⟨1024545693137092259544803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 683030462091394839696535 1024545693137092259544803)
            ·
              refine ⟨1536818539705638389317205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1024545693137092259544803 1536818539705638389317205)
              ·
                refine ⟨18009592262175449874811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1536818539705638389317205 18009592262175449874811)
                ·
                  rfl

theorem cell23_946986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 8].length) (baseStart_946986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946986 prefixEnd_946986 := by exact prefixLift 946986
  have htrace : WordTrace (prefixWord ++ tailWord_946986) baseStart_946986 baseEnd_946986 := by
    simpa [prefixWord, tailWord_946986, baseEnd_946986] using wordTrace_append hprefix tailTrace_946986
  have hstable : (prefixWord ++ tailWord_946986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946986).length < 2 ^ (prefixWord ++ tailWord_946986).sum := by decide
  have hdescent : baseEnd_946986 < baseStart_946986 := by decide
  rcases family_descends (prefixWord ++ tailWord_946986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946995 : List Nat := [1, 1, 1, 2, 6, 1, 1, 1, 1, 8]
def baseStart_946995 : Nat := 118140960795 + 946995 * 2 ^ 59
def prefixEnd_946995 : Nat := 4983230072969 + 3 ^ 40 * 946995 * 2
def baseEnd_946995 : Nat := 162087870801542537135785

theorem tailTrace_946995 : CollatzResearch.WordTrace tailWord_946995 prefixEnd_946995 162087870801542537135785 := by
  unfold tailWord_946995
  simp only [CollatzResearch.WordTrace]
  refine ⟨34539745204206323714818439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23026496802804215809878959 34539745204206323714818439)
  ·
    refine ⟨51809617806309485572227659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34539745204206323714818439 51809617806309485572227659)
    ·
      refine ⟨77714426709464228358341489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51809617806309485572227659 77714426709464228358341489)
      ·
        refine ⟨58285820032098171268756117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77714426709464228358341489 58285820032098171268756117)
        ·
          refine ⟨2732147814004601778222943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 58285820032098171268756117 2732147814004601778222943)
          ·
            refine ⟨4098221721006902667334415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2732147814004601778222943 4098221721006902667334415)
            ·
              refine ⟨6147332581510354001001623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4098221721006902667334415 6147332581510354001001623)
              ·
                refine ⟨9220998872265531001502435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6147332581510354001001623 9220998872265531001502435)
                ·
                  refine ⟨13831498308398296502253653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9220998872265531001502435 13831498308398296502253653)
                  ·
                    refine ⟨162087870801542537135785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13831498308398296502253653 162087870801542537135785)
                    ·
                      rfl

theorem cell23_946995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 8].length) (baseStart_946995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946995 prefixEnd_946995 := by exact prefixLift 946995
  have htrace : WordTrace (prefixWord ++ tailWord_946995) baseStart_946995 baseEnd_946995 := by
    simpa [prefixWord, tailWord_946995, baseEnd_946995] using wordTrace_append hprefix tailTrace_946995
  have hstable : (prefixWord ++ tailWord_946995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946995).length < 2 ^ (prefixWord ++ tailWord_946995).sum := by decide
  have hdescent : baseEnd_946995 < baseStart_946995 := by decide
  rcases family_descends (prefixWord ++ tailWord_946995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946996 : List Nat := [2, 5, 1, 1, 3, 1, 2, 1, 1, 3, 3]
def baseStart_946996 : Nat := 118140960795 + 946996 * 2 ^ 59
def prefixEnd_946996 : Nat := 4983230072969 + 3 ^ 40 * 946996 * 2
def baseEnd_946996 : Nat := 486264125885282107494851

theorem tailTrace_946996 : CollatzResearch.WordTrace tailWord_946996 prefixEnd_946996 486264125885282107494851 := by
  unfold tailWord_946996
  simp only [CollatzResearch.WordTrace]
  refine ⟨17269890838601350442802421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23026521118135133923736561 17269890838601350442802421)
  ·
    refine ⟨1619052266118876604012727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17269890838601350442802421 1619052266118876604012727)
    ·
      refine ⟨2428578399178314906019091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1619052266118876604012727 2428578399178314906019091)
      ·
        refine ⟨3642867598767472359028637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2428578399178314906019091 3642867598767472359028637)
        ·
          refine ⟨1366075349537802134635739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3642867598767472359028637 1366075349537802134635739)
          ·
            refine ⟨2049113024306703201953609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1366075349537802134635739 2049113024306703201953609)
            ·
              refine ⟨1536834768230027401465207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2049113024306703201953609 1536834768230027401465207)
              ·
                refine ⟨2305252152345041102197811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1536834768230027401465207 2305252152345041102197811)
                ·
                  refine ⟨3457878228517561653296717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2305252152345041102197811 3457878228517561653296717)
                  ·
                    refine ⟨1296704335694085619986269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3457878228517561653296717 1296704335694085619986269)
                    ·
                      refine ⟨486264125885282107494851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1296704335694085619986269 486264125885282107494851)
                      ·
                        rfl

theorem cell23_946996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_946996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_946996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_946996 prefixEnd_946996 := by exact prefixLift 946996
  have htrace : WordTrace (prefixWord ++ tailWord_946996) baseStart_946996 baseEnd_946996 := by
    simpa [prefixWord, tailWord_946996, baseEnd_946996] using wordTrace_append hprefix tailTrace_946996
  have hstable : (prefixWord ++ tailWord_946996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946996).length < 2 ^ (prefixWord ++ tailWord_946996).sum := by decide
  have hdescent : baseEnd_946996 < baseStart_946996 := by decide
  rcases family_descends (prefixWord ++ tailWord_946996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947015 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 4]
def baseStart_947015 : Nat := 118140960795 + 947015 * 2 ^ 59
def prefixEnd_947015 : Nat := 4983230072969 + 3 ^ 40 * 947015 * 2
def baseEnd_947015 : Nat := 486273882017717533157263

theorem tailTrace_947015 : CollatzResearch.WordTrace tailWord_947015 prefixEnd_947015 486273882017717533157263 := by
  unfold tailWord_947015
  simp only [CollatzResearch.WordTrace]
  refine ⟨34540474664133867130546499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23026983109422578087030999 34540474664133867130546499)
  ·
    refine ⟨51810711996200800695819749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34540474664133867130546499 51810711996200800695819749)
    ·
      refine ⟨9714508499287650130466203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51810711996200800695819749 9714508499287650130466203)
      ·
        refine ⟨14571762748931475195699305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9714508499287650130466203 14571762748931475195699305)
        ·
          refine ⟨10928822061698606396774479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14571762748931475195699305 10928822061698606396774479)
          ·
            refine ⟨16393233092547909595161719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10928822061698606396774479 16393233092547909595161719)
            ·
              refine ⟨24589849638821864392742579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16393233092547909595161719 24589849638821864392742579)
              ·
                refine ⟨36884774458232796589113869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24589849638821864392742579 36884774458232796589113869)
                ·
                  refine ⟨13831790421837298720917701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36884774458232796589113869 13831790421837298720917701)
                  ·
                    refine ⟨2593460704094493510172069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13831790421837298720917701 2593460704094493510172069)
                    ·
                      refine ⟨486273882017717533157263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2593460704094493510172069 486273882017717533157263)
                      ·
                        rfl

theorem cell23_947015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_947015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_947015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_947015 prefixEnd_947015 := by exact prefixLift 947015
  have htrace : WordTrace (prefixWord ++ tailWord_947015) baseStart_947015 baseEnd_947015 := by
    simpa [prefixWord, tailWord_947015, baseEnd_947015] using wordTrace_append hprefix tailTrace_947015
  have hstable : (prefixWord ++ tailWord_947015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947015).length < 2 ^ (prefixWord ++ tailWord_947015).sum := by decide
  have hdescent : baseEnd_947015 < baseStart_947015 := by decide
  rcases family_descends (prefixWord ++ tailWord_947015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947052 : List Nat := [2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 3]
def baseStart_947052 : Nat := 118140960795 + 947052 * 2 ^ 59
def prefixEnd_947052 : Nat := 4983230072969 + 3 ^ 40 * 947052 * 2
def baseEnd_947052 : Nat := 486292880801933888394593

theorem tailTrace_947052 : CollatzResearch.WordTrace tailWord_947052 prefixEnd_947052 486292880801933888394593 := by
  unfold tailWord_947052
  simp only [CollatzResearch.WordTrace]
  refine ⟨17270912082499911224821705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23027882776666548299762273 17270912082499911224821705)
  ·
    refine ⟨12953184061874933418616279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17270912082499911224821705 12953184061874933418616279)
    ·
      refine ⟨19429776092812400127924419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12953184061874933418616279 19429776092812400127924419)
      ·
        refine ⟨29144664139218600191886629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19429776092812400127924419 29144664139218600191886629)
        ·
          refine ⟨5464624526103487535978743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29144664139218600191886629 5464624526103487535978743)
          ·
            refine ⟨8196936789155231303968115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5464624526103487535978743 8196936789155231303968115)
            ·
              refine ⟨12295405183732846955952173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8196936789155231303968115 12295405183732846955952173)
              ·
                refine ⟨4610776943899817608482065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12295405183732846955952173 4610776943899817608482065)
                ·
                  refine ⟨3458082707924863206361549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4610776943899817608482065 3458082707924863206361549)
                  ·
                    refine ⟨1296781015471823702385581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3458082707924863206361549 1296781015471823702385581)
                    ·
                      refine ⟨486292880801933888394593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1296781015471823702385581 486292880801933888394593)
                      ·
                        rfl

theorem cell23_947052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 3].length) (baseStart_947052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_947052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_947052 prefixEnd_947052 := by exact prefixLift 947052
  have htrace : WordTrace (prefixWord ++ tailWord_947052) baseStart_947052 baseEnd_947052 := by
    simpa [prefixWord, tailWord_947052, baseEnd_947052] using wordTrace_append hprefix tailTrace_947052
  have hstable : (prefixWord ++ tailWord_947052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947052).length < 2 ^ (prefixWord ++ tailWord_947052).sum := by decide
  have hdescent : baseEnd_947052 < baseStart_947052 := by decide
  rcases family_descends (prefixWord ++ tailWord_947052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947129 : List Nat := [1, 2, 1, 4, 2, 2, 1, 3, 2, 2, 3]
def baseStart_947129 : Nat := 118140960795 + 947129 * 2 ^ 59
def prefixEnd_947129 : Nat := 4983230072969 + 3 ^ 40 * 947129 * 2
def baseEnd_947129 : Nat := 486332418812330087131739

theorem tailTrace_947129 : CollatzResearch.WordTrace tailWord_947129 prefixEnd_947129 486332418812330087131739 := by
  unfold tailWord_947129
  simp only [CollatzResearch.WordTrace]
  refine ⟨34544632585720864600196441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23029755057147243066797627 34544632585720864600196441)
  ·
    refine ⟨25908474439290648450147331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34544632585720864600196441 25908474439290648450147331)
    ·
      refine ⟨38862711658935972675220997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25908474439290648450147331 38862711658935972675220997)
      ·
        refine ⟨7286758436050494876603937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38862711658935972675220997 7286758436050494876603937)
        ·
          refine ⟨5465068827037871157452953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7286758436050494876603937 5465068827037871157452953)
          ·
            refine ⟨4098801620278403368089715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5465068827037871157452953 4098801620278403368089715)
            ·
              refine ⟨6148202430417605052134573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4098801620278403368089715 6148202430417605052134573)
              ·
                refine ⟨2305575911406601894550465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6148202430417605052134573 2305575911406601894550465)
                ·
                  refine ⟨1729181933554951420912849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2305575911406601894550465 1729181933554951420912849)
                  ·
                    refine ⟨1296886450166213565684637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1729181933554951420912849 1296886450166213565684637)
                    ·
                      refine ⟨486332418812330087131739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1296886450166213565684637 486332418812330087131739)
                      ·
                        rfl

theorem cell23_947129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_947129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_947129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_947129 prefixEnd_947129 := by exact prefixLift 947129
  have htrace : WordTrace (prefixWord ++ tailWord_947129) baseStart_947129 baseEnd_947129 := by
    simpa [prefixWord, tailWord_947129, baseEnd_947129] using wordTrace_append hprefix tailTrace_947129
  have hstable : (prefixWord ++ tailWord_947129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947129).length < 2 ^ (prefixWord ++ tailWord_947129).sum := by decide
  have hdescent : baseEnd_947129 < baseStart_947129 := by decide
  rcases family_descends (prefixWord ++ tailWord_947129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947169 : List Nat := [1, 2, 3, 1, 2, 1, 1, 4, 1, 5, 2]
def baseStart_947169 : Nat := 118140960795 + 947169 * 2 ^ 59
def prefixEnd_947169 : Nat := 4983230072969 + 3 ^ 40 * 947169 * 2
def baseEnd_947169 : Nat := 486352958038509930631555

theorem tailTrace_947169 : CollatzResearch.WordTrace tailWord_947169 prefixEnd_947169 486352958038509930631555 := by
  unfold tailWord_947169
  simp only [CollatzResearch.WordTrace]
  refine ⟨34546091505575951431652561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23030727670383967621101707 34546091505575951431652561)
  ·
    refine ⟨25909568629181963573739421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34546091505575951431652561 25909568629181963573739421)
    ·
      refine ⟨9716088235943236340152283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25909568629181963573739421 9716088235943236340152283)
      ·
        refine ⟨14574132353914854510228425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9716088235943236340152283 14574132353914854510228425)
        ·
          refine ⟨10930599265436140882671319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14574132353914854510228425 10930599265436140882671319)
          ·
            refine ⟨16395898898154211324006979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10930599265436140882671319 16395898898154211324006979)
            ·
              refine ⟨24593848347231316986010469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16395898898154211324006979 24593848347231316986010469)
              ·
                refine ⟨4611346565105871934876963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24593848347231316986010469 4611346565105871934876963)
                ·
                  refine ⟨6917019847658807902315445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4611346565105871934876963 6917019847658807902315445)
                  ·
                    refine ⟨648470610718013240842073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6917019847658807902315445 648470610718013240842073)
                    ·
                      refine ⟨486352958038509930631555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 648470610718013240842073 486352958038509930631555)
                      ·
                        rfl

theorem cell23_947169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 5, 2].length) (baseStart_947169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_947169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_947169 prefixEnd_947169 := by exact prefixLift 947169
  have htrace : WordTrace (prefixWord ++ tailWord_947169) baseStart_947169 baseEnd_947169 := by
    simpa [prefixWord, tailWord_947169, baseEnd_947169] using wordTrace_append hprefix tailTrace_947169
  have hstable : (prefixWord ++ tailWord_947169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947169).length < 2 ^ (prefixWord ++ tailWord_947169).sum := by decide
  have hdescent : baseEnd_947169 < baseStart_947169 := by decide
  rcases family_descends (prefixWord ++ tailWord_947169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947193 : List Nat := [1, 2, 1, 3, 1, 3, 4, 3, 1, 1, 3]
def baseStart_947193 : Nat := 118140960795 + 947193 * 2 ^ 59
def prefixEnd_947193 : Nat := 4983230072969 + 3 ^ 40 * 947193 * 2
def baseEnd_947193 : Nat := 486365281574217836731445

theorem tailTrace_947193 : CollatzResearch.WordTrace tailWord_947193 prefixEnd_947193 486365281574217836731445 := by
  unfold tailWord_947193
  simp only [CollatzResearch.WordTrace]
  refine ⟨34546966857489003530526233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23031311238326002353684155 34546966857489003530526233)
  ·
    refine ⟨25910225143116752647894675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34546966857489003530526233 25910225143116752647894675)
    ·
      refine ⟨38865337714675128971842013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25910225143116752647894675 38865337714675128971842013)
      ·
        refine ⟨14574501643003173364440755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38865337714675128971842013 14574501643003173364440755)
        ·
          refine ⟨21861752464504760046661133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14574501643003173364440755 21861752464504760046661133)
          ·
            refine ⟨8198157174189285017497925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21861752464504760046661133 8198157174189285017497925)
            ·
              refine ⟨1537154470160490940780861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8198157174189285017497925 1537154470160490940780861)
              ·
                refine ⟨576432926310184102792823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1537154470160490940780861 576432926310184102792823)
                ·
                  refine ⟨864649389465276154189235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 576432926310184102792823 864649389465276154189235)
                  ·
                    refine ⟨1296974084197914231283853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 864649389465276154189235 1296974084197914231283853)
                    ·
                      refine ⟨486365281574217836731445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1296974084197914231283853 486365281574217836731445)
                      ·
                        rfl

theorem cell23_947193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 3, 1, 1, 3].length) (baseStart_947193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_947193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_947193 prefixEnd_947193 := by exact prefixLift 947193
  have htrace : WordTrace (prefixWord ++ tailWord_947193) baseStart_947193 baseEnd_947193 := by
    simpa [prefixWord, tailWord_947193, baseEnd_947193] using wordTrace_append hprefix tailTrace_947193
  have hstable : (prefixWord ++ tailWord_947193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947193).length < 2 ^ (prefixWord ++ tailWord_947193).sum := by decide
  have hdescent : baseEnd_947193 < baseStart_947193 := by decide
  rcases family_descends (prefixWord ++ tailWord_947193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947196 : List Nat := [2, 2, 2, 1, 2, 3, 4, 1, 1, 5]
def baseStart_947196 : Nat := 118140960795 + 947196 * 2 ^ 59
def prefixEnd_947196 : Nat := 4983230072969 + 3 ^ 40 * 947196 * 2
def baseEnd_947196 : Nat := 162122274005393774997977

theorem tailTrace_947196 : CollatzResearch.WordTrace tailWord_947196 prefixEnd_947196 162122274005393774997977 := by
  unfold tailWord_947196
  simp only [CollatzResearch.WordTrace]
  refine ⟨17273538138239067521442721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23031384184318756695256961 17273538138239067521442721)
  ·
    refine ⟨12955153603679300641082041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17273538138239067521442721 12955153603679300641082041)
    ·
      refine ⟨9716365202759475480811531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12955153603679300641082041 9716365202759475480811531)
      ·
        refine ⟨14574547804139213221217297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9716365202759475480811531 14574547804139213221217297)
        ·
          refine ⟨10930910853104409915912973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14574547804139213221217297 10930910853104409915912973)
          ·
            refine ⟨4099091569914153718467365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10930910853104409915912973 4099091569914153718467365)
            ·
              refine ⟨768579669358903822212631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4099091569914153718467365 768579669358903822212631)
              ·
                refine ⟨1152869504038355733318947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 768579669358903822212631 1152869504038355733318947)
                ·
                  refine ⟨1729304256057533599978421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1152869504038355733318947 1729304256057533599978421)
                  ·
                    refine ⟨162122274005393774997977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1729304256057533599978421 162122274005393774997977)
                    ·
                      rfl

theorem cell23_947196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 1, 5].length) (baseStart_947196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_947196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_947196 prefixEnd_947196 := by exact prefixLift 947196
  have htrace : WordTrace (prefixWord ++ tailWord_947196) baseStart_947196 baseEnd_947196 := by
    simpa [prefixWord, tailWord_947196, baseEnd_947196] using wordTrace_append hprefix tailTrace_947196
  have hstable : (prefixWord ++ tailWord_947196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947196).length < 2 ^ (prefixWord ++ tailWord_947196).sum := by decide
  have hdescent : baseEnd_947196 < baseStart_947196 := by decide
  rcases family_descends (prefixWord ++ tailWord_947196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947233 : List Nat := [1, 2, 3, 2, 3, 1, 2, 2, 3, 2, 2]
def baseStart_947233 : Nat := 118140960795 + 947233 * 2 ^ 59
def prefixEnd_947233 : Nat := 4983230072969 + 3 ^ 40 * 947233 * 2
def baseEnd_947233 : Nat := 486385820800397680231261

theorem tailTrace_947233 : CollatzResearch.WordTrace tailWord_947233 prefixEnd_947233 486385820800397680231261 := by
  unfold tailWord_947233
  simp only [CollatzResearch.WordTrace]
  refine ⟨34548425777344090361982353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23032283851562726907988235 34548425777344090361982353)
  ·
    refine ⟨25911319333008067771486765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34548425777344090361982353 25911319333008067771486765)
    ·
      refine ⟨9716744749878025414307537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25911319333008067771486765 9716744749878025414307537)
      ·
        refine ⟨7287558562408519060730653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9716744749878025414307537 7287558562408519060730653)
        ·
          refine ⟨2732834460903194647773995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7287558562408519060730653 2732834460903194647773995)
          ·
            refine ⟨4099251691354791971660993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2732834460903194647773995 4099251691354791971660993)
            ·
              refine ⟨3074438768516093978745745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4099251691354791971660993 3074438768516093978745745)
              ·
                refine ⟨2305829076387070484059309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3074438768516093978745745 2305829076387070484059309)
                ·
                  refine ⟨864685903645151431522241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2305829076387070484059309 864685903645151431522241)
                  ·
                    refine ⟨648514427733863573641681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 864685903645151431522241 648514427733863573641681)
                    ·
                      refine ⟨486385820800397680231261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 648514427733863573641681 486385820800397680231261)
                      ·
                        rfl

theorem cell23_947233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_947233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_947233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_947233 prefixEnd_947233 := by exact prefixLift 947233
  have htrace : WordTrace (prefixWord ++ tailWord_947233) baseStart_947233 baseEnd_947233 := by
    simpa [prefixWord, tailWord_947233, baseEnd_947233] using wordTrace_append hprefix tailTrace_947233
  have hstable : (prefixWord ++ tailWord_947233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947233).length < 2 ^ (prefixWord ++ tailWord_947233).sum := by decide
  have hdescent : baseEnd_947233 < baseStart_947233 := by decide
  rcases family_descends (prefixWord ++ tailWord_947233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947249 : List Nat := [1, 2, 2, 3, 1, 2, 2, 1, 3, 3, 3]
def baseStart_947249 : Nat := 118140960795 + 947249 * 2 ^ 59
def prefixEnd_947249 : Nat := 4983230072969 + 3 ^ 40 * 947249 * 2
def baseEnd_947249 : Nat := 486394036490869617631187

theorem tailTrace_947249 : CollatzResearch.WordTrace tailWord_947249 prefixEnd_947249 486394036490869617631187 := by
  unfold tailWord_947249
  simp only [CollatzResearch.WordTrace]
  refine ⟨34549009345286125094564801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23032672896857416729709867 34549009345286125094564801)
  ·
    refine ⟨25911757008964593820923601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34549009345286125094564801 25911757008964593820923601)
    ·
      refine ⟨19433817756723445365692701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25911757008964593820923601 19433817756723445365692701)
      ·
        refine ⟨7287681658771292012134763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19433817756723445365692701 7287681658771292012134763)
        ·
          refine ⟨10931522488156938018202145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7287681658771292012134763 10931522488156938018202145)
          ·
            refine ⟨8198641866117703513651609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10931522488156938018202145 8198641866117703513651609)
            ·
              refine ⟨6148981399588277635238707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8198641866117703513651609 6148981399588277635238707)
              ·
                refine ⟨9223472099382416452858061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6148981399588277635238707 9223472099382416452858061)
                ·
                  refine ⟨3458802037268406169821773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9223472099382416452858061 3458802037268406169821773)
                  ·
                    refine ⟨1297050763975652313683165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3458802037268406169821773 1297050763975652313683165)
                    ·
                      refine ⟨486394036490869617631187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1297050763975652313683165 486394036490869617631187)
                      ·
                        rfl

theorem cell23_947249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_947249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_947249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_947249 prefixEnd_947249 := by exact prefixLift 947249
  have htrace : WordTrace (prefixWord ++ tailWord_947249) baseStart_947249 baseEnd_947249 := by
    simpa [prefixWord, tailWord_947249, baseEnd_947249] using wordTrace_append hprefix tailTrace_947249
  have hstable : (prefixWord ++ tailWord_947249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947249).length < 2 ^ (prefixWord ++ tailWord_947249).sum := by decide
  have hdescent : baseEnd_947249 < baseStart_947249 := by decide
  rcases family_descends (prefixWord ++ tailWord_947249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947276 : List Nat := [2, 2, 1, 3, 1, 1, 1, 4, 3, 3, 2]
def baseStart_947276 : Nat := 118140960795 + 947276 * 2 ^ 59
def prefixEnd_947276 : Nat := 4983230072969 + 3 ^ 40 * 947276 * 2
def baseEnd_947276 : Nat := 486407900468541011993563

theorem tailTrace_947276 : CollatzResearch.WordTrace tailWord_947276 prefixEnd_947276 486407900468541011993563 := by
  unfold tailWord_947276
  simp only [CollatzResearch.WordTrace]
  refine ⟨17274997058094154352898841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23033329410792205803865121 17274997058094154352898841)
  ·
    refine ⟨12956247793570615764674131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17274997058094154352898841 12956247793570615764674131)
    ·
      refine ⟨19434371690355923647011197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12956247793570615764674131 19434371690355923647011197)
      ·
        refine ⟨7287889383883471367629199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19434371690355923647011197 7287889383883471367629199)
        ·
          refine ⟨10931834075825207051443799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7287889383883471367629199 10931834075825207051443799)
          ·
            refine ⟨16397751113737810577165699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10931834075825207051443799 16397751113737810577165699)
            ·
              refine ⟨24596626670606715865748549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16397751113737810577165699 24596626670606715865748549)
              ·
                refine ⟨4611867500738759224827853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24596626670606715865748549 4611867500738759224827853)
                ·
                  refine ⟨1729450312777034709310445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4611867500738759224827853 1729450312777034709310445)
                  ·
                    refine ⟨648543867291388015991417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1729450312777034709310445 648543867291388015991417)
                    ·
                      refine ⟨486407900468541011993563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 648543867291388015991417 486407900468541011993563)
                      ·
                        rfl

theorem cell23_947276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_947276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_947276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_947276 prefixEnd_947276 := by exact prefixLift 947276
  have htrace : WordTrace (prefixWord ++ tailWord_947276) baseStart_947276 baseEnd_947276 := by
    simpa [prefixWord, tailWord_947276, baseEnd_947276] using wordTrace_append hprefix tailTrace_947276
  have hstable : (prefixWord ++ tailWord_947276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947276).length < 2 ^ (prefixWord ++ tailWord_947276).sum := by decide
  have hdescent : baseEnd_947276 < baseStart_947276 := by decide
  rcases family_descends (prefixWord ++ tailWord_947276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947317 : List Nat := [1, 3, 4, 3, 1, 1, 2, 2, 2, 1, 3]
def baseStart_947317 : Nat := 118140960795 + 947317 * 2 ^ 59
def prefixEnd_947317 : Nat := 4983230072969 + 3 ^ 40 * 947317 * 2
def baseEnd_947317 : Nat := 486428953175375351580875

theorem tailTrace_947317 : CollatzResearch.WordTrace tailWord_947317 prefixEnd_947317 486428953175375351580875 := by
  unfold tailWord_947317
  simp only [CollatzResearch.WordTrace]
  refine ⟨34551489509039772708040205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23034326339359848472026803 34551489509039772708040205)
  ·
    refine ⟨12956808565889914765515077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34551489509039772708040205 12956808565889914765515077)
    ·
      refine ⟨2429401606104359018534077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12956808565889914765515077 2429401606104359018534077)
      ·
        refine ⟨911025602289134631950279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2429401606104359018534077 911025602289134631950279)
        ·
          refine ⟨1366538403433701947925419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 911025602289134631950279 1366538403433701947925419)
          ·
            refine ⟨2049807605150552921888129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1366538403433701947925419 2049807605150552921888129)
            ·
              refine ⟨1537355703862914691416097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2049807605150552921888129 1537355703862914691416097)
              ·
                refine ⟨1153016777897186018562073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1537355703862914691416097 1153016777897186018562073)
                ·
                  refine ⟨864762583422889513921555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1153016777897186018562073 864762583422889513921555)
                  ·
                    refine ⟨1297143875134334270882333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 864762583422889513921555 1297143875134334270882333)
                    ·
                      refine ⟨486428953175375351580875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1297143875134334270882333 486428953175375351580875)
                      ·
                        rfl

theorem cell23_947317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_947317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_947317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_947317 prefixEnd_947317 := by exact prefixLift 947317
  have htrace : WordTrace (prefixWord ++ tailWord_947317) baseStart_947317 baseEnd_947317 := by
    simpa [prefixWord, tailWord_947317, baseEnd_947317] using wordTrace_append hprefix tailTrace_947317
  have hstable : (prefixWord ++ tailWord_947317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947317).length < 2 ^ (prefixWord ++ tailWord_947317).sum := by decide
  have hdescent : baseEnd_947317 < baseStart_947317 := by decide
  rcases family_descends (prefixWord ++ tailWord_947317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947319 : List Nat := [1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 4]
def baseStart_947319 : Nat := 118140960795 + 947319 * 2 ^ 59
def prefixEnd_947319 : Nat := 4983230072969 + 3 ^ 40 * 947319 * 2
def baseEnd_947319 : Nat := 486429980136684343755865

theorem tailTrace_947319 : CollatzResearch.WordTrace tailWord_947319 prefixEnd_947319 486429980136684343755865 := by
  unfold tailWord_947319
  simp only [CollatzResearch.WordTrace]
  refine ⟨34551562455032527049613011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23034374970021684699742007 34551562455032527049613011)
  ·
    refine ⟨51827343682548790574419517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34551562455032527049613011 51827343682548790574419517)
    ·
      refine ⟨19435253880955796465407319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51827343682548790574419517 19435253880955796465407319)
      ·
        refine ⟨29152880821433694698110979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19435253880955796465407319 29152880821433694698110979)
        ·
          refine ⟨43729321232150542047166469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29152880821433694698110979 43729321232150542047166469)
          ·
            refine ⟨8199247731028226633843713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43729321232150542047166469 8199247731028226633843713)
            ·
              refine ⟨6149435798271169975382785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8199247731028226633843713 6149435798271169975382785)
              ·
                refine ⟨4612076848703377481537089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6149435798271169975382785 4612076848703377481537089)
                ·
                  refine ⟨3459057636527533111152817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4612076848703377481537089 3459057636527533111152817)
                  ·
                    refine ⟨2594293227395649833364613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3459057636527533111152817 2594293227395649833364613)
                    ·
                      refine ⟨486429980136684343755865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2594293227395649833364613 486429980136684343755865)
                      ·
                        rfl

theorem cell23_947319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_947319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_947319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_947319 prefixEnd_947319 := by exact prefixLift 947319
  have htrace : WordTrace (prefixWord ++ tailWord_947319) baseStart_947319 baseEnd_947319 := by
    simpa [prefixWord, tailWord_947319, baseEnd_947319] using wordTrace_append hprefix tailTrace_947319
  have hstable : (prefixWord ++ tailWord_947319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947319).length < 2 ^ (prefixWord ++ tailWord_947319).sum := by decide
  have hdescent : baseEnd_947319 < baseStart_947319 := by decide
  rcases family_descends (prefixWord ++ tailWord_947319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947346 : List Nat := [3, 2, 3, 1, 1, 3, 1, 2, 7]
def baseStart_947346 : Nat := 118140960795 + 947346 * 2 ^ 59
def prefixEnd_947346 : Nat := 4983230072969 + 3 ^ 40 * 947346 * 2
def baseEnd_947346 : Nat := 54049316012706193124249

theorem tailTrace_947346 : CollatzResearch.WordTrace tailWord_947346 prefixEnd_947346 54049316012706193124249 := by
  unfold tailWord_947346
  simp only [CollatzResearch.WordTrace]
  refine ⟨8638136806483677665211473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23035031483956473773897261 8638136806483677665211473)
  ·
    refine ⟨6478602604862758248908605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8638136806483677665211473 6478602604862758248908605)
    ·
      refine ⟨2429475976823534343340727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6478602604862758248908605 2429475976823534343340727)
      ·
        refine ⟨3644213965235301515011091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2429475976823534343340727 3644213965235301515011091)
        ·
          refine ⟨5466320947852952272516637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3644213965235301515011091 5466320947852952272516637)
          ·
            refine ⟨2049870355444857102193739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5466320947852952272516637 2049870355444857102193739)
            ·
              refine ⟨3074805533167285653290609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2049870355444857102193739 3074805533167285653290609)
              ·
                refine ⟨2306104149875464239967957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3074805533167285653290609 2306104149875464239967957)
                ·
                  refine ⟨54049316012706193124249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2306104149875464239967957 54049316012706193124249)
                  ·
                    rfl

theorem cell23_947346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 7].length) (baseStart_947346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_947346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_947346 prefixEnd_947346 := by exact prefixLift 947346
  have htrace : WordTrace (prefixWord ++ tailWord_947346) baseStart_947346 baseEnd_947346 := by
    simpa [prefixWord, tailWord_947346, baseEnd_947346] using wordTrace_append hprefix tailTrace_947346
  have hstable : (prefixWord ++ tailWord_947346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947346).length < 2 ^ (prefixWord ++ tailWord_947346).sum := by decide
  have hdescent : baseEnd_947346 < baseStart_947346 := by decide
  rcases family_descends (prefixWord ++ tailWord_947346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947409 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 1, 6, 4]
def baseStart_947409 : Nat := 118140960795 + 947409 * 2 ^ 59
def prefixEnd_947409 : Nat := 4983230072969 + 3 ^ 40 * 947409 * 2
def baseEnd_947409 : Nat := 486476193395588991630451

theorem tailTrace_947409 : CollatzResearch.WordTrace tailWord_947409 prefixEnd_947409 486476193395588991630451 := by
  unfold tailWord_947409
  simp only [CollatzResearch.WordTrace]
  refine ⟨34554845024706472420389281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23036563349804314946926187 34554845024706472420389281)
  ·
    refine ⟨25916133768529854315291961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34554845024706472420389281 25916133768529854315291961)
    ·
      refine ⟨19437100326397390736468971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25916133768529854315291961 19437100326397390736468971)
      ·
        refine ⟨29155650489596086104703457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19437100326397390736468971 29155650489596086104703457)
        ·
          refine ⟨21866737867197064578527593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29155650489596086104703457 21866737867197064578527593)
          ·
            refine ⟨16400053400397798433895695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21866737867197064578527593 16400053400397798433895695)
            ·
              refine ⟨24600080100596697650843543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16400053400397798433895695 24600080100596697650843543)
              ·
                refine ⟨36900120150895046476265315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24600080100596697650843543 36900120150895046476265315)
                ·
                  refine ⟨55350180226342569714397973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36900120150895046476265315 55350180226342569714397973)
                  ·
                    refine ⟨2594539698109807955362405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55350180226342569714397973 2594539698109807955362405)
                    ·
                      refine ⟨486476193395588991630451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2594539698109807955362405 486476193395588991630451)
                      ·
                        rfl

theorem cell23_947409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_947409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_947409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_947409 prefixEnd_947409 := by exact prefixLift 947409
  have htrace : WordTrace (prefixWord ++ tailWord_947409) baseStart_947409 baseEnd_947409 := by
    simpa [prefixWord, tailWord_947409, baseEnd_947409] using wordTrace_append hprefix tailTrace_947409
  have hstable : (prefixWord ++ tailWord_947409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947409).length < 2 ^ (prefixWord ++ tailWord_947409).sum := by decide
  have hdescent : baseEnd_947409 < baseStart_947409 := by decide
  rcases family_descends (prefixWord ++ tailWord_947409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947414 : List Nat := [5, 2, 1, 2, 3, 1, 1, 3, 5]
def baseStart_947414 : Nat := 118140960795 + 947414 * 2 ^ 59
def prefixEnd_947414 : Nat := 4983230072969 + 3 ^ 40 * 947414 * 2
def baseEnd_947414 : Nat := 54053195644317941340881

theorem tailTrace_947414 : CollatzResearch.WordTrace tailWord_947414 prefixEnd_947414 54053195644317941340881 := by
  unfold tailWord_947414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2159689211855522392145081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23036684926458905516214197 2159689211855522392145081)
  ·
    refine ⟨1619766908891641794108811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2159689211855522392145081 1619766908891641794108811)
    ·
      refine ⟨2429650363337462691163217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1619766908891641794108811 2429650363337462691163217)
      ·
        refine ⟨1822237772503097018372413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2429650363337462691163217 1822237772503097018372413)
        ·
          refine ⟨683339164688661381889655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1822237772503097018372413 683339164688661381889655)
          ·
            refine ⟨1025008747032992072834483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 683339164688661381889655 1025008747032992072834483)
            ·
              refine ⟨1537513120549488109251725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1025008747032992072834483 1537513120549488109251725)
              ·
                refine ⟨576567420206058040969397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1537513120549488109251725 576567420206058040969397)
                ·
                  refine ⟨54053195644317941340881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 576567420206058040969397 54053195644317941340881)
                  ·
                    rfl

theorem cell23_947414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_947414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_947414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_947414 prefixEnd_947414 := by exact prefixLift 947414
  have htrace : WordTrace (prefixWord ++ tailWord_947414) baseStart_947414 baseEnd_947414 := by
    simpa [prefixWord, tailWord_947414, baseEnd_947414] using wordTrace_append hprefix tailTrace_947414
  have hstable : (prefixWord ++ tailWord_947414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947414).length < 2 ^ (prefixWord ++ tailWord_947414).sum := by decide
  have hdescent : baseEnd_947414 < baseStart_947414 := by decide
  rcases family_descends (prefixWord ++ tailWord_947414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947520 : List Nat := [2, 1, 1, 2, 2, 1, 5, 2, 3, 2, 2]
def baseStart_947520 : Nat := 118140960795 + 947520 * 2 ^ 59
def prefixEnd_947520 : Nat := 4983230072969 + 3 ^ 40 * 947520 * 2
def baseEnd_947520 : Nat := 486533189748238057342441

theorem tailTrace_947520 : CollatzResearch.WordTrace tailWord_947520 prefixEnd_947520 486533189748238057342441 := by
  unfold tailWord_947520
  simp only [CollatzResearch.WordTrace]
  refine ⟨17279446763652169188840007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23039262351536225585120009 17279446763652169188840007)
  ·
    refine ⟨25919170145478253783260011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17279446763652169188840007 25919170145478253783260011)
    ·
      refine ⟨38878755218217380674890017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25919170145478253783260011 38878755218217380674890017)
      ·
        refine ⟨29159066413663035506167513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38878755218217380674890017 29159066413663035506167513)
        ·
          refine ⟨21869299810247276629625635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29159066413663035506167513 21869299810247276629625635)
          ·
            refine ⟨32803949715370914944438453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21869299810247276629625635 32803949715370914944438453)
            ·
              refine ⟨3075370285816023276041105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32803949715370914944438453 3075370285816023276041105)
              ·
                refine ⟨2306527714362017457030829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3075370285816023276041105 2306527714362017457030829)
                ·
                  refine ⟨864947892885756546386561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2306527714362017457030829 864947892885756546386561)
                  ·
                    refine ⟨648710919664317409789921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 864947892885756546386561 648710919664317409789921)
                    ·
                      refine ⟨486533189748238057342441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 648710919664317409789921 486533189748238057342441)
                      ·
                        rfl

theorem cell23_947520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 3, 2, 2].length) (baseStart_947520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_947520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_947520 prefixEnd_947520 := by exact prefixLift 947520
  have htrace : WordTrace (prefixWord ++ tailWord_947520) baseStart_947520 baseEnd_947520 := by
    simpa [prefixWord, tailWord_947520, baseEnd_947520] using wordTrace_append hprefix tailTrace_947520
  have hstable : (prefixWord ++ tailWord_947520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947520).length < 2 ^ (prefixWord ++ tailWord_947520).sum := by decide
  have hdescent : baseEnd_947520 < baseStart_947520 := by decide
  rcases family_descends (prefixWord ++ tailWord_947520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947523 : List Nat := [1, 1, 1, 3, 1, 3, 1, 6, 1, 2, 3]
def baseStart_947523 : Nat := 118140960795 + 947523 * 2 ^ 59
def prefixEnd_947523 : Nat := 4983230072969 + 3 ^ 40 * 947523 * 2
def baseEnd_947523 : Nat := 486534730190201545604927

theorem tailTrace_947523 : CollatzResearch.WordTrace tailWord_947523 prefixEnd_947523 486534730190201545604927 := by
  unfold tailWord_947523
  simp only [CollatzResearch.WordTrace]
  refine ⟨34559002946293469890039223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23039335297528979926692815 34559002946293469890039223)
  ·
    refine ⟨51838504419440204835058835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34559002946293469890039223 51838504419440204835058835)
    ·
      refine ⟨77757756629160307252588253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51838504419440204835058835 77757756629160307252588253)
      ·
        refine ⟨29159158735935115219720595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77757756629160307252588253 29159158735935115219720595)
        ·
          refine ⟨43738738103902672829580893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29159158735935115219720595 43738738103902672829580893)
          ·
            refine ⟨16402026788963502311092835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43738738103902672829580893 16402026788963502311092835)
            ·
              refine ⟨24603040183445253466639253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16402026788963502311092835 24603040183445253466639253)
              ·
                refine ⟨1153267508598996256248715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24603040183445253466639253 1153267508598996256248715)
                ·
                  refine ⟨1729901262898494384373073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1153267508598996256248715 1729901262898494384373073)
                  ·
                    refine ⟨1297425947173870788279805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1729901262898494384373073 1297425947173870788279805)
                    ·
                      refine ⟨486534730190201545604927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1297425947173870788279805 486534730190201545604927)
                      ·
                        rfl

theorem cell23_947523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 2, 3].length) (baseStart_947523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_947523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_947523 prefixEnd_947523 := by exact prefixLift 947523
  have htrace : WordTrace (prefixWord ++ tailWord_947523) baseStart_947523 baseEnd_947523 := by
    simpa [prefixWord, tailWord_947523, baseEnd_947523] using wordTrace_append hprefix tailTrace_947523
  have hstable : (prefixWord ++ tailWord_947523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947523).length < 2 ^ (prefixWord ++ tailWord_947523).sum := by decide
  have hdescent : baseEnd_947523 < baseStart_947523 := by decide
  rcases family_descends (prefixWord ++ tailWord_947523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947524 : List Nat := [2, 3, 4, 1, 1, 3, 1, 1, 2, 3, 2]
def baseStart_947524 : Nat := 118140960795 + 947524 * 2 ^ 59
def prefixEnd_947524 : Nat := 4983230072969 + 3 ^ 40 * 947524 * 2
def baseEnd_947524 : Nat := 486535243670856041692423

theorem tailTrace_947524 : CollatzResearch.WordTrace tailWord_947524 prefixEnd_947524 486535243670856041692423 := by
  unfold tailWord_947524
  simp only [CollatzResearch.WordTrace]
  refine ⟨17279519709644923530412813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23039359612859898040550417 17279519709644923530412813)
  ·
    refine ⟨6479819891116846323904805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17279519709644923530412813 6479819891116846323904805)
    ·
      refine ⟨1214966229584408685732151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6479819891116846323904805 1214966229584408685732151)
      ·
        refine ⟨1822449344376613028598227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1214966229584408685732151 1822449344376613028598227)
        ·
          refine ⟨2733674016564919542897341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1822449344376613028598227 2733674016564919542897341)
          ·
            refine ⟨1025127756211844828586503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2733674016564919542897341 1025127756211844828586503)
            ·
              refine ⟨1537691634317767242879755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1025127756211844828586503 1537691634317767242879755)
              ·
                refine ⟨2306537451476650864319633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1537691634317767242879755 2306537451476650864319633)
                ·
                  refine ⟨1729903088607488148239725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2306537451476650864319633 1729903088607488148239725)
                  ·
                    refine ⟨648713658227808055589897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1729903088607488148239725 648713658227808055589897)
                    ·
                      refine ⟨486535243670856041692423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 648713658227808055589897 486535243670856041692423)
                      ·
                        rfl

theorem cell23_947524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_947524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_947524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_947524 prefixEnd_947524 := by exact prefixLift 947524
  have htrace : WordTrace (prefixWord ++ tailWord_947524) baseStart_947524 baseEnd_947524 := by
    simpa [prefixWord, tailWord_947524, baseEnd_947524] using wordTrace_append hprefix tailTrace_947524
  have hstable : (prefixWord ++ tailWord_947524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947524).length < 2 ^ (prefixWord ++ tailWord_947524).sum := by decide
  have hdescent : baseEnd_947524 < baseStart_947524 := by decide
  rcases family_descends (prefixWord ++ tailWord_947524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947540 : List Nat := [2, 4, 1, 1, 2, 1, 3, 3, 1, 2, 3]
def baseStart_947540 : Nat := 118140960795 + 947540 * 2 ^ 59
def prefixEnd_947540 : Nat := 4983230072969 + 3 ^ 40 * 947540 * 2
def baseEnd_947540 : Nat := 486543459361327979092349

theorem tailTrace_947540 : CollatzResearch.WordTrace tailWord_947540 prefixEnd_947540 486543459361327979092349 := by
  unfold tailWord_947540
  simp only [CollatzResearch.WordTrace]
  refine ⟨17279811493615940896704037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23039748658154587862272049 17279811493615940896704037)
  ·
    refine ⟨3239964655052988918132007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17279811493615940896704037 3239964655052988918132007)
    ·
      refine ⟨4859946982579483377198011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3239964655052988918132007 4859946982579483377198011)
      ·
        refine ⟨7289920473869225065797017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4859946982579483377198011 7289920473869225065797017)
        ·
          refine ⟨5467440355401918799347763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7289920473869225065797017 5467440355401918799347763)
          ·
            refine ⟨8201160533102878199021645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5467440355401918799347763 8201160533102878199021645)
            ·
              refine ⟨3075435199913579324633117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8201160533102878199021645 3075435199913579324633117)
              ·
                refine ⟨1153288199967592246737419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3075435199913579324633117 1153288199967592246737419)
                ·
                  refine ⟨1729932299951388370106129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1153288199967592246737419 1729932299951388370106129)
                  ·
                    refine ⟨1297449224963541277579597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1729932299951388370106129 1297449224963541277579597)
                    ·
                      refine ⟨486543459361327979092349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1297449224963541277579597 486543459361327979092349)
                      ·
                        rfl

theorem cell23_947540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_947540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_947540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_947540 prefixEnd_947540 := by exact prefixLift 947540
  have htrace : WordTrace (prefixWord ++ tailWord_947540) baseStart_947540 baseEnd_947540 := by
    simpa [prefixWord, tailWord_947540, baseEnd_947540] using wordTrace_append hprefix tailTrace_947540
  have hstable : (prefixWord ++ tailWord_947540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947540).length < 2 ^ (prefixWord ++ tailWord_947540).sum := by decide
  have hdescent : baseEnd_947540 < baseStart_947540 := by decide
  rcases family_descends (prefixWord ++ tailWord_947540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947554 : List Nat := [3, 3, 2, 1, 1, 1, 1, 6, 1, 2, 2]
def baseStart_947554 : Nat := 118140960795 + 947554 * 2 ^ 59
def prefixEnd_947554 : Nat := 4983230072969 + 3 ^ 40 * 947554 * 2
def baseEnd_947554 : Nat := 486550648090490924317285

theorem tailTrace_947554 : CollatzResearch.WordTrace tailWord_947554 prefixEnd_947554 486550648090490924317285 := by
  unfold tailWord_947554
  simp only [CollatzResearch.WordTrace]
  refine ⟨8640033402295290546104429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23040089072787441456278477 8640033402295290546104429)
  ·
    refine ⟨3240012525860733954789161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8640033402295290546104429 3240012525860733954789161)
    ·
      refine ⟨2430009394395550466091871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3240012525860733954789161 2430009394395550466091871)
      ·
        refine ⟨3645014091593325699137807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2430009394395550466091871 3645014091593325699137807)
        ·
          refine ⟨5467521137389988548706711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3645014091593325699137807 5467521137389988548706711)
          ·
            refine ⟨8201281706084982823060067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5467521137389988548706711 8201281706084982823060067)
            ·
              refine ⟨12301922559127474234590101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8201281706084982823060067 12301922559127474234590101)
              ·
                refine ⟨576652619959100354746411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12301922559127474234590101 576652619959100354746411)
                ·
                  refine ⟨864978929938650532119617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 576652619959100354746411 864978929938650532119617)
                  ·
                    refine ⟨648734197453987899089713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 864978929938650532119617 648734197453987899089713)
                    ·
                      refine ⟨486550648090490924317285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 648734197453987899089713 486550648090490924317285)
                      ·
                        rfl

theorem cell23_947554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_947554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_947554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_947554 prefixEnd_947554 := by exact prefixLift 947554
  have htrace : WordTrace (prefixWord ++ tailWord_947554) baseStart_947554 baseEnd_947554 := by
    simpa [prefixWord, tailWord_947554, baseEnd_947554] using wordTrace_append hprefix tailTrace_947554
  have hstable : (prefixWord ++ tailWord_947554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947554).length < 2 ^ (prefixWord ++ tailWord_947554).sum := by decide
  have hdescent : baseEnd_947554 < baseStart_947554 := by decide
  rcases family_descends (prefixWord ++ tailWord_947554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947623 : List Nat := [1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 4]
def baseStart_947623 : Nat := 118140960795 + 947623 * 2 ^ 59
def prefixEnd_947623 : Nat := 4983230072969 + 3 ^ 40 * 947623 * 2
def baseEnd_947623 : Nat := 486586078255651154354467

theorem tailTrace_947623 : CollatzResearch.WordTrace tailWord_947623 prefixEnd_947623 486586078255651154354467 := by
  unfold tailWord_947623
  simp only [CollatzResearch.WordTrace]
  refine ⟨34562650245931186968679523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23041766830620791312453015 34562650245931186968679523)
  ·
    refine ⟨51843975368896780453019285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34562650245931186968679523 51843975368896780453019285)
    ·
      refine ⟨2430186345417036583735279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51843975368896780453019285 2430186345417036583735279)
      ·
        refine ⟨3645279518125554875602919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2430186345417036583735279 3645279518125554875602919)
        ·
          refine ⟨5467919277188332313404379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3645279518125554875602919 5467919277188332313404379)
          ·
            refine ⟨8201878915782498470106569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5467919277188332313404379 8201878915782498470106569)
            ·
              refine ⟨6151409186836873852579927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8201878915782498470106569 6151409186836873852579927)
              ·
                refine ⟨9227113780255310778869891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6151409186836873852579927 9227113780255310778869891)
                ·
                  refine ⟨13840670670382966168304837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9227113780255310778869891 13840670670382966168304837)
                  ·
                    refine ⟨2595125750696806156557157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13840670670382966168304837 2595125750696806156557157)
                    ·
                      refine ⟨486586078255651154354467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2595125750696806156557157 486586078255651154354467)
                      ·
                        rfl

theorem cell23_947623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_947623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_947623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_947623 prefixEnd_947623 := by exact prefixLift 947623
  have htrace : WordTrace (prefixWord ++ tailWord_947623) baseStart_947623 baseEnd_947623 := by
    simpa [prefixWord, tailWord_947623, baseEnd_947623] using wordTrace_append hprefix tailTrace_947623
  have hstable : (prefixWord ++ tailWord_947623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947623).length < 2 ^ (prefixWord ++ tailWord_947623).sum := by decide
  have hdescent : baseEnd_947623 < baseStart_947623 := by decide
  rcases family_descends (prefixWord ++ tailWord_947623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947663 : List Nat := [1, 1, 2, 1, 1, 4, 4, 2, 2, 5]
def baseStart_947663 : Nat := 118140960795 + 947663 * 2 ^ 59
def prefixEnd_947663 : Nat := 4983230072969 + 3 ^ 40 * 947663 * 2
def baseEnd_947663 : Nat := 162202205827276999284761

theorem tailTrace_947663 : CollatzResearch.WordTrace tailWord_947663 prefixEnd_947663 162202205827276999284761 := by
  unfold tailWord_947663
  simp only [CollatzResearch.WordTrace]
  refine ⟨34564109165786273800135643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23042739443857515866757095 34564109165786273800135643)
  ·
    refine ⟨51846163748679410700203465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34564109165786273800135643 51846163748679410700203465)
    ·
      refine ⟨38884622811509558025152599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51846163748679410700203465 38884622811509558025152599)
      ·
        refine ⟨58326934217264337037728899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38884622811509558025152599 58326934217264337037728899)
        ·
          refine ⟨87490401325896505556593349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58326934217264337037728899 87490401325896505556593349)
          ·
            refine ⟨16404450248605594791861253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87490401325896505556593349 16404450248605594791861253)
            ·
              refine ⟨3075834421613549023473985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16404450248605594791861253 3075834421613549023473985)
              ·
                refine ⟨2306875816210161767605489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3075834421613549023473985 2306875816210161767605489)
                ·
                  refine ⟨1730156862157621325704117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2306875816210161767605489 1730156862157621325704117)
                  ·
                    refine ⟨162202205827276999284761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1730156862157621325704117 162202205827276999284761)
                    ·
                      rfl

theorem cell23_947663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 5].length) (baseStart_947663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_947663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_947663 prefixEnd_947663 := by exact prefixLift 947663
  have htrace : WordTrace (prefixWord ++ tailWord_947663) baseStart_947663 baseEnd_947663 := by
    simpa [prefixWord, tailWord_947663, baseEnd_947663] using wordTrace_append hprefix tailTrace_947663
  have hstable : (prefixWord ++ tailWord_947663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947663).length < 2 ^ (prefixWord ++ tailWord_947663).sum := by decide
  have hdescent : baseEnd_947663 < baseStart_947663 := by decide
  rcases family_descends (prefixWord ++ tailWord_947663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947673 : List Nat := [1, 2, 1, 2, 4, 2, 2, 1, 1, 2, 5]
def baseStart_947673 : Nat := 118140960795 + 947673 * 2 ^ 59
def prefixEnd_947673 : Nat := 4983230072969 + 3 ^ 40 * 947673 * 2
def baseEnd_947673 : Nat := 486611752288375958729237

theorem tailTrace_947673 : CollatzResearch.WordTrace tailWord_947673 prefixEnd_947673 486611752288375958729237 := by
  unfold tailWord_947673
  simp only [CollatzResearch.WordTrace]
  refine ⟨34564473895750045507999673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23042982597166697005333115 34564473895750045507999673)
  ·
    refine ⟨25923355421812534130999755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34564473895750045507999673 25923355421812534130999755)
    ·
      refine ⟨38885033132718801196499633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25923355421812534130999755 38885033132718801196499633)
      ·
        refine ⟨29163774849539100897374725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38885033132718801196499633 29163774849539100897374725)
        ·
          refine ⟨5468207784288581418257761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29163774849539100897374725 5468207784288581418257761)
          ·
            refine ⟨4101155838216436063693321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5468207784288581418257761 4101155838216436063693321)
            ·
              refine ⟨3075866878662327047769991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4101155838216436063693321 3075866878662327047769991)
              ·
                refine ⟨4613800317993490571654987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3075866878662327047769991 4613800317993490571654987)
                ·
                  refine ⟨6920700476990235857482481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4613800317993490571654987 6920700476990235857482481)
                  ·
                    refine ⟨5190525357742676893111861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6920700476990235857482481 5190525357742676893111861)
                    ·
                      refine ⟨486611752288375958729237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5190525357742676893111861 486611752288375958729237)
                      ·
                        rfl

theorem cell23_947673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_947673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_947673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_947673 prefixEnd_947673 := by exact prefixLift 947673
  have htrace : WordTrace (prefixWord ++ tailWord_947673) baseStart_947673 baseEnd_947673 := by
    simpa [prefixWord, tailWord_947673, baseEnd_947673] using wordTrace_append hprefix tailTrace_947673
  have hstable : (prefixWord ++ tailWord_947673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947673).length < 2 ^ (prefixWord ++ tailWord_947673).sum := by decide
  have hdescent : baseEnd_947673 < baseStart_947673 := by decide
  rcases family_descends (prefixWord ++ tailWord_947673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947720 : List Nat := [2, 1, 3, 2, 1, 1, 2, 4, 2, 2, 3]
def baseStart_947720 : Nat := 118140960795 + 947720 * 2 ^ 59
def prefixEnd_947720 : Nat := 4983230072969 + 3 ^ 40 * 947720 * 2
def baseEnd_947720 : Nat := 486635885879137274841521

theorem tailTrace_947720 : CollatzResearch.WordTrace tailWord_947720 prefixEnd_947720 486635885879137274841521 := by
  unfold tailWord_947720
  simp only [CollatzResearch.WordTrace]
  refine ⟨17283094063289886267480307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23044125417719848356640409 17283094063289886267480307)
  ·
    refine ⟨25924641094934829401220461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17283094063289886267480307 25924641094934829401220461)
    ·
      refine ⟨9721740410600561025457673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25924641094934829401220461 9721740410600561025457673)
      ·
        refine ⟨7291305307950420769093255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9721740410600561025457673 7291305307950420769093255)
        ·
          refine ⟨10936957961925631153639883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7291305307950420769093255 10936957961925631153639883)
          ·
            refine ⟨16405436942888446730459825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10936957961925631153639883 16405436942888446730459825)
            ·
              refine ⟨12304077707166335047844869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16405436942888446730459825 12304077707166335047844869)
              ·
                refine ⟨2307014570093687821470913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12304077707166335047844869 2307014570093687821470913)
                ·
                  refine ⟨1730260927570265866103185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2307014570093687821470913 1730260927570265866103185)
                  ·
                    refine ⟨1297695695677699399577389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1730260927570265866103185 1297695695677699399577389)
                    ·
                      refine ⟨486635885879137274841521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1297695695677699399577389 486635885879137274841521)
                      ·
                        rfl

theorem cell23_947720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_947720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_947720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_947720 prefixEnd_947720 := by exact prefixLift 947720
  have htrace : WordTrace (prefixWord ++ tailWord_947720) baseStart_947720 baseEnd_947720 := by
    simpa [prefixWord, tailWord_947720, baseEnd_947720] using wordTrace_append hprefix tailTrace_947720
  have hstable : (prefixWord ++ tailWord_947720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947720).length < 2 ^ (prefixWord ++ tailWord_947720).sum := by decide
  have hdescent : baseEnd_947720 < baseStart_947720 := by decide
  rcases family_descends (prefixWord ++ tailWord_947720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947770 : List Nat := [3, 1, 1, 1, 3, 2, 1, 5, 1, 5]
def baseStart_947770 : Nat := 118140960795 + 947770 * 2 ^ 59
def prefixEnd_947770 : Nat := 4983230072969 + 3 ^ 40 * 947770 * 2
def baseEnd_947770 : Nat := 162220519970620693072097

theorem tailTrace_947770 : CollatzResearch.WordTrace tailWord_947770 prefixEnd_947770 162220519970620693072097 := by
  unfold tailWord_947770
  simp only [CollatzResearch.WordTrace]
  refine ⟨8642002944099657768570191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23045341184265754049520509 8642002944099657768570191)
  ·
    refine ⟨12963004416149486652855287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8642002944099657768570191 12963004416149486652855287)
    ·
      refine ⟨19444506624224229979282931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12963004416149486652855287 19444506624224229979282931)
      ·
        refine ⟨29166759936336344968924397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19444506624224229979282931 29166759936336344968924397)
        ·
          refine ⟨10937534976126129363346649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29166759936336344968924397 10937534976126129363346649)
          ·
            refine ⟨8203151232094597022509987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10937534976126129363346649 8203151232094597022509987)
            ·
              refine ⟨12304726848141895533764981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8203151232094597022509987 12304726848141895533764981)
              ·
                refine ⟨1153568142013302706290467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12304726848141895533764981 1153568142013302706290467)
                ·
                  refine ⟨1730352213019954059435701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1153568142013302706290467 1730352213019954059435701)
                  ·
                    refine ⟨162220519970620693072097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1730352213019954059435701 162220519970620693072097)
                    ·
                      rfl

theorem cell23_947770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 1, 5].length) (baseStart_947770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_947770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_947770 prefixEnd_947770 := by exact prefixLift 947770
  have htrace : WordTrace (prefixWord ++ tailWord_947770) baseStart_947770 baseEnd_947770 := by
    simpa [prefixWord, tailWord_947770, baseEnd_947770] using wordTrace_append hprefix tailTrace_947770
  have hstable : (prefixWord ++ tailWord_947770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947770).length < 2 ^ (prefixWord ++ tailWord_947770).sum := by decide
  have hdescent : baseEnd_947770 < baseStart_947770 := by decide
  rcases family_descends (prefixWord ++ tailWord_947770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947790 : List Nat := [4, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4]
def baseStart_947790 : Nat := 118140960795 + 947790 * 2 ^ 59
def prefixEnd_947790 : Nat := 4983230072969 + 3 ^ 40 * 947790 * 2
def baseEnd_947790 : Nat := 486671829524952000966199

theorem tailTrace_947790 : CollatzResearch.WordTrace tailWord_947790 prefixEnd_947790 486671829524952000966199 := by
  unfold tailWord_947790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4321092654540771811251103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23045827490884116326672549 4321092654540771811251103)
  ·
    refine ⟨6481638981811157716876655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4321092654540771811251103 6481638981811157716876655)
    ·
      refine ⟨9722458472716736575314983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6481638981811157716876655 9722458472716736575314983)
      ·
        refine ⟨14583687709075104862972475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9722458472716736575314983 14583687709075104862972475)
        ·
          refine ⟨21875531563612657294458713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14583687709075104862972475 21875531563612657294458713)
          ·
            refine ⟨16406648672709492970844035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21875531563612657294458713 16406648672709492970844035)
            ·
              refine ⟨24609973009064239456266053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16406648672709492970844035 24609973009064239456266053)
              ·
                refine ⟨4614369939199544898049885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24609973009064239456266053 4614369939199544898049885)
                ·
                  refine ⟨1730388727199829336768707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4614369939199544898049885 1730388727199829336768707)
                  ·
                    refine ⟨2595583090799744005153061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1730388727199829336768707 2595583090799744005153061)
                    ·
                      refine ⟨486671829524952000966199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2595583090799744005153061 486671829524952000966199)
                      ·
                        rfl

theorem cell23_947790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_947790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_947790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_947790 prefixEnd_947790 := by exact prefixLift 947790
  have htrace : WordTrace (prefixWord ++ tailWord_947790) baseStart_947790 baseEnd_947790 := by
    simpa [prefixWord, tailWord_947790, baseEnd_947790] using wordTrace_append hprefix tailTrace_947790
  have hstable : (prefixWord ++ tailWord_947790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947790).length < 2 ^ (prefixWord ++ tailWord_947790).sum := by decide
  have hdescent : baseEnd_947790 < baseStart_947790 := by decide
  rcases family_descends (prefixWord ++ tailWord_947790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947804 : List Nat := [2, 2, 4, 1, 2, 3, 1, 2, 1, 5]
def baseStart_947804 : Nat := 118140960795 + 947804 * 2 ^ 59
def prefixEnd_947804 : Nat := 4983230072969 + 3 ^ 40 * 947804 * 2
def baseEnd_947804 : Nat := 162226339418038315397045

theorem tailTrace_947804 : CollatzResearch.WordTrace tailWord_947804 prefixEnd_947804 162226339418038315397045 := by
  unfold tailWord_947804
  simp only [CollatzResearch.WordTrace]
  refine ⟨17284625929137727440509233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23046167905516969920678977 17284625929137727440509233)
  ·
    refine ⟨12963469446853295580381925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17284625929137727440509233 12963469446853295580381925)
    ·
      refine ⟨2430650521284992921321611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12963469446853295580381925 2430650521284992921321611)
      ·
        refine ⟨3645975781927489381982417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2430650521284992921321611 3645975781927489381982417)
        ·
          refine ⟨2734481836445617036486813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3645975781927489381982417 2734481836445617036486813)
          ·
            refine ⟨1025430688667106388682555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2734481836445617036486813 1025430688667106388682555)
            ·
              refine ⟨1538146033000659583023833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1025430688667106388682555 1538146033000659583023833)
              ·
                refine ⟨1153609524750494687267875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1538146033000659583023833 1153609524750494687267875)
                ·
                  refine ⟨1730414287125742030901813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1153609524750494687267875 1730414287125742030901813)
                  ·
                    refine ⟨162226339418038315397045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1730414287125742030901813 162226339418038315397045)
                    ·
                      rfl

theorem cell23_947804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_947804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_947804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_947804 prefixEnd_947804 := by exact prefixLift 947804
  have htrace : WordTrace (prefixWord ++ tailWord_947804) baseStart_947804 baseEnd_947804 := by
    simpa [prefixWord, tailWord_947804, baseEnd_947804] using wordTrace_append hprefix tailTrace_947804
  have hstable : (prefixWord ++ tailWord_947804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947804).length < 2 ^ (prefixWord ++ tailWord_947804).sum := by decide
  have hdescent : baseEnd_947804 < baseStart_947804 := by decide
  rcases family_descends (prefixWord ++ tailWord_947804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947824 : List Nat := [2, 1, 1, 1, 6, 2, 3, 1, 1, 1, 4]
def baseStart_947824 : Nat := 118140960795 + 947824 * 2 ^ 59
def prefixEnd_947824 : Nat := 4983230072969 + 3 ^ 40 * 947824 * 2
def baseEnd_947824 : Nat := 486689287867204867941043

theorem tailTrace_947824 : CollatzResearch.WordTrace tailWord_947824 prefixEnd_947824 486689287867204867941043 := by
  unfold tailWord_947824
  simp only [CollatzResearch.WordTrace]
  refine ⟨17284990659101499148373263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23046654212135332197831017 17284990659101499148373263)
  ·
    refine ⟨25927485988652248722559895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17284990659101499148373263 25927485988652248722559895)
    ·
      refine ⟨38891228982978373083839843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25927485988652248722559895 38891228982978373083839843)
      ·
        refine ⟨58336843474467559625759765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38891228982978373083839843 58336843474467559625759765)
        ·
          refine ⟨2734539537865666857457489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 58336843474467559625759765 2734539537865666857457489)
          ·
            refine ⟨2050904653399250143093117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2734539537865666857457489 2050904653399250143093117)
            ·
              refine ⟨769089245024718803659919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2050904653399250143093117 769089245024718803659919)
              ·
                refine ⟨1153633867537078205489879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 769089245024718803659919 1153633867537078205489879)
                ·
                  refine ⟨1730450801305617308234819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1153633867537078205489879 1730450801305617308234819)
                  ·
                    refine ⟨2595676201958425962352229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1730450801305617308234819 2595676201958425962352229)
                    ·
                      refine ⟨486689287867204867941043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2595676201958425962352229 486689287867204867941043)
                      ·
                        rfl

theorem cell23_947824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 1, 1, 4].length) (baseStart_947824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_947824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_947824 prefixEnd_947824 := by exact prefixLift 947824
  have htrace : WordTrace (prefixWord ++ tailWord_947824) baseStart_947824 baseEnd_947824 := by
    simpa [prefixWord, tailWord_947824, baseEnd_947824] using wordTrace_append hprefix tailTrace_947824
  have hstable : (prefixWord ++ tailWord_947824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947824).length < 2 ^ (prefixWord ++ tailWord_947824).sum := by decide
  have hdescent : baseEnd_947824 < baseStart_947824 := by decide
  rcases family_descends (prefixWord ++ tailWord_947824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947830 : List Nat := [5, 1, 1, 2, 2, 12]
def baseStart_947830 : Nat := 118140960795 + 947830 * 2 ^ 59
def prefixEnd_947830 : Nat := 4983230072969 + 3 ^ 40 * 947830 * 2
def baseEnd_947830 : Nat := 2002849254119884133605

theorem tailTrace_947830 : CollatzResearch.WordTrace tailWord_947830 prefixEnd_947830 2002849254119884133605 := by
  unfold tailWord_947830
  simp only [CollatzResearch.WordTrace]
  refine ⟨2160637509761328832591559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23046800104120840880976629 2160637509761328832591559)
  ·
    refine ⟨3240956264641993248887339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2160637509761328832591559 3240956264641993248887339)
    ·
      refine ⟨4861434396962989873331009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3240956264641993248887339 4861434396962989873331009)
      ·
        refine ⟨3646075797722242404998257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4861434396962989873331009 3646075797722242404998257)
        ·
          refine ⟨2734556848291681803748693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3646075797722242404998257 2734556848291681803748693)
          ·
            refine ⟨2002849254119884133605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 2734556848291681803748693 2002849254119884133605)
            ·
              rfl

theorem cell23_947830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 12].length) (baseStart_947830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_947830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_947830 prefixEnd_947830 := by exact prefixLift 947830
  have htrace : WordTrace (prefixWord ++ tailWord_947830) baseStart_947830 baseEnd_947830 := by
    simpa [prefixWord, tailWord_947830, baseEnd_947830] using wordTrace_append hprefix tailTrace_947830
  have hstable : (prefixWord ++ tailWord_947830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947830).length < 2 ^ (prefixWord ++ tailWord_947830).sum := by decide
  have hdescent : baseEnd_947830 < baseStart_947830 := by decide
  rcases family_descends (prefixWord ++ tailWord_947830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947840 : List Nat := [2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 3]
def baseStart_947840 : Nat := 118140960795 + 947840 * 2 ^ 59
def prefixEnd_947840 : Nat := 4983230072969 + 3 ^ 40 * 947840 * 2
def baseEnd_947840 : Nat := 486697503557676805340969

theorem tailTrace_947840 : CollatzResearch.WordTrace tailWord_947840 prefixEnd_947840 486697503557676805340969 := by
  unfold tailWord_947840
  simp only [CollatzResearch.WordTrace]
  refine ⟨17285282443072516514664487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23047043257430022019552649 17285282443072516514664487)
  ·
    refine ⟨25927923664608774771996731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17285282443072516514664487 25927923664608774771996731)
    ·
      refine ⟨38891885496913162157995097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25927923664608774771996731 38891885496913162157995097)
      ·
        refine ⟨29168914122684871618496323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38891885496913162157995097 29168914122684871618496323)
        ·
          refine ⟨43753371184027307427744485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29168914122684871618496323 43753371184027307427744485)
          ·
            refine ⟨8203757097005120142702091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43753371184027307427744485 8203757097005120142702091)
            ·
              refine ⟨12305635645507680214053137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8203757097005120142702091 12305635645507680214053137)
              ·
                refine ⟨9229226734130760160539853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12305635645507680214053137 9229226734130760160539853)
                ·
                  refine ⟨3460960025299035060202445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9229226734130760160539853 3460960025299035060202445)
                  ·
                    refine ⟨1297860009487138147575917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3460960025299035060202445 1297860009487138147575917)
                    ·
                      refine ⟨486697503557676805340969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1297860009487138147575917 486697503557676805340969)
                      ·
                        rfl

theorem cell23_947840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 3].length) (baseStart_947840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_947840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_947840 prefixEnd_947840 := by exact prefixLift 947840
  have htrace : WordTrace (prefixWord ++ tailWord_947840) baseStart_947840 baseEnd_947840 := by
    simpa [prefixWord, tailWord_947840, baseEnd_947840] using wordTrace_append hprefix tailTrace_947840
  have hstable : (prefixWord ++ tailWord_947840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947840).length < 2 ^ (prefixWord ++ tailWord_947840).sum := by decide
  have hdescent : baseEnd_947840 < baseStart_947840 := by decide
  rcases family_descends (prefixWord ++ tailWord_947840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947890 : List Nat := [3, 2, 1, 1, 1, 2, 3, 2, 2, 6]
def baseStart_947890 : Nat := 118140960795 + 947890 * 2 ^ 59
def prefixEnd_947890 : Nat := 4983230072969 + 3 ^ 40 * 947890 * 2
def baseEnd_947890 : Nat := 162241059196800536571913

theorem tailTrace_947890 : CollatzResearch.WordTrace tailWord_947890 prefixEnd_947890 162241059196800536571913 := by
  unfold tailWord_947890
  simp only [CollatzResearch.WordTrace]
  refine ⟨8643097133990972892162281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23048259023975927712432749 8643097133990972892162281)
  ·
    refine ⟨6482322850493229669121711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8643097133990972892162281 6482322850493229669121711)
    ·
      refine ⟨9723484275739844503682567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6482322850493229669121711 9723484275739844503682567)
      ·
        refine ⟨14585226413609766755523851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9723484275739844503682567 14585226413609766755523851)
        ·
          refine ⟨21877839620414650133285777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14585226413609766755523851 21877839620414650133285777)
          ·
            refine ⟨16408379715310987599964333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21877839620414650133285777 16408379715310987599964333)
            ·
              refine ⟨6153142393241620349986625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16408379715310987599964333 6153142393241620349986625)
              ·
                refine ⟨4614856794931215262489969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6153142393241620349986625 4614856794931215262489969)
                ·
                  refine ⟨3461142596198411446867477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4614856794931215262489969 3461142596198411446867477)
                  ·
                    refine ⟨162241059196800536571913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3461142596198411446867477 162241059196800536571913)
                    ·
                      rfl

theorem cell23_947890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_947890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_947890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_947890 prefixEnd_947890 := by exact prefixLift 947890
  have htrace : WordTrace (prefixWord ++ tailWord_947890) baseStart_947890 baseEnd_947890 := by
    simpa [prefixWord, tailWord_947890, baseEnd_947890] using wordTrace_append hprefix tailTrace_947890
  have hstable : (prefixWord ++ tailWord_947890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947890).length < 2 ^ (prefixWord ++ tailWord_947890).sum := by decide
  have hdescent : baseEnd_947890 < baseStart_947890 := by decide
  rcases family_descends (prefixWord ++ tailWord_947890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947897 : List Nat := [1, 2, 1, 4, 1, 1, 2, 2, 3, 4, 2]
def baseStart_947897 : Nat := 118140960795 + 947897 * 2 ^ 59
def prefixEnd_947897 : Nat := 4983230072969 + 3 ^ 40 * 947897 * 2
def baseEnd_947897 : Nat := 486726771954983082328207

theorem tailTrace_947897 : CollatzResearch.WordTrace tailWord_947897 prefixEnd_947897 486726771954983082328207 := by
  unfold tailWord_947897
  simp only [CollatzResearch.WordTrace]
  refine ⟨34572643846938531764153945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23048429231292354509435963 34572643846938531764153945)
  ·
    refine ⟨25929482885203898823115459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34572643846938531764153945 25929482885203898823115459)
    ·
      refine ⟨38894224327805848234673189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25929482885203898823115459 38894224327805848234673189)
      ·
        refine ⟨7292667061463596544001223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38894224327805848234673189 7292667061463596544001223)
        ·
          refine ⟨10939000592195394816001835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7292667061463596544001223 10939000592195394816001835)
          ·
            refine ⟨16408500888293092224002753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10939000592195394816001835 16408500888293092224002753)
            ·
              refine ⟨12306375666219819168002065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16408500888293092224002753 12306375666219819168002065)
              ·
                refine ⟨9229781749664864376001549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12306375666219819168002065 9229781749664864376001549)
                ·
                  refine ⟨3461168156124324141000581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9229781749664864376001549 3461168156124324141000581)
                  ·
                    refine ⟨648969029273310776437609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3461168156124324141000581 648969029273310776437609)
                    ·
                      refine ⟨486726771954983082328207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 648969029273310776437609 486726771954983082328207)
                      ·
                        rfl

theorem cell23_947897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_947897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_947897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_947897 prefixEnd_947897 := by exact prefixLift 947897
  have htrace : WordTrace (prefixWord ++ tailWord_947897) baseStart_947897 baseEnd_947897 := by
    simpa [prefixWord, tailWord_947897, baseEnd_947897] using wordTrace_append hprefix tailTrace_947897
  have hstable : (prefixWord ++ tailWord_947897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947897).length < 2 ^ (prefixWord ++ tailWord_947897).sum := by decide
  have hdescent : baseEnd_947897 < baseStart_947897 := by decide
  rcases family_descends (prefixWord ++ tailWord_947897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947980 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 2, 8]
def baseStart_947980 : Nat := 118140960795 + 947980 * 2 ^ 59
def prefixEnd_947980 : Nat := 4983230072969 + 3 ^ 40 * 947980 * 2
def baseEnd_947980 : Nat := 162256463616435419196775

theorem tailTrace_947980 : CollatzResearch.WordTrace tailWord_947980 prefixEnd_947980 162256463616435419196775 := by
  unfold tailWord_947980
  simp only [CollatzResearch.WordTrace]
  refine ⟨17287835552818918469712697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23050447403758557959616929 17287835552818918469712697)
  ·
    refine ⟨12965876664614188852284523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17287835552818918469712697 12965876664614188852284523)
    ·
      refine ⟨19448814996921283278426785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12965876664614188852284523 19448814996921283278426785)
      ·
        refine ⟨14586611247690962458820089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19448814996921283278426785 14586611247690962458820089)
        ·
          refine ⟨10939958435768221844115067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14586611247690962458820089 10939958435768221844115067)
          ·
            refine ⟨16409937653652332766172601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10939958435768221844115067 16409937653652332766172601)
            ·
              refine ⟨12307453240239249574629451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16409937653652332766172601 12307453240239249574629451)
              ·
                refine ⟨18461179860358874361944177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12307453240239249574629451 18461179860358874361944177)
                ·
                  refine ⟨13845884895269155771458133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18461179860358874361944177 13845884895269155771458133)
                  ·
                    refine ⟨162256463616435419196775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13845884895269155771458133 162256463616435419196775)
                    ·
                      rfl

theorem cell23_947980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 8].length) (baseStart_947980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_947980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_947980 prefixEnd_947980 := by exact prefixLift 947980
  have htrace : WordTrace (prefixWord ++ tailWord_947980) baseStart_947980 baseEnd_947980 := by
    simpa [prefixWord, tailWord_947980, baseEnd_947980] using wordTrace_append hprefix tailTrace_947980
  have hstable : (prefixWord ++ tailWord_947980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947980).length < 2 ^ (prefixWord ++ tailWord_947980).sum := by decide
  have hdescent : baseEnd_947980 < baseStart_947980 := by decide
  rcases family_descends (prefixWord ++ tailWord_947980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947987 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 3, 6, 2]
def baseStart_947987 : Nat := 118140960795 + 947987 * 2 ^ 59
def prefixEnd_947987 : Nat := 4983230072969 + 3 ^ 40 * 947987 * 2
def baseEnd_947987 : Nat := 486772985213887730202793

theorem tailTrace_947987 : CollatzResearch.WordTrace tailWord_947987 prefixEnd_947987 486772985213887730202793 := by
  unfold tailWord_947987
  simp only [CollatzResearch.WordTrace]
  refine ⟨34575926416612477134930215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23050617611074984756620143 34575926416612477134930215)
  ·
    refine ⟨51863889624918715702395323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34575926416612477134930215 51863889624918715702395323)
    ·
      refine ⟨77795834437378073553592985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51863889624918715702395323 77795834437378073553592985)
      ·
        refine ⟨58346875828033555165194739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77795834437378073553592985 58346875828033555165194739)
        ·
          refine ⟨87520313742050332747792109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58346875828033555165194739 87520313742050332747792109)
          ·
            refine ⟨32820117653268874780422041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87520313742050332747792109 32820117653268874780422041)
            ·
              refine ⟨24615088239951656085316531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32820117653268874780422041 24615088239951656085316531)
              ·
                refine ⟨36922632359927484127974797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24615088239951656085316531 36922632359927484127974797)
                ·
                  refine ⟨13845987134972806547990549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36922632359927484127974797 13845987134972806547990549)
                  ·
                    refine ⟨649030646951850306937057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13845987134972806547990549 649030646951850306937057)
                    ·
                      refine ⟨486772985213887730202793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 649030646951850306937057 486772985213887730202793)
                      ·
                        rfl

theorem cell23_947987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 6, 2].length) (baseStart_947987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_947987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_947987 prefixEnd_947987 := by exact prefixLift 947987
  have htrace : WordTrace (prefixWord ++ tailWord_947987) baseStart_947987 baseEnd_947987 := by
    simpa [prefixWord, tailWord_947987, baseEnd_947987] using wordTrace_append hprefix tailTrace_947987
  have hstable : (prefixWord ++ tailWord_947987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947987).length < 2 ^ (prefixWord ++ tailWord_947987).sum := by decide
  have hdescent : baseEnd_947987 < baseStart_947987 := by decide
  rcases family_descends (prefixWord ++ tailWord_947987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948004 : List Nat := [2, 3, 1, 3, 2, 1, 2, 2, 2, 1, 4]
def baseStart_948004 : Nat := 118140960795 + 948004 * 2 ^ 59
def prefixEnd_948004 : Nat := 4983230072969 + 3 ^ 40 * 948004 * 2
def baseEnd_948004 : Nat := 486781714385014163690215

theorem tailTrace_948004 : CollatzResearch.WordTrace tailWord_948004 prefixEnd_948004 486781714385014163690215 := by
  unfold tailWord_948004
  simp only [CollatzResearch.WordTrace]
  refine ⟨17288273228775444519149533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23051030971700592692199377 17288273228775444519149533)
  ·
    refine ⟨6483102460790791694681075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17288273228775444519149533 6483102460790791694681075)
    ·
      refine ⟨9724653691186187542021613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6483102460790791694681075 9724653691186187542021613)
      ·
        refine ⟨3646745134194820328258105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9724653691186187542021613 3646745134194820328258105)
        ·
          refine ⟨2735058850646115246193579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3646745134194820328258105 2735058850646115246193579)
          ·
            refine ⟨4102588275969172869290369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2735058850646115246193579 4102588275969172869290369)
            ·
              refine ⟨3076941206976879651967777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4102588275969172869290369 3076941206976879651967777)
              ·
                refine ⟨2307705905232659738975833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3076941206976879651967777 2307705905232659738975833)
                ·
                  refine ⟨1730779428924494804231875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2307705905232659738975833 1730779428924494804231875)
                  ·
                    refine ⟨2596169143386742206347813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1730779428924494804231875 2596169143386742206347813)
                    ·
                      refine ⟨486781714385014163690215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2596169143386742206347813 486781714385014163690215)
                      ·
                        rfl

theorem cell23_948004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_948004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948004 prefixEnd_948004 := by exact prefixLift 948004
  have htrace : WordTrace (prefixWord ++ tailWord_948004) baseStart_948004 baseEnd_948004 := by
    simpa [prefixWord, tailWord_948004, baseEnd_948004] using wordTrace_append hprefix tailTrace_948004
  have hstable : (prefixWord ++ tailWord_948004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948004).length < 2 ^ (prefixWord ++ tailWord_948004).sum := by decide
  have hdescent : baseEnd_948004 < baseStart_948004 := by decide
  rcases family_descends (prefixWord ++ tailWord_948004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948021 : List Nat := [1, 3, 3, 1, 4, 1, 1, 1, 2, 4, 2]
def baseStart_948021 : Nat := 118140960795 + 948021 * 2 ^ 59
def prefixEnd_948021 : Nat := 4983230072969 + 3 ^ 40 * 948021 * 2
def baseEnd_948021 : Nat := 486790443556140597177637

theorem tailTrace_948021 : CollatzResearch.WordTrace tailWord_948021 prefixEnd_948021 486790443556140597177637 := by
  unfold tailWord_948021
  simp only [CollatzResearch.WordTrace]
  refine ⟨34577166498489300941667917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23051444332326200627778611 34577166498489300941667917)
  ·
    refine ⟨12966437436933487853125469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34577166498489300941667917 12966437436933487853125469)
    ·
      refine ⟨4862414038850057944922051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12966437436933487853125469 4862414038850057944922051)
      ·
        refine ⟨7293621058275086917383077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4862414038850057944922051 7293621058275086917383077)
        ·
          refine ⟨1367553948426578797009327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7293621058275086917383077 1367553948426578797009327)
          ·
            refine ⟨2051330922639868195513991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1367553948426578797009327 2051330922639868195513991)
            ·
              refine ⟨3076996383959802293270987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2051330922639868195513991 3076996383959802293270987)
              ·
                refine ⟨4615494575939703439906481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3076996383959802293270987 4615494575939703439906481)
                ·
                  refine ⟨3461620931954777579929861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4615494575939703439906481 3461620931954777579929861)
                  ·
                    refine ⟨649053924741520796236849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3461620931954777579929861 649053924741520796236849)
                    ·
                      refine ⟨486790443556140597177637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 649053924741520796236849 486790443556140597177637)
                      ·
                        rfl

theorem cell23_948021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_948021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948021 prefixEnd_948021 := by exact prefixLift 948021
  have htrace : WordTrace (prefixWord ++ tailWord_948021) baseStart_948021 baseEnd_948021 := by
    simpa [prefixWord, tailWord_948021, baseEnd_948021] using wordTrace_append hprefix tailTrace_948021
  have hstable : (prefixWord ++ tailWord_948021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948021).length < 2 ^ (prefixWord ++ tailWord_948021).sum := by decide
  have hdescent : baseEnd_948021 < baseStart_948021 := by decide
  rcases family_descends (prefixWord ++ tailWord_948021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948038 : List Nat := [6, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4]
def baseStart_948038 : Nat := 118140960795 + 948038 * 2 ^ 59
def prefixEnd_948038 : Nat := 4983230072969 + 3 ^ 40 * 948038 * 2
def baseEnd_948038 : Nat := 486799172727267030665059

theorem tailTrace_948038 : CollatzResearch.WordTrace tailWord_948038 prefixEnd_948038 486799172727267030665059 := by
  unfold tailWord_948038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1080555829357116026407399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23051857692951808563357845 1080555829357116026407399)
  ·
    refine ⟨1620833744035674039611099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1080555829357116026407399 1620833744035674039611099)
    ·
      refine ⟨2431250616053511059416649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1620833744035674039611099 2431250616053511059416649)
      ·
        refine ⟨1823437962040133294562487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2431250616053511059416649 1823437962040133294562487)
        ·
          refine ⟨2735156943060199941843731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1823437962040133294562487 2735156943060199941843731)
          ·
            refine ⟨4102735414590299912765597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2735156943060199941843731 4102735414590299912765597)
            ·
              refine ⟨1538525780471362467287099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4102735414590299912765597 1538525780471362467287099)
              ·
                refine ⟨2307788670707043700930649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1538525780471362467287099 2307788670707043700930649)
                ·
                  refine ⟨1730841503030282775697987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2307788670707043700930649 1730841503030282775697987)
                  ·
                    refine ⟨2596262254545424163546981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1730841503030282775697987 2596262254545424163546981)
                    ·
                      refine ⟨486799172727267030665059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2596262254545424163546981 486799172727267030665059)
                      ·
                        rfl

theorem cell23_948038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_948038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948038 prefixEnd_948038 := by exact prefixLift 948038
  have htrace : WordTrace (prefixWord ++ tailWord_948038) baseStart_948038 baseEnd_948038 := by
    simpa [prefixWord, tailWord_948038, baseEnd_948038] using wordTrace_append hprefix tailTrace_948038
  have hstable : (prefixWord ++ tailWord_948038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948038).length < 2 ^ (prefixWord ++ tailWord_948038).sum := by decide
  have hdescent : baseEnd_948038 < baseStart_948038 := by decide
  rcases family_descends (prefixWord ++ tailWord_948038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948071 : List Nat := [1, 1, 5, 1, 2, 1, 4, 1, 3, 1, 3]
def baseStart_948071 : Nat := 118140960795 + 948071 * 2 ^ 59
def prefixEnd_948071 : Nat := 4983230072969 + 3 ^ 40 * 948071 * 2
def baseEnd_948071 : Nat := 486816117588865401552407

theorem tailTrace_948071 : CollatzResearch.WordTrace tailWord_948071 prefixEnd_948071 486816117588865401552407 := by
  unfold tailWord_948071
  simp only [CollatzResearch.WordTrace]
  refine ⟨34578990148308159480988067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23052660098872106320658711 34578990148308159480988067)
  ·
    refine ⟨51868485222462239221482101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34578990148308159480988067 51868485222462239221482101)
    ·
      refine ⟨4862670489605834927013947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51868485222462239221482101 4862670489605834927013947)
      ·
        refine ⟨7294005734408752390520921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4862670489605834927013947 7294005734408752390520921)
        ·
          refine ⟨5470504300806564292890691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7294005734408752390520921 5470504300806564292890691)
          ·
            refine ⟨8205756451209846439336037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5470504300806564292890691 8205756451209846439336037)
            ·
              refine ⟨1538579334601846207375507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8205756451209846439336037 1538579334601846207375507)
              ·
                refine ⟨2307869001902769311063261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1538579334601846207375507 2307869001902769311063261)
                ·
                  refine ⟨865450875713538491648723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2307869001902769311063261 865450875713538491648723)
                  ·
                    refine ⟨1298176313570307737473085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 865450875713538491648723 1298176313570307737473085)
                    ·
                      refine ⟨486816117588865401552407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1298176313570307737473085 486816117588865401552407)
                      ·
                        rfl

theorem cell23_948071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_948071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948071 prefixEnd_948071 := by exact prefixLift 948071
  have htrace : WordTrace (prefixWord ++ tailWord_948071) baseStart_948071 baseEnd_948071 := by
    simpa [prefixWord, tailWord_948071, baseEnd_948071] using wordTrace_append hprefix tailTrace_948071
  have hstable : (prefixWord ++ tailWord_948071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948071).length < 2 ^ (prefixWord ++ tailWord_948071).sum := by decide
  have hdescent : baseEnd_948071 < baseStart_948071 := by decide
  rcases family_descends (prefixWord ++ tailWord_948071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948107 : List Nat := [1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 4]
def baseStart_948107 : Nat := 118140960795 + 948107 * 2 ^ 59
def prefixEnd_948107 : Nat := 4983230072969 + 3 ^ 40 * 948107 * 2
def baseEnd_948107 : Nat := 486834602892427260702241

theorem tailTrace_948107 : CollatzResearch.WordTrace tailWord_948107 prefixEnd_948107 486834602892427260702241 := by
  unfold tailWord_948107
  simp only [CollatzResearch.WordTrace]
  refine ⟨34580303176177737629298575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23053535450785158419532383 34580303176177737629298575)
  ·
    refine ⟨51870454764266606443947863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34580303176177737629298575 51870454764266606443947863)
    ·
      refine ⟨77805682146399909665921795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51870454764266606443947863 77805682146399909665921795)
      ·
        refine ⟨116708523219599864498882693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77805682146399909665921795 116708523219599864498882693)
        ·
          refine ⟨21882848103674974593540505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116708523219599864498882693 21882848103674974593540505)
          ·
            refine ⟨16412136077756230945155379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21882848103674974593540505 16412136077756230945155379)
            ·
              refine ⟨24618204116634346417733069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16412136077756230945155379 24618204116634346417733069)
              ·
                refine ⟨9231826543737879906649901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24618204116634346417733069 9231826543737879906649901)
                ·
                  refine ⟨3461934953901704964993713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9231826543737879906649901 3461934953901704964993713)
                  ·
                    refine ⟨2596451215426278723745285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3461934953901704964993713 2596451215426278723745285)
                    ·
                      refine ⟨486834602892427260702241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2596451215426278723745285 486834602892427260702241)
                      ·
                        rfl

theorem cell23_948107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 4].length) (baseStart_948107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948107 prefixEnd_948107 := by exact prefixLift 948107
  have htrace : WordTrace (prefixWord ++ tailWord_948107) baseStart_948107 baseEnd_948107 := by
    simpa [prefixWord, tailWord_948107, baseEnd_948107] using wordTrace_append hprefix tailTrace_948107
  have hstable : (prefixWord ++ tailWord_948107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948107).length < 2 ^ (prefixWord ++ tailWord_948107).sum := by decide
  have hdescent : baseEnd_948107 < baseStart_948107 := by decide
  rcases family_descends (prefixWord ++ tailWord_948107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948124 : List Nat := [2, 2, 3, 3, 1, 1, 1, 2, 1, 1, 6]
def baseStart_948124 : Nat := 118140960795 + 948124 * 2 ^ 59
def prefixEnd_948124 : Nat := 4983230072969 + 3 ^ 40 * 948124 * 2
def baseEnd_948124 : Nat := 486843332063553694189663

theorem tailTrace_948124 : CollatzResearch.WordTrace tailWord_948124 prefixEnd_948124 486843332063553694189663 := by
  unfold tailWord_948124
  simp only [CollatzResearch.WordTrace]
  refine ⟨17290461608558074766333713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23053948811410766355111617 17290461608558074766333713)
  ·
    refine ⟨12967846206418556074750285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17290461608558074766333713 12967846206418556074750285)
    ·
      refine ⟨4862942327406958528031357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12967846206418556074750285 4862942327406958528031357)
      ·
        refine ⟨1823603372777609448011759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4862942327406958528031357 1823603372777609448011759)
        ·
          refine ⟨2735405059166414172017639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1823603372777609448011759 2735405059166414172017639)
          ·
            refine ⟨4103107588749621258026459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2735405059166414172017639 4103107588749621258026459)
            ·
              refine ⟨6154661383124431887039689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4103107588749621258026459 6154661383124431887039689)
              ·
                refine ⟨4615996037343323915279767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6154661383124431887039689 4615996037343323915279767)
                ·
                  refine ⟨6923994056014985872919651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4615996037343323915279767 6923994056014985872919651)
                  ·
                    refine ⟨10385991084022478809379477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6923994056014985872919651 10385991084022478809379477)
                    ·
                      refine ⟨486843332063553694189663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10385991084022478809379477 486843332063553694189663)
                      ·
                        rfl

theorem cell23_948124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_948124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948124 prefixEnd_948124 := by exact prefixLift 948124
  have htrace : WordTrace (prefixWord ++ tailWord_948124) baseStart_948124 baseEnd_948124 := by
    simpa [prefixWord, tailWord_948124, baseEnd_948124] using wordTrace_append hprefix tailTrace_948124
  have hstable : (prefixWord ++ tailWord_948124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948124).length < 2 ^ (prefixWord ++ tailWord_948124).sum := by decide
  have hdescent : baseEnd_948124 < baseStart_948124 := by decide
  rcases family_descends (prefixWord ++ tailWord_948124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948142 : List Nat := [4, 1, 5, 1, 1, 2, 1, 2, 1, 5]
def baseStart_948142 : Nat := 118140960795 + 948142 * 2 ^ 59
def prefixEnd_948142 : Nat := 4983230072969 + 3 ^ 40 * 948142 * 2
def baseEnd_948142 : Nat := 162284191571778207921527

theorem tailTrace_948142 : CollatzResearch.WordTrace tailWord_948142 prefixEnd_948142 162284191571778207921527 := by
  unfold tailWord_948142
  simp only [CollatzResearch.WordTrace]
  refine ⟨4322697466381367325852835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23054386487367292404548453 4322697466381367325852835)
  ·
    refine ⟨6484046199572050988779253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4322697466381367325852835 6484046199572050988779253)
    ·
      refine ⟨607879331209879780198055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6484046199572050988779253 607879331209879780198055)
      ·
        refine ⟨911818996814819670297083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607879331209879780198055 911818996814819670297083)
        ·
          refine ⟨1367728495222229505445625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 911818996814819670297083 1367728495222229505445625)
          ·
            refine ⟨1025796371416672129084219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1367728495222229505445625 1025796371416672129084219)
            ·
              refine ⟨1538694557125008193626329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1025796371416672129084219 1538694557125008193626329)
              ·
                refine ⟨1154020917843756145219747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1538694557125008193626329 1154020917843756145219747)
                ·
                  refine ⟨1731031376765634217829621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1154020917843756145219747 1731031376765634217829621)
                  ·
                    refine ⟨162284191571778207921527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1731031376765634217829621 162284191571778207921527)
                    ·
                      rfl

theorem cell23_948142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_948142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948142 prefixEnd_948142 := by exact prefixLift 948142
  have htrace : WordTrace (prefixWord ++ tailWord_948142) baseStart_948142 baseEnd_948142 := by
    simpa [prefixWord, tailWord_948142, baseEnd_948142] using wordTrace_append hprefix tailTrace_948142
  have hstable : (prefixWord ++ tailWord_948142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948142).length < 2 ^ (prefixWord ++ tailWord_948142).sum := by decide
  have hdescent : baseEnd_948142 < baseStart_948142 := by decide
  rcases family_descends (prefixWord ++ tailWord_948142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948222 : List Nat := [4, 2, 2, 2, 1, 1, 4, 1, 1, 3, 2]
def baseStart_948222 : Nat := 118140960795 + 948222 * 2 ^ 59
def prefixEnd_948222 : Nat := 4983230072969 + 3 ^ 40 * 948222 * 2
def baseEnd_948222 : Nat := 486893653167694310764213

theorem tailTrace_948222 : CollatzResearch.WordTrace tailWord_948222 prefixEnd_948222 486893653167694310764213 := by
  unfold tailWord_948222
  simp only [CollatzResearch.WordTrace]
  refine ⟨4323062196345139033716865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23056331713840741513156613 4323062196345139033716865)
  ·
    refine ⟨3242296647258854275287649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4323062196345139033716865 3242296647258854275287649)
    ·
      refine ⟨2431722485444140706465737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3242296647258854275287649 2431722485444140706465737)
      ·
        refine ⟨1823791864083105529849303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2431722485444140706465737 1823791864083105529849303)
        ·
          refine ⟨2735687796124658294773955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1823791864083105529849303 2735687796124658294773955)
          ·
            refine ⟨4103531694186987442160933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2735687796124658294773955 4103531694186987442160933)
            ·
              refine ⟨769412192660060145405175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4103531694186987442160933 769412192660060145405175)
              ·
                refine ⟨1154118288990090218107763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 769412192660060145405175 1154118288990090218107763)
                ·
                  refine ⟨1731177433485135327161645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1154118288990090218107763 1731177433485135327161645)
                  ·
                    refine ⟨649191537556925747685617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1731177433485135327161645 649191537556925747685617)
                    ·
                      refine ⟨486893653167694310764213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 649191537556925747685617 486893653167694310764213)
                      ·
                        rfl

theorem cell23_948222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_948222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948222 prefixEnd_948222 := by exact prefixLift 948222
  have htrace : WordTrace (prefixWord ++ tailWord_948222) baseStart_948222 baseEnd_948222 := by
    simpa [prefixWord, tailWord_948222, baseEnd_948222] using wordTrace_append hprefix tailTrace_948222
  have hstable : (prefixWord ++ tailWord_948222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948222).length < 2 ^ (prefixWord ++ tailWord_948222).sum := by decide
  have hdescent : baseEnd_948222 < baseStart_948222 := by decide
  rcases family_descends (prefixWord ++ tailWord_948222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948252 : List Nat := [2, 2, 3, 1, 3, 2, 3, 1, 2, 2, 2]
def baseStart_948252 : Nat := 118140960795 + 948252 * 2 ^ 59
def prefixEnd_948252 : Nat := 4983230072969 + 3 ^ 40 * 948252 * 2
def baseEnd_948252 : Nat := 486909057587329193389075

theorem tailTrace_948252 : CollatzResearch.WordTrace tailWord_948252 prefixEnd_948252 486909057587329193389075 := by
  unfold tailWord_948252
  simp only [CollatzResearch.WordTrace]
  refine ⟨17292795880326213696663505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23057061173768284928884673 17292795880326213696663505)
  ·
    refine ⟨12969596910244660272497629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17292795880326213696663505 12969596910244660272497629)
    ·
      refine ⟨4863598841341747602186611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12969596910244660272497629 4863598841341747602186611)
      ·
        refine ⟨7295398262012621403279917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4863598841341747602186611 7295398262012621403279917)
        ·
          refine ⟨2735774348254733026229969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7295398262012621403279917 2735774348254733026229969)
          ·
            refine ⟨2051830761191049769672477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2735774348254733026229969 2051830761191049769672477)
            ·
              refine ⟨769436535446643663627179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2051830761191049769672477 769436535446643663627179)
              ·
                refine ⟨1154154803169965495440769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 769436535446643663627179 1154154803169965495440769)
                ·
                  refine ⟨865616102377474121580577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1154154803169965495440769 865616102377474121580577)
                  ·
                    refine ⟨649212076783105591185433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 865616102377474121580577 649212076783105591185433)
                    ·
                      refine ⟨486909057587329193389075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 649212076783105591185433 486909057587329193389075)
                      ·
                        rfl

theorem cell23_948252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_948252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948252 prefixEnd_948252 := by exact prefixLift 948252
  have htrace : WordTrace (prefixWord ++ tailWord_948252) baseStart_948252 baseEnd_948252 := by
    simpa [prefixWord, tailWord_948252, baseEnd_948252] using wordTrace_append hprefix tailTrace_948252
  have hstable : (prefixWord ++ tailWord_948252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948252).length < 2 ^ (prefixWord ++ tailWord_948252).sum := by decide
  have hdescent : baseEnd_948252 < baseStart_948252 := by decide
  rcases family_descends (prefixWord ++ tailWord_948252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948291 : List Nat := [1, 1, 1, 3, 1, 2, 2, 4, 2, 4, 2]
def baseStart_948291 : Nat := 118140960795 + 948291 * 2 ^ 59
def prefixEnd_948291 : Nat := 4983230072969 + 3 ^ 40 * 948291 * 2
def baseEnd_948291 : Nat := 486929083332854540801395

theorem tailTrace_948291 : CollatzResearch.WordTrace tailWord_948291 prefixEnd_948291 486929083332854540801395 := by
  unfold tailWord_948291
  simp only [CollatzResearch.WordTrace]
  refine ⟨34587014207511137053996727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23058009471674091369331151 34587014207511137053996727)
  ·
    refine ⟨51880521311266705580995091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34587014207511137053996727 51880521311266705580995091)
    ·
      refine ⟨77820781966900058371492637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51880521311266705580995091 77820781966900058371492637)
      ·
        refine ⟨29182793237587521889309739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77820781966900058371492637 29182793237587521889309739)
        ·
          refine ⟨43774189856381282833964609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29182793237587521889309739 43774189856381282833964609)
          ·
            refine ⟨32830642392285962125473457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43774189856381282833964609 32830642392285962125473457)
            ·
              refine ⟨24622981794214471594105093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32830642392285962125473457 24622981794214471594105093)
              ·
                refine ⟨4616809086415213423894705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24622981794214471594105093 4616809086415213423894705)
                ·
                  refine ⟨3462606814811410067921029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4616809086415213423894705 3462606814811410067921029)
                  ·
                    refine ⟨649238777777139387735193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3462606814811410067921029 649238777777139387735193)
                    ·
                      refine ⟨486929083332854540801395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 649238777777139387735193 486929083332854540801395)
                      ·
                        rfl

theorem cell23_948291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 4, 2].length) (baseStart_948291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948291 prefixEnd_948291 := by exact prefixLift 948291
  have htrace : WordTrace (prefixWord ++ tailWord_948291) baseStart_948291 baseEnd_948291 := by
    simpa [prefixWord, tailWord_948291, baseEnd_948291] using wordTrace_append hprefix tailTrace_948291
  have hstable : (prefixWord ++ tailWord_948291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948291).length < 2 ^ (prefixWord ++ tailWord_948291).sum := by decide
  have hdescent : baseEnd_948291 < baseStart_948291 := by decide
  rcases family_descends (prefixWord ++ tailWord_948291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948375 : List Nat := [1, 1, 3, 3, 4, 1, 1, 2, 3, 1, 3]
def baseStart_948375 : Nat := 118140960795 + 948375 * 2 ^ 59
def prefixEnd_948375 : Nat := 4983230072969 + 3 ^ 40 * 948375 * 2
def baseEnd_948375 : Nat := 486972215707832212151009

theorem tailTrace_948375 : CollatzResearch.WordTrace tailWord_948375 prefixEnd_948375 486972215707832212151009 := by
  unfold tailWord_948375
  simp only [CollatzResearch.WordTrace]
  refine ⟨34590077939206819400054579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23060051959471212933369719 34590077939206819400054579)
  ·
    refine ⟨51885116908810229100081869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34590077939206819400054579 51885116908810229100081869)
    ·
      refine ⟨19456918840803835912530701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51885116908810229100081869 19456918840803835912530701)
      ·
        refine ⟨7296344565301438467199013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19456918840803835912530701 7296344565301438467199013)
        ·
          refine ⟨1368064605994019712599815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7296344565301438467199013 1368064605994019712599815)
          ·
            refine ⟨2052096908991029568899723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1368064605994019712599815 2052096908991029568899723)
            ·
              refine ⟨3078145363486544353349585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2052096908991029568899723 3078145363486544353349585)
              ·
                refine ⟨2308609022614908265012189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3078145363486544353349585 2308609022614908265012189)
                ·
                  refine ⟨865728383480590599379571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2308609022614908265012189 865728383480590599379571)
                  ·
                    refine ⟨1298592575220885899069357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 865728383480590599379571 1298592575220885899069357)
                    ·
                      refine ⟨486972215707832212151009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1298592575220885899069357 486972215707832212151009)
                      ·
                        rfl

theorem cell23_948375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_948375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948375 prefixEnd_948375 := by exact prefixLift 948375
  have htrace : WordTrace (prefixWord ++ tailWord_948375) baseStart_948375 baseEnd_948375 := by
    simpa [prefixWord, tailWord_948375, baseEnd_948375] using wordTrace_append hprefix tailTrace_948375
  have hstable : (prefixWord ++ tailWord_948375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948375).length < 2 ^ (prefixWord ++ tailWord_948375).sum := by decide
  have hdescent : baseEnd_948375 < baseStart_948375 := by decide
  rcases family_descends (prefixWord ++ tailWord_948375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948385 : List Nat := [1, 2, 3, 3, 1, 2, 3, 1, 2, 3, 2]
def baseStart_948385 : Nat := 118140960795 + 948385 * 2 ^ 59
def prefixEnd_948385 : Nat := 4983230072969 + 3 ^ 40 * 948385 * 2
def baseEnd_948385 : Nat := 486977350514377173025963

theorem tailTrace_948385 : CollatzResearch.WordTrace tailWord_948385 prefixEnd_948385 486977350514377173025963 := by
  unfold tailWord_948385
  simp only [CollatzResearch.WordTrace]
  refine ⟨34590442669170591107918609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23060295112780394071945739 34590442669170591107918609)
  ·
    refine ⟨25942832001877943330938957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34590442669170591107918609 25942832001877943330938957)
    ·
      refine ⟨9728562000704228749102109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25942832001877943330938957 9728562000704228749102109)
      ·
        refine ⟨3648210750264085780913291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9728562000704228749102109 3648210750264085780913291)
        ·
          refine ⟨5472316125396128671369937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3648210750264085780913291 5472316125396128671369937)
          ·
            refine ⟨4104237094047096503527453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5472316125396128671369937 4104237094047096503527453)
            ·
              refine ⟨1539088910267661188822795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4104237094047096503527453 1539088910267661188822795)
              ·
                refine ⟨2308633365401491783234193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1539088910267661188822795 2308633365401491783234193)
                ·
                  refine ⟨1731475024051118837425645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2308633365401491783234193 1731475024051118837425645)
                  ·
                    refine ⟨649303134019169564034617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1731475024051118837425645 649303134019169564034617)
                    ·
                      refine ⟨486977350514377173025963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 649303134019169564034617 486977350514377173025963)
                      ·
                        rfl

theorem cell23_948385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_948385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948385 prefixEnd_948385 := by exact prefixLift 948385
  have htrace : WordTrace (prefixWord ++ tailWord_948385) baseStart_948385 baseEnd_948385 := by
    simpa [prefixWord, tailWord_948385, baseEnd_948385] using wordTrace_append hprefix tailTrace_948385
  have hstable : (prefixWord ++ tailWord_948385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948385).length < 2 ^ (prefixWord ++ tailWord_948385).sum := by decide
  have hdescent : baseEnd_948385 < baseStart_948385 := by decide
  rcases family_descends (prefixWord ++ tailWord_948385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948448 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 6, 1, 3]
def baseStart_948448 : Nat := 118140960795 + 948448 * 2 ^ 59
def prefixEnd_948448 : Nat := 4983230072969 + 3 ^ 40 * 948448 * 2
def baseEnd_948448 : Nat := 487009699795610426538173

theorem tailTrace_948448 : CollatzResearch.WordTrace tailWord_948448 prefixEnd_948448 487009699795610426538173 := by
  unfold tailWord_948448
  simp only [CollatzResearch.WordTrace]
  refine ⟨17296370233971176433730999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23061826978628235244974665 17296370233971176433730999)
  ·
    refine ⟨25944555350956764650596499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17296370233971176433730999 25944555350956764650596499)
    ·
      refine ⟨38916833026435146975894749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25944555350956764650596499 38916833026435146975894749)
      ·
        refine ⟨14593812384913180115960531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38916833026435146975894749 14593812384913180115960531)
        ·
          refine ⟨21890718577369770173940797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14593812384913180115960531 21890718577369770173940797)
          ·
            refine ⟨8209019466513663815227799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21890718577369770173940797 8209019466513663815227799)
            ·
              refine ⟨12313529199770495722841699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8209019466513663815227799 12313529199770495722841699)
              ·
                refine ⟨18470293799655743584262549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12313529199770495722841699 18470293799655743584262549)
                ·
                  refine ⟨865795021858862980512307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 18470293799655743584262549 865795021858862980512307)
                  ·
                    refine ⟨1298692532788294470768461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 865795021858862980512307 1298692532788294470768461)
                    ·
                      refine ⟨487009699795610426538173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1298692532788294470768461 487009699795610426538173)
                      ·
                        rfl

theorem cell23_948448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 6, 1, 3].length) (baseStart_948448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948448 prefixEnd_948448 := by exact prefixLift 948448
  have htrace : WordTrace (prefixWord ++ tailWord_948448) baseStart_948448 baseEnd_948448 := by
    simpa [prefixWord, tailWord_948448, baseEnd_948448] using wordTrace_append hprefix tailTrace_948448
  have hstable : (prefixWord ++ tailWord_948448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948448).length < 2 ^ (prefixWord ++ tailWord_948448).sum := by decide
  have hdescent : baseEnd_948448 < baseStart_948448 := by decide
  rcases family_descends (prefixWord ++ tailWord_948448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948466 : List Nat := [3, 2, 1, 3, 2, 2, 3, 2, 1, 2, 2]
def baseStart_948466 : Nat := 118140960795 + 948466 * 2 ^ 59
def prefixEnd_948466 : Nat := 4983230072969 + 3 ^ 40 * 948466 * 2
def baseEnd_948466 : Nat := 487018942447391356113091

theorem tailTrace_948466 : CollatzResearch.WordTrace tailWord_948466 prefixEnd_948466 487018942447391356113091 := by
  unfold tailWord_948466
  simp only [CollatzResearch.WordTrace]
  refine ⟨8648349245469285485404313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23062264654584761294411501 8648349245469285485404313)
  ·
    refine ⟨6486261934101964114053235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8648349245469285485404313 6486261934101964114053235)
    ·
      refine ⟨9729392901152946171079853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6486261934101964114053235 9729392901152946171079853)
      ·
        refine ⟨3648522337932354814154945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9729392901152946171079853 3648522337932354814154945)
        ·
          refine ⟨2736391753449266110616209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3648522337932354814154945 2736391753449266110616209)
          ·
            refine ⟨2052293815086949582962157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2736391753449266110616209 2052293815086949582962157)
            ·
              refine ⟨769610180657606093610809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2052293815086949582962157 769610180657606093610809)
              ·
                refine ⟨577207635493204570208107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 769610180657606093610809 577207635493204570208107)
                ·
                  refine ⟨865811453239806855312161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 577207635493204570208107 865811453239806855312161)
                  ·
                    refine ⟨649358589929855141484121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 865811453239806855312161 649358589929855141484121)
                    ·
                      refine ⟨487018942447391356113091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 649358589929855141484121 487018942447391356113091)
                      ·
                        rfl

theorem cell23_948466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_948466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948466 prefixEnd_948466 := by exact prefixLift 948466
  have htrace : WordTrace (prefixWord ++ tailWord_948466) baseStart_948466 baseEnd_948466 := by
    simpa [prefixWord, tailWord_948466, baseEnd_948466] using wordTrace_append hprefix tailTrace_948466
  have hstable : (prefixWord ++ tailWord_948466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948466).length < 2 ^ (prefixWord ++ tailWord_948466).sum := by decide
  have hdescent : baseEnd_948466 < baseStart_948466 := by decide
  rcases family_descends (prefixWord ++ tailWord_948466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948481 : List Nat := [1, 2, 4, 1, 1, 2, 2, 1, 1, 8]
def baseStart_948481 : Nat := 118140960795 + 948481 * 2 ^ 59
def prefixEnd_948481 : Nat := 4983230072969 + 3 ^ 40 * 948481 * 2
def baseEnd_948481 : Nat := 162342214885736265808507

theorem tailTrace_948481 : CollatzResearch.WordTrace tailWord_948481 prefixEnd_948481 162342214885736265808507 := by
  unfold tailWord_948481
  simp only [CollatzResearch.WordTrace]
  refine ⟨34593944076822799503413297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23062629384548533002275531 34593944076822799503413297)
  ·
    refine ⟨25945458057617099627559973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34593944076822799503413297 25945458057617099627559973)
    ·
      refine ⟨4864773385803206180167495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25945458057617099627559973 4864773385803206180167495)
      ·
        refine ⟨7297160078704809270251243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4864773385803206180167495 7297160078704809270251243)
        ·
          refine ⟨10945740118057213905376865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7297160078704809270251243 10945740118057213905376865)
          ·
            refine ⟨8209305088542910429032649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10945740118057213905376865 8209305088542910429032649)
            ·
              refine ⟨6156978816407182821774487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8209305088542910429032649 6156978816407182821774487)
              ·
                refine ⟨9235468224610774232661731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6156978816407182821774487 9235468224610774232661731)
                ·
                  refine ⟨13853202336916161348992597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9235468224610774232661731 13853202336916161348992597)
                  ·
                    refine ⟨162342214885736265808507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13853202336916161348992597 162342214885736265808507)
                    ·
                      rfl

theorem cell23_948481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_948481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948481 prefixEnd_948481 := by exact prefixLift 948481
  have htrace : WordTrace (prefixWord ++ tailWord_948481) baseStart_948481 baseEnd_948481 := by
    simpa [prefixWord, tailWord_948481, baseEnd_948481] using wordTrace_append hprefix tailTrace_948481
  have hstable : (prefixWord ++ tailWord_948481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948481).length < 2 ^ (prefixWord ++ tailWord_948481).sum := by decide
  have hdescent : baseEnd_948481 < baseStart_948481 := by decide
  rcases family_descends (prefixWord ++ tailWord_948481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948491 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 5]
def baseStart_948491 : Nat := 118140960795 + 948491 * 2 ^ 59
def prefixEnd_948491 : Nat := 4983230072969 + 3 ^ 40 * 948491 * 2
def baseEnd_948491 : Nat := 487031779463753758300475

theorem tailTrace_948491 : CollatzResearch.WordTrace tailWord_948491 prefixEnd_948491 487031779463753758300475 := by
  unfold tailWord_948491
  simp only [CollatzResearch.WordTrace]
  refine ⟨34594308806786571211277327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23062872537857714140851551 34594308806786571211277327)
  ·
    refine ⟨51891463210179856816915991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34594308806786571211277327 51891463210179856816915991)
    ·
      refine ⟨77837194815269785225373987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51891463210179856816915991 77837194815269785225373987)
      ·
        refine ⟨116755792222904677838060981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77837194815269785225373987 116755792222904677838060981)
        ·
          refine ⟨10945855520897313547318217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116755792222904677838060981 10945855520897313547318217)
          ·
            refine ⟨8209391640672985160488663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10945855520897313547318217 8209391640672985160488663)
            ·
              refine ⟨12314087461009477740732995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8209391640672985160488663 12314087461009477740732995)
              ·
                refine ⟨18471131191514216611099493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12314087461009477740732995 18471131191514216611099493)
                ·
                  refine ⟨3463337098408915614581155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18471131191514216611099493 3463337098408915614581155)
                  ·
                    refine ⟨5195005647613373421871733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3463337098408915614581155 5195005647613373421871733)
                    ·
                      refine ⟨487031779463753758300475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5195005647613373421871733 487031779463753758300475)
                      ·
                        rfl

theorem cell23_948491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 5].length) (baseStart_948491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948491 prefixEnd_948491 := by exact prefixLift 948491
  have htrace : WordTrace (prefixWord ++ tailWord_948491) baseStart_948491 baseEnd_948491 := by
    simpa [prefixWord, tailWord_948491, baseEnd_948491] using wordTrace_append hprefix tailTrace_948491
  have hstable : (prefixWord ++ tailWord_948491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948491).length < 2 ^ (prefixWord ++ tailWord_948491).sum := by decide
  have hdescent : baseEnd_948491 < baseStart_948491 := by decide
  rcases family_descends (prefixWord ++ tailWord_948491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948538 : List Nat := [3, 1, 1, 1, 4, 2, 1, 1, 1, 5, 3]
def baseStart_948538 : Nat := 118140960795 + 948538 * 2 ^ 59
def prefixEnd_948538 : Nat := 4983230072969 + 3 ^ 40 * 948538 * 2
def baseEnd_948538 : Nat := 487055913054515074412759

theorem tailTrace_948538 : CollatzResearch.WordTrace tailWord_948538 prefixEnd_948538 487055913054515074412759 := by
  unfold tailWord_948538
  simp only [CollatzResearch.WordTrace]
  refine ⟨8649005759404074559559567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23064015358410865492158845 8649005759404074559559567)
  ·
    refine ⟨12973508639106111839339351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8649005759404074559559567 12973508639106111839339351)
    ·
      refine ⟨19460262958659167759009027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12973508639106111839339351 19460262958659167759009027)
      ·
        refine ⟨29190394437988751638513541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19460262958659167759009027 29190394437988751638513541)
        ·
          refine ⟨5473198957122890932221289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29190394437988751638513541 5473198957122890932221289)
          ·
            refine ⟨4104899217842168199165967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5473198957122890932221289 4104899217842168199165967)
            ·
              refine ⟨6157348826763252298748951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4104899217842168199165967 6157348826763252298748951)
              ·
                refine ⟨9236023240144878448123427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6157348826763252298748951 9236023240144878448123427)
                ·
                  refine ⟨13854034860217317672185141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9236023240144878448123427 13854034860217317672185141)
                  ·
                    refine ⟨1298815768145373531767357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13854034860217317672185141 1298815768145373531767357)
                    ·
                      refine ⟨487055913054515074412759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1298815768145373531767357 487055913054515074412759)
                      ·
                        rfl

theorem cell23_948538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 1, 5, 3].length) (baseStart_948538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948538 prefixEnd_948538 := by exact prefixLift 948538
  have htrace : WordTrace (prefixWord ++ tailWord_948538) baseStart_948538 baseEnd_948538 := by
    simpa [prefixWord, tailWord_948538, baseEnd_948538] using wordTrace_append hprefix tailTrace_948538
  have hstable : (prefixWord ++ tailWord_948538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948538).length < 2 ^ (prefixWord ++ tailWord_948538).sum := by decide
  have hdescent : baseEnd_948538 < baseStart_948538 := by decide
  rcases family_descends (prefixWord ++ tailWord_948538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948545 : List Nat := [1, 2, 5, 2, 2, 1, 1, 2, 7]
def baseStart_948545 : Nat := 118140960795 + 948545 * 2 ^ 59
def prefixEnd_948545 : Nat := 4983230072969 + 3 ^ 40 * 948545 * 2
def baseEnd_948545 : Nat := 54117723046566283002803

theorem tailTrace_948545 : CollatzResearch.WordTrace tailWord_948545 prefixEnd_948545 54117723046566283002803 := by
  unfold tailWord_948545
  simp only [CollatzResearch.WordTrace]
  refine ⟨34596278348590938433743089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23064185565727292289162059 34596278348590938433743089)
  ·
    refine ⟨25947208761443203825307317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34596278348590938433743089 25947208761443203825307317)
    ·
      refine ⟨2432550821385300358622561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25947208761443203825307317 2432550821385300358622561)
      ·
        refine ⟨1824413116038975268966921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2432550821385300358622561 1824413116038975268966921)
        ·
          refine ⟨1368309837029231451725191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1824413116038975268966921 1368309837029231451725191)
          ·
            refine ⟨2052464755543847177587787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1368309837029231451725191 2052464755543847177587787)
            ·
              refine ⟨3078697133315770766381681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2052464755543847177587787 3078697133315770766381681)
              ·
                refine ⟨2309022849986828074786261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3078697133315770766381681 2309022849986828074786261)
                ·
                  refine ⟨54117723046566283002803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2309022849986828074786261 54117723046566283002803)
                  ·
                    rfl

theorem cell23_948545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 7].length) (baseStart_948545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948545 prefixEnd_948545 := by exact prefixLift 948545
  have htrace : WordTrace (prefixWord ++ tailWord_948545) baseStart_948545 baseEnd_948545 := by
    simpa [prefixWord, tailWord_948545, baseEnd_948545] using wordTrace_append hprefix tailTrace_948545
  have hstable : (prefixWord ++ tailWord_948545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948545).length < 2 ^ (prefixWord ++ tailWord_948545).sum := by decide
  have hdescent : baseEnd_948545 < baseStart_948545 := by decide
  rcases family_descends (prefixWord ++ tailWord_948545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948558 : List Nat := [4, 1, 1, 1, 1, 1, 2, 5, 2, 5]
def baseStart_948558 : Nat := 118140960795 + 948558 * 2 ^ 59
def prefixEnd_948558 : Nat := 4983230072969 + 3 ^ 40 * 948558 * 2
def baseEnd_948558 : Nat := 162355394222534998720889

theorem tailTrace_948558 : CollatzResearch.WordTrace tailWord_948558 prefixEnd_948558 162355394222534998720889 := by
  unfold tailWord_948558
  simp only [CollatzResearch.WordTrace]
  refine ⟨4324594062192980206745791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23064501665029227769310885 4324594062192980206745791)
  ·
    refine ⟨6486891093289470310118687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4324594062192980206745791 6486891093289470310118687)
    ·
      refine ⟨9730336639934205465178031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6486891093289470310118687 9730336639934205465178031)
      ·
        refine ⟨14595504959901308197767047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9730336639934205465178031 14595504959901308197767047)
        ·
          refine ⟨21893257439851962296650571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14595504959901308197767047 21893257439851962296650571)
          ·
            refine ⟨32839886159777943444975857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21893257439851962296650571 32839886159777943444975857)
            ·
              refine ⟨24629914619833457583731893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32839886159777943444975857 24629914619833457583731893)
              ·
                refine ⟨2309054495609386648474865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24629914619833457583731893 2309054495609386648474865)
                ·
                  refine ⟨1731790871707039986356149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2309054495609386648474865 1731790871707039986356149)
                  ·
                    refine ⟨162355394222534998720889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1731790871707039986356149 162355394222534998720889)
                    ·
                      rfl

theorem cell23_948558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_948558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948558 prefixEnd_948558 := by exact prefixLift 948558
  have htrace : WordTrace (prefixWord ++ tailWord_948558) baseStart_948558 baseEnd_948558 := by
    simpa [prefixWord, tailWord_948558, baseEnd_948558] using wordTrace_append hprefix tailTrace_948558
  have hstable : (prefixWord ++ tailWord_948558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948558).length < 2 ^ (prefixWord ++ tailWord_948558).sum := by decide
  have hdescent : baseEnd_948558 < baseStart_948558 := by decide
  rcases family_descends (prefixWord ++ tailWord_948558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948605 : List Nat := [1, 4, 1, 1, 2, 3, 2, 2, 3, 4]
def baseStart_948605 : Nat := 118140960795 + 948605 * 2 ^ 59
def prefixEnd_948605 : Nat := 4983230072969 + 3 ^ 40 * 948605 * 2
def baseEnd_948605 : Nat := 162363438752788770758317

theorem tailTrace_948605 : CollatzResearch.WordTrace tailWord_948605 prefixEnd_948605 162363438752788770758317 := by
  unfold tailWord_948605
  simp only [CollatzResearch.WordTrace]
  refine ⟨34598466728373568680927269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23065644485582379120618179 34598466728373568680927269)
  ·
    refine ⟨6487212511570044127673863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34598466728373568680927269 6487212511570044127673863)
    ·
      refine ⟨9730818767355066191510795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6487212511570044127673863 9730818767355066191510795)
      ·
        refine ⟨14596228151032599287266193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9730818767355066191510795 14596228151032599287266193)
        ·
          refine ⟨10947171113274449465449645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14596228151032599287266193 10947171113274449465449645)
          ·
            refine ⟨4105189167477918549543617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10947171113274449465449645 4105189167477918549543617)
            ·
              refine ⟨3078891875608438912157713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4105189167477918549543617 3078891875608438912157713)
              ·
                refine ⟨2309168906706329184118285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3078891875608438912157713 2309168906706329184118285)
                ·
                  refine ⟨865938340014873444044357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2309168906706329184118285 865938340014873444044357)
                  ·
                    refine ⟨162363438752788770758317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 865938340014873444044357 162363438752788770758317)
                    ·
                      rfl

theorem cell23_948605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_948605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948605 prefixEnd_948605 := by exact prefixLift 948605
  have htrace : WordTrace (prefixWord ++ tailWord_948605) baseStart_948605 baseEnd_948605 := by
    simpa [prefixWord, tailWord_948605, baseEnd_948605] using wordTrace_append hprefix tailTrace_948605
  have hstable : (prefixWord ++ tailWord_948605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948605).length < 2 ^ (prefixWord ++ tailWord_948605).sum := by decide
  have hdescent : baseEnd_948605 < baseStart_948605 := by decide
  rcases family_descends (prefixWord ++ tailWord_948605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948615 : List Nat := [1, 1, 4, 2, 2, 1, 2, 3, 2, 2, 3]
def baseStart_948615 : Nat := 118140960795 + 948615 * 2 ^ 59
def prefixEnd_948615 : Nat := 4983230072969 + 3 ^ 40 * 948615 * 2
def baseEnd_948615 : Nat := 487095451064911273149905

theorem tailTrace_948615 : CollatzResearch.WordTrace tailWord_948615 prefixEnd_948615 487095451064911273149905 := by
  unfold tailWord_948615
  simp only [CollatzResearch.WordTrace]
  refine ⟨34598831458337340388791299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23065887638891560259194199 34598831458337340388791299)
  ·
    refine ⟨51898247187506010583186949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34598831458337340388791299 51898247187506010583186949)
    ·
      refine ⟨9730921347657376984347553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51898247187506010583186949 9730921347657376984347553)
      ·
        refine ⟨7298191010743032738260665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9730921347657376984347553 7298191010743032738260665)
        ·
          refine ⟨5473643258057274553695499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7298191010743032738260665 5473643258057274553695499)
          ·
            refine ⟨8210464887085911830543249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5473643258057274553695499 8210464887085911830543249)
            ·
              refine ⟨6157848665314433872907437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8210464887085911830543249 6157848665314433872907437)
              ·
                refine ⟨2309193249492912702340289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6157848665314433872907437 2309193249492912702340289)
                ·
                  refine ⟨1731894937119684526755217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2309193249492912702340289 1731894937119684526755217)
                  ·
                    refine ⟨1298921202839763395066413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1731894937119684526755217 1298921202839763395066413)
                    ·
                      refine ⟨487095451064911273149905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1298921202839763395066413 487095451064911273149905)
                      ·
                        rfl

theorem cell23_948615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_948615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948615 prefixEnd_948615 := by exact prefixLift 948615
  have htrace : WordTrace (prefixWord ++ tailWord_948615) baseStart_948615 baseEnd_948615 := by
    simpa [prefixWord, tailWord_948615, baseEnd_948615] using wordTrace_append hprefix tailTrace_948615
  have hstable : (prefixWord ++ tailWord_948615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948615).length < 2 ^ (prefixWord ++ tailWord_948615).sum := by decide
  have hdescent : baseEnd_948615 < baseStart_948615 := by decide
  rcases family_descends (prefixWord ++ tailWord_948615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948632 : List Nat := [2, 1, 2, 5, 1, 2, 1, 2, 2, 2, 3]
def baseStart_948632 : Nat := 118140960795 + 948632 * 2 ^ 59
def prefixEnd_948632 : Nat := 4983230072969 + 3 ^ 40 * 948632 * 2
def baseEnd_948632 : Nat := 487104180236037706637327

theorem tailTrace_948632 : CollatzResearch.WordTrace tailWord_948632 prefixEnd_948632 487104180236037706637327 := by
  unfold tailWord_948632
  simp only [CollatzResearch.WordTrace]
  refine ⟨17299725749637876146080075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23066300999517168194773433 17299725749637876146080075)
  ·
    refine ⟨25949588624456814219120113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17299725749637876146080075 25949588624456814219120113)
    ·
      refine ⟨19462191468342610664340085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25949588624456814219120113 19462191468342610664340085)
      ·
        refine ⟨1824580450157119749781883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19462191468342610664340085 1824580450157119749781883)
        ·
          refine ⟨2736870675235679624672825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1824580450157119749781883 2736870675235679624672825)
          ·
            refine ⟨2052653006426759718504619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2736870675235679624672825 2052653006426759718504619)
            ·
              refine ⟨3078979509640139577756929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2052653006426759718504619 3078979509640139577756929)
              ·
                refine ⟨2309234632230104683317697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3078979509640139577756929 2309234632230104683317697)
                ·
                  refine ⟨1731925974172578512488273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2309234632230104683317697 1731925974172578512488273)
                  ·
                    refine ⟨1298944480629433884366205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1731925974172578512488273 1298944480629433884366205)
                    ·
                      refine ⟨487104180236037706637327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1298944480629433884366205 487104180236037706637327)
                      ·
                        rfl

theorem cell23_948632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_948632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948632 prefixEnd_948632 := by exact prefixLift 948632
  have htrace : WordTrace (prefixWord ++ tailWord_948632) baseStart_948632 baseEnd_948632 := by
    simpa [prefixWord, tailWord_948632, baseEnd_948632] using wordTrace_append hprefix tailTrace_948632
  have hstable : (prefixWord ++ tailWord_948632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948632).length < 2 ^ (prefixWord ++ tailWord_948632).sum := by decide
  have hdescent : baseEnd_948632 < baseStart_948632 := by decide
  rcases family_descends (prefixWord ++ tailWord_948632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948639 : List Nat := [1, 1, 2, 5, 1, 1, 5, 2, 1, 4]
def baseStart_948639 : Nat := 118140960795 + 948639 * 2 ^ 59
def prefixEnd_948639 : Nat := 4983230072969 + 3 ^ 40 * 948639 * 2
def baseEnd_948639 : Nat := 162369258200206393083265

theorem tailTrace_948639 : CollatzResearch.WordTrace tailWord_948639 prefixEnd_948639 162369258200206393083265 := by
  unfold tailWord_948639
  simp only [CollatzResearch.WordTrace]
  refine ⟨34599706810250392487664971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23066471206833594991776647 34599706810250392487664971)
  ·
    refine ⟨51899560215375588731497457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34599706810250392487664971 51899560215375588731497457)
    ·
      refine ⟨38924670161531691548623093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51899560215375588731497457 38924670161531691548623093)
      ·
        refine ⟨3649187827643596082683415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38924670161531691548623093 3649187827643596082683415)
        ·
          refine ⟨5473781741465394124025123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3649187827643596082683415 5473781741465394124025123)
          ·
            refine ⟨8210672612198091186037685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5473781741465394124025123 8210672612198091186037685)
            ·
              refine ⟨769750557393571048691033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8210672612198091186037685 769750557393571048691033)
              ·
                refine ⟨577312918045178286518275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 769750557393571048691033 577312918045178286518275)
                ·
                  refine ⟨865969377067767429777413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 577312918045178286518275 865969377067767429777413)
                  ·
                    refine ⟨162369258200206393083265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 865969377067767429777413 162369258200206393083265)
                    ·
                      rfl

theorem cell23_948639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 2, 1, 4].length) (baseStart_948639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948639 prefixEnd_948639 := by exact prefixLift 948639
  have htrace : WordTrace (prefixWord ++ tailWord_948639) baseStart_948639 baseEnd_948639 := by
    simpa [prefixWord, tailWord_948639, baseEnd_948639] using wordTrace_append hprefix tailTrace_948639
  have hstable : (prefixWord ++ tailWord_948639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948639).length < 2 ^ (prefixWord ++ tailWord_948639).sum := by decide
  have hdescent : baseEnd_948639 < baseStart_948639 := by decide
  rcases family_descends (prefixWord ++ tailWord_948639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948665 : List Nat := [1, 2, 1, 4, 3, 2, 1, 1, 3, 5]
def baseStart_948665 : Nat := 118140960795 + 948665 * 2 ^ 59
def prefixEnd_948665 : Nat := 4983230072969 + 3 ^ 40 * 948665 * 2
def baseEnd_948665 : Nat := 162373708365878692508225

theorem tailTrace_948665 : CollatzResearch.WordTrace tailWord_948665 prefixEnd_948665 162373708365878692508225 := by
  unfold tailWord_948665
  simp only [CollatzResearch.WordTrace]
  refine ⟨34600655108156198928111449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23067103405437465952074299 34600655108156198928111449)
  ·
    refine ⟨25950491331117149196083587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34600655108156198928111449 25950491331117149196083587)
    ·
      refine ⟨38925736996675723794125381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25950491331117149196083587 38925736996675723794125381)
      ·
        refine ⟨7298575686876698211398509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38925736996675723794125381 7298575686876698211398509)
        ·
          refine ⟨2736965882578761829274441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7298575686876698211398509 2736965882578761829274441)
          ·
            refine ⟨2052724411934071371955831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2736965882578761829274441 2052724411934071371955831)
            ·
              refine ⟨3079086617901107057933747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2052724411934071371955831 3079086617901107057933747)
              ·
                refine ⟨4618629926851660586900621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3079086617901107057933747 4618629926851660586900621)
                ·
                  refine ⟨1731986222569372720087733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4618629926851660586900621 1731986222569372720087733)
                  ·
                    refine ⟨162373708365878692508225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1731986222569372720087733 162373708365878692508225)
                    ·
                      rfl

theorem cell23_948665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 5].length) (baseStart_948665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948665 prefixEnd_948665 := by exact prefixLift 948665
  have htrace : WordTrace (prefixWord ++ tailWord_948665) baseStart_948665 baseEnd_948665 := by
    simpa [prefixWord, tailWord_948665, baseEnd_948665] using wordTrace_append hprefix tailTrace_948665
  have hstable : (prefixWord ++ tailWord_948665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948665).length < 2 ^ (prefixWord ++ tailWord_948665).sum := by decide
  have hdescent : baseEnd_948665 < baseStart_948665 := by decide
  rcases family_descends (prefixWord ++ tailWord_948665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948682 : List Nat := [3, 1, 2, 1, 2, 2, 5, 1, 1, 5]
def baseStart_948682 : Nat := 118140960795 + 948682 * 2 ^ 59
def prefixEnd_948682 : Nat := 4983230072969 + 3 ^ 40 * 948682 * 2
def baseEnd_948682 : Nat := 162376618089587503670699

theorem tailTrace_948682 : CollatzResearch.WordTrace tailWord_948682 prefixEnd_948682 162376618089587503670699 := by
  unfold tailWord_948682
  simp only [CollatzResearch.WordTrace]
  refine ⟨8650318787273652707870075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23067516766063073887653533 8650318787273652707870075)
  ·
    refine ⟨12975478180910479061805113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8650318787273652707870075 12975478180910479061805113)
    ·
      refine ⟨9731608635682859296353835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12975478180910479061805113 9731608635682859296353835)
      ·
        refine ⟨14597412953524288944530753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9731608635682859296353835 14597412953524288944530753)
        ·
          refine ⟨10948059715143216708398065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14597412953524288944530753 10948059715143216708398065)
          ·
            refine ⟨8211044786357412531298549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10948059715143216708398065 8211044786357412531298549)
            ·
              refine ⟨769785448721007424809239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8211044786357412531298549 769785448721007424809239)
              ·
                refine ⟨1154678173081511137213859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 769785448721007424809239 1154678173081511137213859)
                ·
                  refine ⟨1732017259622266705820789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1154678173081511137213859 1732017259622266705820789)
                  ·
                    refine ⟨162376618089587503670699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1732017259622266705820789 162376618089587503670699)
                    ·
                      rfl

theorem cell23_948682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 1, 5].length) (baseStart_948682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948682 prefixEnd_948682 := by exact prefixLift 948682
  have htrace : WordTrace (prefixWord ++ tailWord_948682) baseStart_948682 baseEnd_948682 := by
    simpa [prefixWord, tailWord_948682, baseEnd_948682] using wordTrace_append hprefix tailTrace_948682
  have hstable : (prefixWord ++ tailWord_948682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948682).length < 2 ^ (prefixWord ++ tailWord_948682).sum := by decide
  have hdescent : baseEnd_948682 < baseStart_948682 := by decide
  rcases family_descends (prefixWord ++ tailWord_948682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948690 : List Nat := [3, 2, 2, 4, 2, 1, 2, 2, 1, 4]
def baseStart_948690 : Nat := 118140960795 + 948690 * 2 ^ 59
def prefixEnd_948690 : Nat := 4983230072969 + 3 ^ 40 * 948690 * 2
def baseEnd_948690 : Nat := 162377987371332826570687

theorem tailTrace_948690 : CollatzResearch.WordTrace tailWord_948690 prefixEnd_948690 162377987371332826570687 := by
  unfold tailWord_948690
  simp only [CollatzResearch.WordTrace]
  refine ⟨8650391733266407049442881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23067711288710418798514349 8650391733266407049442881)
  ·
    refine ⟨6487793799949805287082161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8650391733266407049442881 6487793799949805287082161)
    ·
      refine ⟨4865845349962353965311621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6487793799949805287082161 4865845349962353965311621)
      ·
        refine ⟨912346003117941368495929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4865845349962353965311621 912346003117941368495929)
        ·
          refine ⟨684259502338456026371947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 912346003117941368495929 684259502338456026371947)
          ·
            refine ⟨1026389253507684039557921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 684259502338456026371947 1026389253507684039557921)
            ·
              refine ⟨769791940130763029668441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1026389253507684039557921 769791940130763029668441)
              ·
                refine ⟨577343955098072272251331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 769791940130763029668441 577343955098072272251331)
                ·
                  refine ⟨866015932647108408376997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 577343955098072272251331 866015932647108408376997)
                  ·
                    refine ⟨162377987371332826570687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 866015932647108408376997 162377987371332826570687)
                    ·
                      rfl

theorem cell23_948690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_948690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948690 prefixEnd_948690 := by exact prefixLift 948690
  have htrace : WordTrace (prefixWord ++ tailWord_948690) baseStart_948690 baseEnd_948690 := by
    simpa [prefixWord, tailWord_948690, baseEnd_948690] using wordTrace_append hprefix tailTrace_948690
  have hstable : (prefixWord ++ tailWord_948690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948690).length < 2 ^ (prefixWord ++ tailWord_948690).sum := by decide
  have hdescent : baseEnd_948690 < baseStart_948690 := by decide
  rcases family_descends (prefixWord ++ tailWord_948690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948705 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 5, 2, 3]
def baseStart_948705 : Nat := 118140960795 + 948705 * 2 ^ 59
def prefixEnd_948705 : Nat := 4983230072969 + 3 ^ 40 * 948705 * 2
def baseEnd_948705 : Nat := 487141664323815921024491

theorem tailTrace_948705 : CollatzResearch.WordTrace tailWord_948705 prefixEnd_948705 487141664323815921024491 := by
  unfold tailWord_948705
  simp only [CollatzResearch.WordTrace]
  refine ⟨34602114028011285759567569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23068076018674190506378379 34602114028011285759567569)
  ·
    refine ⟨25951585521008464319675677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34602114028011285759567569 25951585521008464319675677)
    ·
      refine ⟨9731844570378174119878379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25951585521008464319675677 9731844570378174119878379)
      ·
        refine ⟨14597766855567261179817569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9731844570378174119878379 14597766855567261179817569)
        ·
          refine ⟨10948325141675445884863177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14597766855567261179817569 10948325141675445884863177)
          ·
            refine ⟨8211243856256584413647383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10948325141675445884863177 8211243856256584413647383)
            ·
              refine ⟨12316865784384876620471075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8211243856256584413647383 12316865784384876620471075)
              ·
                refine ⟨18475298676577314930706613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12316865784384876620471075 18475298676577314930706613)
                ·
                  refine ⟨1732059250929123274753745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18475298676577314930706613 1732059250929123274753745)
                  ·
                    refine ⟨1299044438196842456065309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1732059250929123274753745 1299044438196842456065309)
                    ·
                      refine ⟨487141664323815921024491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1299044438196842456065309 487141664323815921024491)
                      ·
                        rfl

theorem cell23_948705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_948705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948705 prefixEnd_948705 := by exact prefixLift 948705
  have htrace : WordTrace (prefixWord ++ tailWord_948705) baseStart_948705 baseEnd_948705 := by
    simpa [prefixWord, tailWord_948705, baseEnd_948705] using wordTrace_append hprefix tailTrace_948705
  have hstable : (prefixWord ++ tailWord_948705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948705).length < 2 ^ (prefixWord ++ tailWord_948705).sum := by decide
  have hdescent : baseEnd_948705 < baseStart_948705 := by decide
  rcases family_descends (prefixWord ++ tailWord_948705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948712 : List Nat := [2, 1, 4, 1, 1, 3, 2, 3, 2, 4]
def baseStart_948712 : Nat := 118140960795 + 948712 * 2 ^ 59
def prefixEnd_948712 : Nat := 4983230072969 + 3 ^ 40 * 948712 * 2
def baseEnd_948712 : Nat := 162381752896132464545653

theorem tailTrace_948712 : CollatzResearch.WordTrace tailWord_948712 prefixEnd_948712 162381752896132464545653 := by
  unfold tailWord_948712
  simp only [CollatzResearch.WordTrace]
  refine ⟨17301184669492962977536195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23068246225990617303381593 17301184669492962977536195)
  ·
    refine ⟨25951777004239444466304293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17301184669492962977536195 25951777004239444466304293)
    ·
      refine ⟨4865958188294895837432055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25951777004239444466304293 4865958188294895837432055)
      ·
        refine ⟨7298937282442343756148083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4865958188294895837432055 7298937282442343756148083)
        ·
          refine ⟨10948405923663515634222125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7298937282442343756148083 10948405923663515634222125)
          ·
            refine ⟨4105652221373818362833297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10948405923663515634222125 4105652221373818362833297)
            ·
              refine ⟨3079239166030363772124973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4105652221373818362833297 3079239166030363772124973)
              ·
                refine ⟨1154714687261386414546865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3079239166030363772124973 1154714687261386414546865)
                ·
                  refine ⟨866036015446039810910149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1154714687261386414546865 866036015446039810910149)
                  ·
                    refine ⟨162381752896132464545653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 866036015446039810910149 162381752896132464545653)
                    ·
                      rfl

theorem cell23_948712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_948712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948712 prefixEnd_948712 := by exact prefixLift 948712
  have htrace : WordTrace (prefixWord ++ tailWord_948712) baseStart_948712 baseEnd_948712 := by
    simpa [prefixWord, tailWord_948712, baseEnd_948712] using wordTrace_append hprefix tailTrace_948712
  have hstable : (prefixWord ++ tailWord_948712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948712).length < 2 ^ (prefixWord ++ tailWord_948712).sum := by decide
  have hdescent : baseEnd_948712 < baseStart_948712 := by decide
  rcases family_descends (prefixWord ++ tailWord_948712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948715 : List Nat := [1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 4]
def baseStart_948715 : Nat := 118140960795 + 948715 * 2 ^ 59
def prefixEnd_948715 : Nat := 4983230072969 + 3 ^ 40 * 948715 * 2
def baseEnd_948715 : Nat := 487146799130360881899445

theorem tailTrace_948715 : CollatzResearch.WordTrace tailWord_948715 prefixEnd_948715 487146799130360881899445 := by
  unfold tailWord_948715
  simp only [CollatzResearch.WordTrace]
  refine ⟨34602478757975057467431599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23068319171983371644954399 34602478757975057467431599)
  ·
    refine ⟨51903718136962586201147399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34602478757975057467431599 51903718136962586201147399)
    ·
      refine ⟨77855577205443879301721099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51903718136962586201147399 77855577205443879301721099)
      ·
        refine ⟨116783365808165818952581649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77855577205443879301721099 116783365808165818952581649)
        ·
          refine ⟨87587524356124364214436237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116783365808165818952581649 87587524356124364214436237)
          ·
            refine ⟨32845321633546636580413589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87587524356124364214436237 32845321633546636580413589)
            ·
              refine ⟨1539624451572498589706887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32845321633546636580413589 1539624451572498589706887)
              ·
                refine ⟨2309436677358747884560331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1539624451572498589706887 2309436677358747884560331)
                ·
                  refine ⟨3464155016038121826840497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2309436677358747884560331 3464155016038121826840497)
                  ·
                    refine ⟨2598116262028591370130373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3464155016038121826840497 2598116262028591370130373)
                    ·
                      refine ⟨487146799130360881899445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2598116262028591370130373 487146799130360881899445)
                      ·
                        rfl

theorem cell23_948715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 4].length) (baseStart_948715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948715 prefixEnd_948715 := by exact prefixLift 948715
  have htrace : WordTrace (prefixWord ++ tailWord_948715) baseStart_948715 baseEnd_948715 := by
    simpa [prefixWord, tailWord_948715, baseEnd_948715] using wordTrace_append hprefix tailTrace_948715
  have hstable : (prefixWord ++ tailWord_948715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948715).length < 2 ^ (prefixWord ++ tailWord_948715).sum := by decide
  have hdescent : baseEnd_948715 < baseStart_948715 := by decide
  rcases family_descends (prefixWord ++ tailWord_948715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948735 : List Nat := [1, 1, 2, 2, 1, 2, 3, 4, 1, 3, 3]
def baseStart_948735 : Nat := 118140960795 + 948735 * 2 ^ 59
def prefixEnd_948735 : Nat := 4983230072969 + 3 ^ 40 * 948735 * 2
def baseEnd_948735 : Nat := 487157068743450803649353

theorem tailTrace_948735 : CollatzResearch.WordTrace tailWord_948735 prefixEnd_948735 487157068743450803649353 := by
  unfold tailWord_948735
  simp only [CollatzResearch.WordTrace]
  refine ⟨34603208217902600883159659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23068805478601733922106439 34603208217902600883159659)
  ·
    refine ⟨51904812326853901324739489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34603208217902600883159659 51904812326853901324739489)
    ·
      refine ⟨38928609245140425993554617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51904812326853901324739489 38928609245140425993554617)
      ·
        refine ⟨29196456933855319495165963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38928609245140425993554617 29196456933855319495165963)
        ·
          refine ⟨43794685400782979242748945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29196456933855319495165963 43794685400782979242748945)
          ·
            refine ⟨32846014050587234432061709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43794685400782979242748945 32846014050587234432061709)
            ·
              refine ⟨12317255268970212912023141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32846014050587234432061709 12317255268970212912023141)
              ·
                refine ⟨2309485362931914921004339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12317255268970212912023141 2309485362931914921004339)
                ·
                  refine ⟨3464228044397872381506509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2309485362931914921004339 3464228044397872381506509)
                  ·
                    refine ⟨1299085516649202143064941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3464228044397872381506509 1299085516649202143064941)
                    ·
                      refine ⟨487157068743450803649353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1299085516649202143064941 487157068743450803649353)
                      ·
                        rfl

theorem cell23_948735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 3, 3].length) (baseStart_948735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948735 prefixEnd_948735 := by exact prefixLift 948735
  have htrace : WordTrace (prefixWord ++ tailWord_948735) baseStart_948735 baseEnd_948735 := by
    simpa [prefixWord, tailWord_948735, baseEnd_948735] using wordTrace_append hprefix tailTrace_948735
  have hstable : (prefixWord ++ tailWord_948735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948735).length < 2 ^ (prefixWord ++ tailWord_948735).sum := by decide
  have hdescent : baseEnd_948735 < baseStart_948735 := by decide
  rcases family_descends (prefixWord ++ tailWord_948735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948762 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 5, 3, 2]
def baseStart_948762 : Nat := 118140960795 + 948762 * 2 ^ 59
def prefixEnd_948762 : Nat := 4983230072969 + 3 ^ 40 * 948762 * 2
def baseEnd_948762 : Nat := 487170932721122198011729

theorem tailTrace_948762 : CollatzResearch.WordTrace tailWord_948762 prefixEnd_948762 487170932721122198011729 := by
  unfold tailWord_948762
  simp only [CollatzResearch.WordTrace]
  refine ⟨8651048247201196123598135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23069461992536522996261693 8651048247201196123598135)
  ·
    refine ⟨12976572370801794185397203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8651048247201196123598135 12976572370801794185397203)
    ·
      refine ⟨19464858556202691278095805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12976572370801794185397203 19464858556202691278095805)
      ·
        refine ⟨7299321958576009229285927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19464858556202691278095805 7299321958576009229285927)
        ·
          refine ⟨10948982937864013843928891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7299321958576009229285927 10948982937864013843928891)
          ·
            refine ⟨16423474406796020765893337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10948982937864013843928891 16423474406796020765893337)
            ·
              refine ⟨12317605805097015574420003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16423474406796020765893337 12317605805097015574420003)
              ·
                refine ⟨18476408707645523361630005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12317605805097015574420003 18476408707645523361630005)
                ·
                  refine ⟨1732163316341767815152813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18476408707645523361630005 1732163316341767815152813)
                  ·
                    refine ⟨649561243628162930682305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1732163316341767815152813 649561243628162930682305)
                    ·
                      refine ⟨487170932721122198011729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 649561243628162930682305 487170932721122198011729)
                      ·
                        rfl

theorem cell23_948762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_948762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948762 prefixEnd_948762 := by exact prefixLift 948762
  have htrace : WordTrace (prefixWord ++ tailWord_948762) baseStart_948762 baseEnd_948762 := by
    simpa [prefixWord, tailWord_948762, baseEnd_948762] using wordTrace_append hprefix tailTrace_948762
  have hstable : (prefixWord ++ tailWord_948762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948762).length < 2 ^ (prefixWord ++ tailWord_948762).sum := by decide
  have hdescent : baseEnd_948762 < baseStart_948762 := by decide
  rcases family_descends (prefixWord ++ tailWord_948762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948792 : List Nat := [2, 1, 2, 1, 4, 1, 2, 1, 3, 4, 2]
def baseStart_948792 : Nat := 118140960795 + 948792 * 2 ^ 59
def prefixEnd_948792 : Nat := 4983230072969 + 3 ^ 40 * 948792 * 2
def baseEnd_948792 : Nat := 487186337140757080636591

theorem tailTrace_948792 : CollatzResearch.WordTrace tailWord_948792 prefixEnd_948792 487186337140757080636591 := by
  unfold tailWord_948792
  simp only [CollatzResearch.WordTrace]
  refine ⟨17302643589348049808992315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23070191452464066411989753 17302643589348049808992315)
  ·
    refine ⟨25953965384022074713488473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17302643589348049808992315 25953965384022074713488473)
    ·
      refine ⟨19465474038016556035116355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25953965384022074713488473 19465474038016556035116355)
      ·
        refine ⟨29198211057024834052674533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19465474038016556035116355 29198211057024834052674533)
        ·
          refine ⟨5474664573192156384876475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29198211057024834052674533 5474664573192156384876475)
          ·
            refine ⟨8211996859788234577314713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5474664573192156384876475 8211996859788234577314713)
            ·
              refine ⟨6158997644841175932986035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8211996859788234577314713 6158997644841175932986035)
              ·
                refine ⟨9238496467261763899479053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6158997644841175932986035 9238496467261763899479053)
                ·
                  refine ⟨3464436175223161462304645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9238496467261763899479053 3464436175223161462304645)
                  ·
                    refine ⟨649581782854342774182121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3464436175223161462304645 649581782854342774182121)
                    ·
                      refine ⟨487186337140757080636591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 649581782854342774182121 487186337140757080636591)
                      ·
                        rfl

theorem cell23_948792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 3, 4, 2].length) (baseStart_948792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948792 prefixEnd_948792 := by exact prefixLift 948792
  have htrace : WordTrace (prefixWord ++ tailWord_948792) baseStart_948792 baseEnd_948792 := by
    simpa [prefixWord, tailWord_948792, baseEnd_948792] using wordTrace_append hprefix tailTrace_948792
  have hstable : (prefixWord ++ tailWord_948792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948792).length < 2 ^ (prefixWord ++ tailWord_948792).sum := by decide
  have hdescent : baseEnd_948792 < baseStart_948792 := by decide
  rcases family_descends (prefixWord ++ tailWord_948792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948804 : List Nat := [2, 3, 5, 1, 1, 1, 3, 2, 1, 2, 2]
def baseStart_948804 : Nat := 118140960795 + 948804 * 2 ^ 59
def prefixEnd_948804 : Nat := 4983230072969 + 3 ^ 40 * 948804 * 2
def baseEnd_948804 : Nat := 487192498908611033686537

theorem tailTrace_948804 : CollatzResearch.WordTrace tailWord_948804 prefixEnd_948804 487192498908611033686537 := by
  unfold tailWord_948804
  simp only [CollatzResearch.WordTrace]
  refine ⟨17302862427326312833710733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23070483236435083778280977 17302862427326312833710733)
  ·
    refine ⟨6488573410247367312641525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17302862427326312833710733 6488573410247367312641525)
    ·
      refine ⟨608303757210690685560143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6488573410247367312641525 608303757210690685560143)
      ·
        refine ⟨912455635816036028340215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 608303757210690685560143 912455635816036028340215)
        ·
          refine ⟨1368683453724054042510323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 912455635816036028340215 1368683453724054042510323)
          ·
            refine ⟨2053025180586081063765485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1368683453724054042510323 2053025180586081063765485)
            ·
              refine ⟨769884442719780398912057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2053025180586081063765485 769884442719780398912057)
              ·
                refine ⟨577413332039835299184043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 769884442719780398912057 577413332039835299184043)
                ·
                  refine ⟨866119998059752948776065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 577413332039835299184043 866119998059752948776065)
                  ·
                    refine ⟨649589998544814711582049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 866119998059752948776065 649589998544814711582049)
                    ·
                      refine ⟨487192498908611033686537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 649589998544814711582049 487192498908611033686537)
                      ·
                        rfl

theorem cell23_948804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_948804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948804 prefixEnd_948804 := by exact prefixLift 948804
  have htrace : WordTrace (prefixWord ++ tailWord_948804) baseStart_948804 baseEnd_948804 := by
    simpa [prefixWord, tailWord_948804, baseEnd_948804] using wordTrace_append hprefix tailTrace_948804
  have hstable : (prefixWord ++ tailWord_948804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948804).length < 2 ^ (prefixWord ++ tailWord_948804).sum := by decide
  have hdescent : baseEnd_948804 < baseStart_948804 := by decide
  rcases family_descends (prefixWord ++ tailWord_948804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948815 : List Nat := [1, 1, 2, 1, 1, 2, 7, 1, 7]
def baseStart_948815 : Nat := 118140960795 + 948815 * 2 ^ 59
def prefixEnd_948815 : Nat := 4983230072969 + 3 ^ 40 * 948815 * 2
def baseEnd_948815 : Nat := 54133127466201165627665

theorem tailTrace_948815 : CollatzResearch.WordTrace tailWord_948815 prefixEnd_948815 54133127466201165627665 := by
  unfold tailWord_948815
  simp only [CollatzResearch.WordTrace]
  refine ⟨34606126057612774546071899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23070750705075183030714599 34606126057612774546071899)
  ·
    refine ⟨51909189086419161819107849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34606126057612774546071899 51909189086419161819107849)
    ·
      refine ⟨38931891814814371364330887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51909189086419161819107849 38931891814814371364330887)
      ·
        refine ⟨58397837722221557046496331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38931891814814371364330887 58397837722221557046496331)
        ·
          refine ⟨87596756583332335569744497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58397837722221557046496331 87596756583332335569744497)
          ·
            refine ⟨65697567437499251677308373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87596756583332335569744497 65697567437499251677308373)
            ·
              refine ⟨1539786736816388711186915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 65697567437499251677308373 1539786736816388711186915)
              ·
                refine ⟨2309680105224583066780373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1539786736816388711186915 2309680105224583066780373)
                ·
                  refine ⟨54133127466201165627665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2309680105224583066780373 54133127466201165627665)
                  ·
                    rfl

theorem cell23_948815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 7].length) (baseStart_948815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948815 prefixEnd_948815 := by exact prefixLift 948815
  have htrace : WordTrace (prefixWord ++ tailWord_948815) baseStart_948815 baseEnd_948815 := by
    simpa [prefixWord, tailWord_948815, baseEnd_948815] using wordTrace_append hprefix tailTrace_948815
  have hstable : (prefixWord ++ tailWord_948815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948815).length < 2 ^ (prefixWord ++ tailWord_948815).sum := by decide
  have hdescent : baseEnd_948815 < baseStart_948815 := by decide
  rcases family_descends (prefixWord ++ tailWord_948815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948830 : List Nat := [4, 4, 1, 2, 1, 1, 1, 1, 3, 3, 2]
def baseStart_948830 : Nat := 118140960795 + 948830 * 2 ^ 59
def prefixEnd_948830 : Nat := 4983230072969 + 3 ^ 40 * 948830 * 2
def baseEnd_948830 : Nat := 487205849405627931961417

theorem tailTrace_948830 : CollatzResearch.WordTrace tailWord_948830 prefixEnd_948830 487205849405627931961417 := by
  unfold tailWord_948830
  simp only [CollatzResearch.WordTrace]
  refine ⟨4325834144069804013483493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23071115435038954738578629 4325834144069804013483493)
  ·
    refine ⟨811093902013088252528155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4325834144069804013483493 811093902013088252528155)
    ·
      refine ⟨1216640853019632378792233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 811093902013088252528155 1216640853019632378792233)
      ·
        refine ⟨912480639764724284094175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1216640853019632378792233 912480639764724284094175)
        ·
          refine ⟨1368720959647086426141263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 912480639764724284094175 1368720959647086426141263)
          ·
            refine ⟨2053081439470629639211895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1368720959647086426141263 2053081439470629639211895)
            ·
              refine ⟨3079622159205944458817843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2053081439470629639211895 3079622159205944458817843)
              ·
                refine ⟨4619433238808916688226765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3079622159205944458817843 4619433238808916688226765)
                ·
                  refine ⟨1732287464553343758085037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4619433238808916688226765 1732287464553343758085037)
                  ·
                    refine ⟨649607799207503909281889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1732287464553343758085037 649607799207503909281889)
                    ·
                      refine ⟨487205849405627931961417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 649607799207503909281889 487205849405627931961417)
                      ·
                        rfl

theorem cell23_948830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_948830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948830 prefixEnd_948830 := by exact prefixLift 948830
  have htrace : WordTrace (prefixWord ++ tailWord_948830) baseStart_948830 baseEnd_948830 := by
    simpa [prefixWord, tailWord_948830, baseEnd_948830] using wordTrace_append hprefix tailTrace_948830
  have hstable : (prefixWord ++ tailWord_948830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948830).length < 2 ^ (prefixWord ++ tailWord_948830).sum := by decide
  have hdescent : baseEnd_948830 < baseStart_948830 := by decide
  rcases family_descends (prefixWord ++ tailWord_948830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948855 : List Nat := [1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 5]
def baseStart_948855 : Nat := 118140960795 + 948855 * 2 ^ 59
def prefixEnd_948855 : Nat := 4983230072969 + 3 ^ 40 * 948855 * 2
def baseEnd_948855 : Nat := 487218686421990334148801

theorem tailTrace_948855 : CollatzResearch.WordTrace tailWord_948855 prefixEnd_948855 487218686421990334148801 := by
  unfold tailWord_948855
  simp only [CollatzResearch.WordTrace]
  refine ⟨34607584977467861377528019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23071723318311907585018679 34607584977467861377528019)
  ·
    refine ⟨51911377466201792066292029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34607584977467861377528019 51911377466201792066292029)
    ·
      refine ⟨19466766549825672024859511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51911377466201792066292029 19466766549825672024859511)
      ·
        refine ⟨29200149824738508037289267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19466766549825672024859511 29200149824738508037289267)
        ·
          refine ⟨43800224737107762055933901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29200149824738508037289267 43800224737107762055933901)
          ·
            refine ⟨16425084276415410770975213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43800224737107762055933901 16425084276415410770975213)
            ·
              refine ⟨6159406603655779039115705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16425084276415410770975213 6159406603655779039115705)
              ·
                refine ⟨4619554952741834279336779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6159406603655779039115705 4619554952741834279336779)
                ·
                  refine ⟨6929332429112751419005169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4619554952741834279336779 6929332429112751419005169)
                  ·
                    refine ⟨5196999321834563564253877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6929332429112751419005169 5196999321834563564253877)
                    ·
                      refine ⟨487218686421990334148801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5196999321834563564253877 487218686421990334148801)
                      ·
                        rfl

theorem cell23_948855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_948855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948855 prefixEnd_948855 := by exact prefixLift 948855
  have htrace : WordTrace (prefixWord ++ tailWord_948855) baseStart_948855 baseEnd_948855 := by
    simpa [prefixWord, tailWord_948855, baseEnd_948855] using wordTrace_append hprefix tailTrace_948855
  have hstable : (prefixWord ++ tailWord_948855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948855).length < 2 ^ (prefixWord ++ tailWord_948855).sum := by decide
  have hdescent : baseEnd_948855 < baseStart_948855 := by decide
  rcases family_descends (prefixWord ++ tailWord_948855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948896 : List Nat := [2, 1, 1, 4, 5, 1, 1, 1, 2, 5]
def baseStart_948896 : Nat := 118140960795 + 948896 * 2 ^ 59
def prefixEnd_948896 : Nat := 4983230072969 + 3 ^ 40 * 948896 * 2
def baseEnd_948896 : Nat := 162413246376274891245371

theorem tailTrace_948896 : CollatzResearch.WordTrace tailWord_948896 prefixEnd_948896 162413246376274891245371 := by
  unfold tailWord_948896
  simp only [CollatzResearch.WordTrace]
  refine ⟨17304540185159662689885271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23072720246879550253180361 17304540185159662689885271)
  ·
    refine ⟨25956810277739494034827907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17304540185159662689885271 25956810277739494034827907)
    ·
      refine ⟨38935215416609241052241861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25956810277739494034827907 38935215416609241052241861)
      ·
        refine ⟨7300352890614232697295349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38935215416609241052241861 7300352890614232697295349)
        ·
          refine ⟨684408083495084315371439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7300352890614232697295349 684408083495084315371439)
          ·
            refine ⟨1026612125242626473057159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 684408083495084315371439 1026612125242626473057159)
            ·
              refine ⟨1539918187863939709585739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1026612125242626473057159 1539918187863939709585739)
              ·
                refine ⟨2309877281795909564378609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1539918187863939709585739 2309877281795909564378609)
                ·
                  refine ⟨1732407961346932173283957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2309877281795909564378609 1732407961346932173283957)
                  ·
                    refine ⟨162413246376274891245371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1732407961346932173283957 162413246376274891245371)
                    ·
                      rfl

theorem cell23_948896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 2, 5].length) (baseStart_948896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948896 prefixEnd_948896 := by exact prefixLift 948896
  have htrace : WordTrace (prefixWord ++ tailWord_948896) baseStart_948896 baseEnd_948896 := by
    simpa [prefixWord, tailWord_948896, baseEnd_948896] using wordTrace_append hprefix tailTrace_948896
  have hstable : (prefixWord ++ tailWord_948896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948896).length < 2 ^ (prefixWord ++ tailWord_948896).sum := by decide
  have hdescent : baseEnd_948896 < baseStart_948896 := by decide
  rcases family_descends (prefixWord ++ tailWord_948896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948926 : List Nat := [4, 2, 1, 1, 2, 1, 1, 6, 1, 4]
def baseStart_948926 : Nat := 118140960795 + 948926 * 2 ^ 59
def prefixEnd_948926 : Nat := 4983230072969 + 3 ^ 40 * 948926 * 2
def baseEnd_948926 : Nat := 162418381182819852120325

theorem tailTrace_948926 : CollatzResearch.WordTrace tailWord_948926 prefixEnd_948926 162418381182819852120325 := by
  unfold tailWord_948926
  simp only [CollatzResearch.WordTrace]
  refine ⟨4326271820026330062920329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23073449706807093668908421 4326271820026330062920329)
  ·
    refine ⟨3244703865019747547190247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4326271820026330062920329 3244703865019747547190247)
    ·
      refine ⟨4867055797529621320785371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3244703865019747547190247 4867055797529621320785371)
      ·
        refine ⟨7300583696294431981178057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4867055797529621320785371 7300583696294431981178057)
        ·
          refine ⟨5475437772220823985883543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7300583696294431981178057 5475437772220823985883543)
          ·
            refine ⟨8213156658331235978825315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5475437772220823985883543 8213156658331235978825315)
            ·
              refine ⟨12319734987496853968237973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8213156658331235978825315 12319734987496853968237973)
              ·
                refine ⟨577487577538915029761155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12319734987496853968237973 577487577538915029761155)
                ·
                  refine ⟨866231366308372544641733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 577487577538915029761155 866231366308372544641733)
                  ·
                    refine ⟨162418381182819852120325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 866231366308372544641733 162418381182819852120325)
                    ·
                      rfl

theorem cell23_948926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_948926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948926 prefixEnd_948926 := by exact prefixLift 948926
  have htrace : WordTrace (prefixWord ++ tailWord_948926) baseStart_948926 baseEnd_948926 := by
    simpa [prefixWord, tailWord_948926, baseEnd_948926] using wordTrace_append hprefix tailTrace_948926
  have hstable : (prefixWord ++ tailWord_948926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948926).length < 2 ^ (prefixWord ++ tailWord_948926).sum := by decide
  have hdescent : baseEnd_948926 < baseStart_948926 := by decide
  rcases family_descends (prefixWord ++ tailWord_948926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948935 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 2, 9]
def baseStart_948935 : Nat := 118140960795 + 948935 * 2 ^ 59
def prefixEnd_948935 : Nat := 4983230072969 + 3 ^ 40 * 948935 * 2
def baseEnd_948935 : Nat := 162419921624783340382811

theorem tailTrace_948935 : CollatzResearch.WordTrace tailWord_948935 prefixEnd_948935 162419921624783340382811 := by
  unfold tailWord_948935
  simp only [CollatzResearch.WordTrace]
  refine ⟨34610502817178035040440259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23073668544785356693626839 34610502817178035040440259)
  ·
    refine ⟨51915754225767052560660389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34610502817178035040440259 51915754225767052560660389)
    ·
      refine ⟨9734203917331322355123823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51915754225767052560660389 9734203917331322355123823)
      ·
        refine ⟨14601305875996983532685735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9734203917331322355123823 14601305875996983532685735)
        ·
          refine ⟨21901958813995475299028603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14601305875996983532685735 21901958813995475299028603)
          ·
            refine ⟨32852938220993212948542905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21901958813995475299028603 32852938220993212948542905)
            ·
              refine ⟨24639703665744909711407179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32852938220993212948542905 24639703665744909711407179)
              ·
                refine ⟨36959555498617364567110769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24639703665744909711407179 36959555498617364567110769)
                ·
                  refine ⟨27719666623963023425333077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36959555498617364567110769 27719666623963023425333077)
                  ·
                    refine ⟨162419921624783340382811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 27719666623963023425333077 162419921624783340382811)
                    ·
                      rfl

theorem cell23_948935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_948935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948935 prefixEnd_948935 := by exact prefixLift 948935
  have htrace : WordTrace (prefixWord ++ tailWord_948935) baseStart_948935 baseEnd_948935 := by
    simpa [prefixWord, tailWord_948935, baseEnd_948935] using wordTrace_append hprefix tailTrace_948935
  have hstable : (prefixWord ++ tailWord_948935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948935).length < 2 ^ (prefixWord ++ tailWord_948935).sum := by decide
  have hdescent : baseEnd_948935 < baseStart_948935 := by decide
  rcases family_descends (prefixWord ++ tailWord_948935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948959 : List Nat := [1, 1, 2, 3, 2, 3, 2, 1, 1, 5, 2]
def baseStart_948959 : Nat := 118140960795 + 948959 * 2 ^ 59
def prefixEnd_948959 : Nat := 4983230072969 + 3 ^ 40 * 948959 * 2
def baseEnd_948959 : Nat := 487272088410057927248323

theorem tailTrace_948959 : CollatzResearch.WordTrace tailWord_948959 prefixEnd_948959 487272088410057927248323 := by
  unfold tailWord_948959
  simp only [CollatzResearch.WordTrace]
  refine ⟨34611378169091087139313931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23074252112727391426209287 34611378169091087139313931)
  ·
    refine ⟨51917067253636630708970897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34611378169091087139313931 51917067253636630708970897)
    ·
      refine ⟨38937800440227473031728173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51917067253636630708970897 38937800440227473031728173)
      ·
        refine ⟨14601675165085302386898065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38937800440227473031728173 14601675165085302386898065)
        ·
          refine ⟨10951256373813976790173549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14601675165085302386898065 10951256373813976790173549)
          ·
            refine ⟨4106721140180241296315081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10951256373813976790173549 4106721140180241296315081)
            ·
              refine ⟨3080040855135180972236311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4106721140180241296315081 3080040855135180972236311)
              ·
                refine ⟨4620061282702771458354467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3080040855135180972236311 4620061282702771458354467)
                ·
                  refine ⟨6930091924054157187531701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4620061282702771458354467 6930091924054157187531701)
                  ·
                    refine ⟨649696117880077236331097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6930091924054157187531701 649696117880077236331097)
                    ·
                      refine ⟨487272088410057927248323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 649696117880077236331097 487272088410057927248323)
                      ·
                        rfl

theorem cell23_948959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 5, 2].length) (baseStart_948959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948959 prefixEnd_948959 := by exact prefixLift 948959
  have htrace : WordTrace (prefixWord ++ tailWord_948959) baseStart_948959 baseEnd_948959 := by
    simpa [prefixWord, tailWord_948959, baseEnd_948959] using wordTrace_append hprefix tailTrace_948959
  have hstable : (prefixWord ++ tailWord_948959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948959).length < 2 ^ (prefixWord ++ tailWord_948959).sum := by decide
  have hdescent : baseEnd_948959 < baseStart_948959 := by decide
  rcases family_descends (prefixWord ++ tailWord_948959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948972 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 4]
def baseStart_948972 : Nat := 118140960795 + 948972 * 2 ^ 59
def prefixEnd_948972 : Nat := 4983230072969 + 3 ^ 40 * 948972 * 2
def baseEnd_948972 : Nat := 487278763658566376385763

theorem tailTrace_948972 : CollatzResearch.WordTrace tailWord_948972 prefixEnd_948972 487278763658566376385763 := by
  unfold tailWord_948972
  simp only [CollatzResearch.WordTrace]
  refine ⟨17305926159021995179768585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23074568212029326906358113 17305926159021995179768585)
  ·
    refine ⟨12979444619266496384826439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17305926159021995179768585 12979444619266496384826439)
    ·
      refine ⟨19469166928899744577239659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12979444619266496384826439 19469166928899744577239659)
      ·
        refine ⟨29203750393349616865859489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19469166928899744577239659 29203750393349616865859489)
        ·
          refine ⟨21902812795012212649394617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29203750393349616865859489 21902812795012212649394617)
          ·
            refine ⟨16427109596259159487045963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21902812795012212649394617 16427109596259159487045963)
            ·
              refine ⟨24640664394388739230568945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16427109596259159487045963 24640664394388739230568945)
              ·
                refine ⟨18480498295791554422926709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24640664394388739230568945 18480498295791554422926709)
                ·
                  refine ⟨1732546715230458227149379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18480498295791554422926709 1732546715230458227149379)
                  ·
                    refine ⟨2598820072845687340724069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1732546715230458227149379 2598820072845687340724069)
                    ·
                      refine ⟨487278763658566376385763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2598820072845687340724069 487278763658566376385763)
                      ·
                        rfl

theorem cell23_948972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 4].length) (baseStart_948972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_948972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_948972 prefixEnd_948972 := by exact prefixLift 948972
  have htrace : WordTrace (prefixWord ++ tailWord_948972) baseStart_948972 baseEnd_948972 := by
    simpa [prefixWord, tailWord_948972, baseEnd_948972] using wordTrace_append hprefix tailTrace_948972
  have hstable : (prefixWord ++ tailWord_948972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948972).length < 2 ^ (prefixWord ++ tailWord_948972).sum := by decide
  have hdescent : baseEnd_948972 < baseStart_948972 := by decide
  rcases family_descends (prefixWord ++ tailWord_948972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949002 : List Nat := [3, 1, 2, 2, 1, 2, 1, 3, 1, 1, 6]
def baseStart_949002 : Nat := 118140960795 + 949002 * 2 ^ 59
def prefixEnd_949002 : Nat := 4983230072969 + 3 ^ 40 * 949002 * 2
def baseEnd_949002 : Nat := 487294168078201259010625

theorem tailTrace_949002 : CollatzResearch.WordTrace tailWord_949002 prefixEnd_949002 487294168078201259010625 := by
  unfold tailWord_949002
  simp only [CollatzResearch.WordTrace]
  refine ⟨8653236626983826370782315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23075297671956870322086173 8653236626983826370782315)
  ·
    refine ⟨12979854940475739556173473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8653236626983826370782315 12979854940475739556173473)
    ·
      refine ⟨9734891205356804667130105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12979854940475739556173473 9734891205356804667130105)
      ·
        refine ⟨7301168404017603500347579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9734891205356804667130105 7301168404017603500347579)
        ·
          refine ⟨10951752606026405250521369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7301168404017603500347579 10951752606026405250521369)
          ·
            refine ⟨8213814454519803937891027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10951752606026405250521369 8213814454519803937891027)
            ·
              refine ⟨12320721681779705906836541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8213814454519803937891027 12320721681779705906836541)
              ·
                refine ⟨4620270630667389715063703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12320721681779705906836541 4620270630667389715063703)
                ·
                  refine ⟨6930405946001084572595555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4620270630667389715063703 6930405946001084572595555)
                  ·
                    refine ⟨10395608919001626858893333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6930405946001084572595555 10395608919001626858893333)
                    ·
                      refine ⟨487294168078201259010625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10395608919001626858893333 487294168078201259010625)
                      ·
                        rfl

theorem cell23_949002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_949002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949002 prefixEnd_949002 := by exact prefixLift 949002
  have htrace : WordTrace (prefixWord ++ tailWord_949002) baseStart_949002 baseEnd_949002 := by
    simpa [prefixWord, tailWord_949002, baseEnd_949002] using wordTrace_append hprefix tailTrace_949002
  have hstable : (prefixWord ++ tailWord_949002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949002).length < 2 ^ (prefixWord ++ tailWord_949002).sum := by decide
  have hdescent : baseEnd_949002 < baseStart_949002 := by decide
  rcases family_descends (prefixWord ++ tailWord_949002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949006 : List Nat := [4, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2]
def baseStart_949006 : Nat := 118140960795 + 949006 * 2 ^ 59
def prefixEnd_949006 : Nat := 4983230072969 + 3 ^ 40 * 949006 * 2
def baseEnd_949006 : Nat := 487296222000819243360607

theorem tailTrace_949006 : CollatzResearch.WordTrace tailWord_949006 prefixEnd_949006 487296222000819243360607 := by
  unfold tailWord_949006
  simp only [CollatzResearch.WordTrace]
  refine ⟨4326636549990101770784359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23075394933280542777516581 4326636549990101770784359)
  ·
    refine ⟨6489954824985152656176539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4326636549990101770784359 6489954824985152656176539)
    ·
      refine ⟨9734932237477728984264809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6489954824985152656176539 9734932237477728984264809)
      ·
        refine ⟨7301199178108296738198607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9734932237477728984264809 7301199178108296738198607)
        ·
          refine ⟨10951798767162445107297911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7301199178108296738198607 10951798767162445107297911)
          ·
            refine ⟨16427698150743667660946867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10951798767162445107297911 16427698150743667660946867)
            ·
              refine ⟨24641547226115501491420301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16427698150743667660946867 24641547226115501491420301)
              ·
                refine ⟨9240580209793313059282613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24641547226115501491420301 9240580209793313059282613)
                ·
                  refine ⟨866304394668123099307745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9240580209793313059282613 866304394668123099307745)
                  ·
                    refine ⟨649728296001092324480809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 866304394668123099307745 649728296001092324480809)
                    ·
                      refine ⟨487296222000819243360607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 649728296001092324480809 487296222000819243360607)
                      ·
                        rfl

theorem cell23_949006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_949006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949006 prefixEnd_949006 := by exact prefixLift 949006
  have htrace : WordTrace (prefixWord ++ tailWord_949006) baseStart_949006 baseEnd_949006 := by
    simpa [prefixWord, tailWord_949006, baseEnd_949006] using wordTrace_append hprefix tailTrace_949006
  have hstable : (prefixWord ++ tailWord_949006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949006).length < 2 ^ (prefixWord ++ tailWord_949006).sum := by decide
  have hdescent : baseEnd_949006 < baseStart_949006 := by decide
  rcases family_descends (prefixWord ++ tailWord_949006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949010 : List Nat := [3, 2, 4, 1, 2, 1, 2, 1, 2, 3, 2]
def baseStart_949010 : Nat := 118140960795 + 949010 * 2 ^ 59
def prefixEnd_949010 : Nat := 4983230072969 + 3 ^ 40 * 949010 * 2
def baseEnd_949010 : Nat := 487298275923437227710589

theorem tailTrace_949010 : CollatzResearch.WordTrace tailWord_949010 prefixEnd_949010 487298275923437227710589 := by
  unfold tailWord_949010
  simp only [CollatzResearch.WordTrace]
  refine ⟨8653309572976580712355121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23075492194604215232946989 8653309572976580712355121)
  ·
    refine ⟨6489982179732435534266341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8653309572976580712355121 6489982179732435534266341)
    ·
      refine ⟨1216871658699831662674939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6489982179732435534266341 1216871658699831662674939)
      ·
        refine ⟨1825307488049747494012409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1216871658699831662674939 1825307488049747494012409)
        ·
          refine ⟨1368980616037310620509307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1825307488049747494012409 1368980616037310620509307)
          ·
            refine ⟨2053470924055965930763961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1368980616037310620509307 2053470924055965930763961)
            ·
              refine ⟨1540103193041974448072971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2053470924055965930763961 1540103193041974448072971)
              ·
                refine ⟨2310154789562961672109457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1540103193041974448072971 2310154789562961672109457)
                ·
                  refine ⟨1732616092172221254082093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2310154789562961672109457 1732616092172221254082093)
                  ·
                    refine ⟨649731034564582970280785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1732616092172221254082093 649731034564582970280785)
                    ·
                      refine ⟨487298275923437227710589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 649731034564582970280785 487298275923437227710589)
                      ·
                        rfl

theorem cell23_949010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_949010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949010 prefixEnd_949010 := by exact prefixLift 949010
  have htrace : WordTrace (prefixWord ++ tailWord_949010) baseStart_949010 baseEnd_949010 := by
    simpa [prefixWord, tailWord_949010, baseEnd_949010] using wordTrace_append hprefix tailTrace_949010
  have hstable : (prefixWord ++ tailWord_949010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949010).length < 2 ^ (prefixWord ++ tailWord_949010).sum := by decide
  have hdescent : baseEnd_949010 < baseStart_949010 := by decide
  rcases family_descends (prefixWord ++ tailWord_949010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949026 : List Nat := [3, 3, 1, 1, 2, 4, 1, 1, 1, 1, 5]
def baseStart_949026 : Nat := 118140960795 + 949026 * 2 ^ 59
def prefixEnd_949026 : Nat := 4983230072969 + 3 ^ 40 * 949026 * 2
def baseEnd_949026 : Nat := 487306491613909165110515

theorem tailTrace_949026 : CollatzResearch.WordTrace tailWord_949026 prefixEnd_949026 487306491613909165110515 := by
  unfold tailWord_949026
  simp only [CollatzResearch.WordTrace]
  refine ⟨8653455464962089395500733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23075881239898905054668621 8653455464962089395500733)
  ·
    refine ⟨3245045799360783523312775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8653455464962089395500733 3245045799360783523312775)
    ·
      refine ⟨4867568699041175284969163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3245045799360783523312775 4867568699041175284969163)
      ·
        refine ⟨7301353048561762927453745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4867568699041175284969163 7301353048561762927453745)
        ·
          refine ⟨5476014786421322195590309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7301353048561762927453745 5476014786421322195590309)
          ·
            refine ⟨1026752772453997911673183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5476014786421322195590309 1026752772453997911673183)
            ·
              refine ⟨1540129158680996867509775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1026752772453997911673183 1540129158680996867509775)
              ·
                refine ⟨2310193738021495301264663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1540129158680996867509775 2310193738021495301264663)
                ·
                  refine ⟨3465290607032242951896995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2310193738021495301264663 3465290607032242951896995)
                  ·
                    refine ⟨5197935910548364427845493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3465290607032242951896995 5197935910548364427845493)
                    ·
                      refine ⟨487306491613909165110515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5197935910548364427845493 487306491613909165110515)
                      ·
                        rfl

theorem cell23_949026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_949026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949026 prefixEnd_949026 := by exact prefixLift 949026
  have htrace : WordTrace (prefixWord ++ tailWord_949026) baseStart_949026 baseEnd_949026 := by
    simpa [prefixWord, tailWord_949026, baseEnd_949026] using wordTrace_append hprefix tailTrace_949026
  have hstable : (prefixWord ++ tailWord_949026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949026).length < 2 ^ (prefixWord ++ tailWord_949026).sum := by decide
  have hdescent : baseEnd_949026 < baseStart_949026 := by decide
  rcases family_descends (prefixWord ++ tailWord_949026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949034 : List Nat := [3, 1, 4, 3, 1, 2, 2, 2, 1, 1, 3]
def baseStart_949034 : Nat := 118140960795 + 949034 * 2 ^ 59
def prefixEnd_949034 : Nat := 4983230072969 + 3 ^ 40 * 949034 * 2
def baseEnd_949034 : Nat := 487310599459145133810479

theorem tailTrace_949034 : CollatzResearch.WordTrace tailWord_949034 prefixEnd_949034 487310599459145133810479 := by
  unfold tailWord_949034
  simp only [CollatzResearch.WordTrace]
  refine ⟨8653528410954843737073539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23076075762546249965529437 8653528410954843737073539)
  ·
    refine ⟨12980292616432265605610309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8653528410954843737073539 12980292616432265605610309)
    ·
      refine ⟨2433804865581049801051933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12980292616432265605610309 2433804865581049801051933)
      ·
        refine ⟨912676824592893675394475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2433804865581049801051933 912676824592893675394475)
        ·
          refine ⟨1369015236889340513091713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 912676824592893675394475 1369015236889340513091713)
          ·
            refine ⟨1026761427667005384818785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1369015236889340513091713 1026761427667005384818785)
            ·
              refine ⟨770071070750254038614089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1026761427667005384818785 770071070750254038614089)
              ·
                refine ⟨577553303062690528960567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 770071070750254038614089 577553303062690528960567)
                ·
                  refine ⟨866329954594035793440851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 577553303062690528960567 866329954594035793440851)
                  ·
                    refine ⟨1299494931891053690161277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 866329954594035793440851 1299494931891053690161277)
                    ·
                      refine ⟨487310599459145133810479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1299494931891053690161277 487310599459145133810479)
                      ·
                        rfl

theorem cell23_949034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_949034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949034 prefixEnd_949034 := by exact prefixLift 949034
  have htrace : WordTrace (prefixWord ++ tailWord_949034) baseStart_949034 baseEnd_949034 := by
    simpa [prefixWord, tailWord_949034, baseEnd_949034] using wordTrace_append hprefix tailTrace_949034
  have hstable : (prefixWord ++ tailWord_949034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949034).length < 2 ^ (prefixWord ++ tailWord_949034).sum := by decide
  have hdescent : baseEnd_949034 < baseStart_949034 := by decide
  rcases family_descends (prefixWord ++ tailWord_949034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949042 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 1, 9]
def baseStart_949042 : Nat := 118140960795 + 949042 * 2 ^ 59
def prefixEnd_949042 : Nat := 4983230072969 + 3 ^ 40 * 949042 * 2
def baseEnd_949042 : Nat := 162438235768127034170147

theorem tailTrace_949042 : CollatzResearch.WordTrace tailWord_949042 prefixEnd_949042 162438235768127034170147 := by
  unfold tailWord_949042
  simp only [CollatzResearch.WordTrace]
  refine ⟨8653601356947598078646345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23076270285193594876390253 8653601356947598078646345)
  ·
    refine ⟨6490201017710698558984759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8653601356947598078646345 6490201017710698558984759)
    ·
      refine ⟨9735301526566047838477139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6490201017710698558984759 9735301526566047838477139)
      ·
        refine ⟨14602952289849071757715709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9735301526566047838477139 14602952289849071757715709)
        ·
          refine ⟨5476107108693401909143391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14602952289849071757715709 5476107108693401909143391)
          ·
            refine ⟨8214160663040102863715087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5476107108693401909143391 8214160663040102863715087)
            ·
              refine ⟨12321240994560154295572631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8214160663040102863715087 12321240994560154295572631)
              ·
                refine ⟨18481861491840231443358947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12321240994560154295572631 18481861491840231443358947)
                ·
                  refine ⟨27722792237760347165038421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18481861491840231443358947 27722792237760347165038421)
                  ·
                    refine ⟨162438235768127034170147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 27722792237760347165038421 162438235768127034170147)
                    ·
                      rfl

theorem cell23_949042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_949042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949042 prefixEnd_949042 := by exact prefixLift 949042
  have htrace : WordTrace (prefixWord ++ tailWord_949042) baseStart_949042 baseEnd_949042 := by
    simpa [prefixWord, tailWord_949042, baseEnd_949042] using wordTrace_append hprefix tailTrace_949042
  have hstable : (prefixWord ++ tailWord_949042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949042).length < 2 ^ (prefixWord ++ tailWord_949042).sum := by decide
  have hdescent : baseEnd_949042 < baseStart_949042 := by decide
  rcases family_descends (prefixWord ++ tailWord_949042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949052 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 1, 4, 5]
def baseStart_949052 : Nat := 118140960795 + 949052 * 2 ^ 59
def prefixEnd_949052 : Nat := 4983230072969 + 3 ^ 40 * 949052 * 2
def baseEnd_949052 : Nat := 487319842110926063385395

theorem tailTrace_949052 : CollatzResearch.WordTrace tailWord_949052 prefixEnd_949052 487319842110926063385395 := by
  unfold tailWord_949052
  simp only [CollatzResearch.WordTrace]
  refine ⟨17307385078877082011224705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23076513438502776014966273 17307385078877082011224705)
  ·
    refine ⟨12980538809157811508418529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17307385078877082011224705 12980538809157811508418529)
    ·
      refine ⟨9735404106868358631313897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12980538809157811508418529 9735404106868358631313897)
      ·
        refine ⟨7301553080151268973485423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9735404106868358631313897 7301553080151268973485423)
        ·
          refine ⟨10952329620226903460228135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7301553080151268973485423 10952329620226903460228135)
          ·
            refine ⟨16428494430340355190342203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10952329620226903460228135 16428494430340355190342203)
            ·
              refine ⟨24642741645510532785513305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16428494430340355190342203 24642741645510532785513305)
              ·
                refine ⟨18482056234132899589134979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24642741645510532785513305 18482056234132899589134979)
                ·
                  refine ⟨27723084351199349383702469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18482056234132899589134979 27723084351199349383702469)
                  ·
                    refine ⟨5198078315849878009444213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27723084351199349383702469 5198078315849878009444213)
                    ·
                      refine ⟨487319842110926063385395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5198078315849878009444213 487319842110926063385395)
                      ·
                        rfl

theorem cell23_949052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_949052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949052 prefixEnd_949052 := by exact prefixLift 949052
  have htrace : WordTrace (prefixWord ++ tailWord_949052) baseStart_949052 baseEnd_949052 := by
    simpa [prefixWord, tailWord_949052, baseEnd_949052] using wordTrace_append hprefix tailTrace_949052
  have hstable : (prefixWord ++ tailWord_949052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949052).length < 2 ^ (prefixWord ++ tailWord_949052).sum := by decide
  have hdescent : baseEnd_949052 < baseStart_949052 := by decide
  rcases family_descends (prefixWord ++ tailWord_949052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949113 : List Nat := [1, 2, 1, 3, 2, 5, 1, 1, 1, 4, 2]
def baseStart_949113 : Nat := 118140960795 + 949113 * 2 ^ 59
def prefixEnd_949113 : Nat := 4983230072969 + 3 ^ 40 * 949113 * 2
def baseEnd_949113 : Nat := 487351164430850324722615

theorem tailTrace_949113 : CollatzResearch.WordTrace tailWord_949113 prefixEnd_949113 487351164430850324722615 := by
  unfold tailWord_949113
  simp only [CollatzResearch.WordTrace]
  refine ⟨34616995010533171440419993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23077996673688780960279995 34616995010533171440419993)
  ·
    refine ⟨25962746257899878580314995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34616995010533171440419993 25962746257899878580314995)
    ·
      refine ⟨38944119386849817870472493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25962746257899878580314995 38944119386849817870472493)
      ·
        refine ⟨14604044770068681701427185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38944119386849817870472493 14604044770068681701427185)
        ·
          refine ⟨10953033577551511276070389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14604044770068681701427185 10953033577551511276070389)
          ·
            refine ⟨1026846897895454182131599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10953033577551511276070389 1026846897895454182131599)
            ·
              refine ⟨1540270346843181273197399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1026846897895454182131599 1540270346843181273197399)
              ·
                refine ⟨2310405520264771909796099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1540270346843181273197399 2310405520264771909796099)
                ·
                  refine ⟨3465608280397157864694149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2310405520264771909796099 3465608280397157864694149)
                  ·
                    refine ⟨649801552574467099630153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3465608280397157864694149 649801552574467099630153)
                    ·
                      refine ⟨487351164430850324722615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 649801552574467099630153 487351164430850324722615)
                      ·
                        rfl

theorem cell23_949113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 4, 2].length) (baseStart_949113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949113 prefixEnd_949113 := by exact prefixLift 949113
  have htrace : WordTrace (prefixWord ++ tailWord_949113) baseStart_949113 baseEnd_949113 := by
    simpa [prefixWord, tailWord_949113, baseEnd_949113] using wordTrace_append hprefix tailTrace_949113
  have hstable : (prefixWord ++ tailWord_949113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949113).length < 2 ^ (prefixWord ++ tailWord_949113).sum := by decide
  have hdescent : baseEnd_949113 < baseStart_949113 := by decide
  rcases family_descends (prefixWord ++ tailWord_949113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949156 : List Nat := [2, 3, 1, 2, 1, 2, 2, 1, 2, 5, 2]
def baseStart_949156 : Nat := 118140960795 + 949156 * 2 ^ 59
def prefixEnd_949156 : Nat := 4983230072969 + 3 ^ 40 * 949156 * 2
def baseEnd_949156 : Nat := 487373244098993656484917

theorem tailTrace_949156 : CollatzResearch.WordTrace tailWord_949156 prefixEnd_949156 487373244098993656484917 := by
  unfold tailWord_949156
  simp only [CollatzResearch.WordTrace]
  refine ⟨17309281674688694892117661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23079042232918259856156881 17309281674688694892117661)
  ·
    refine ⟨6490980628008260584544123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17309281674688694892117661 6490980628008260584544123)
    ·
      refine ⟨9736470942012390876816185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6490980628008260584544123 9736470942012390876816185)
      ·
        refine ⟨7302353206509293157612139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9736470942012390876816185 7302353206509293157612139)
        ·
          refine ⟨10953529809763939736418209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7302353206509293157612139 10953529809763939736418209)
          ·
            refine ⟨8215147357322954802313657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10953529809763939736418209 8215147357322954802313657)
            ·
              refine ⟨6161360517992216101735243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8215147357322954802313657 6161360517992216101735243)
              ·
                refine ⟨9242040776988324152602865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6161360517992216101735243 9242040776988324152602865)
                ·
                  refine ⟨6931530582741243114452149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9242040776988324152602865 6931530582741243114452149)
                  ·
                    refine ⟨649830992131991541979889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6931530582741243114452149 649830992131991541979889)
                    ·
                      refine ⟨487373244098993656484917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 649830992131991541979889 487373244098993656484917)
                      ·
                        rfl

theorem cell23_949156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_949156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949156 prefixEnd_949156 := by exact prefixLift 949156
  have htrace : WordTrace (prefixWord ++ tailWord_949156) baseStart_949156 baseEnd_949156 := by
    simpa [prefixWord, tailWord_949156, baseEnd_949156] using wordTrace_append hprefix tailTrace_949156
  have hstable : (prefixWord ++ tailWord_949156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949156).length < 2 ^ (prefixWord ++ tailWord_949156).sum := by decide
  have hdescent : baseEnd_949156 < baseStart_949156 := by decide
  rcases family_descends (prefixWord ++ tailWord_949156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949189 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 5, 4, 3]
def baseStart_949189 : Nat := 118140960795 + 949189 * 2 ^ 59
def prefixEnd_949189 : Nat := 4983230072969 + 3 ^ 40 * 949189 * 2
def baseEnd_949189 : Nat := 487390188960592027372265

theorem tailTrace_949189 : CollatzResearch.WordTrace tailWord_949189 prefixEnd_949189 487390188960592027372265 := by
  unfold tailWord_949189
  simp only [CollatzResearch.WordTrace]
  refine ⟨34619766958257836420186621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23079844638838557613457747 34619766958257836420186621)
  ·
    refine ⟨12982412609346688657569983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34619766958257836420186621 12982412609346688657569983)
    ·
      refine ⟨19473618914020032986354975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12982412609346688657569983 19473618914020032986354975)
      ·
        refine ⟨29210428371030049479532463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19473618914020032986354975 29210428371030049479532463)
        ·
          refine ⟨43815642556545074219298695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29210428371030049479532463 43815642556545074219298695)
          ·
            refine ⟨65723463834817611328948043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43815642556545074219298695 65723463834817611328948043)
            ·
              refine ⟨98585195752226416993422065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65723463834817611328948043 98585195752226416993422065)
              ·
                refine ⟨73938896814169812745066549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98585195752226416993422065 73938896814169812745066549)
                ·
                  refine ⟨6931771576328419944849989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73938896814169812745066549 6931771576328419944849989)
                  ·
                    refine ⟨1299707170561578739659373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6931771576328419944849989 1299707170561578739659373)
                    ·
                      refine ⟨487390188960592027372265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1299707170561578739659373 487390188960592027372265)
                      ·
                        rfl

theorem cell23_949189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 4, 3].length) (baseStart_949189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949189 prefixEnd_949189 := by exact prefixLift 949189
  have htrace : WordTrace (prefixWord ++ tailWord_949189) baseStart_949189 baseEnd_949189 := by
    simpa [prefixWord, tailWord_949189, baseEnd_949189] using wordTrace_append hprefix tailTrace_949189
  have hstable : (prefixWord ++ tailWord_949189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949189).length < 2 ^ (prefixWord ++ tailWord_949189).sum := by decide
  have hdescent : baseEnd_949189 < baseStart_949189 := by decide
  rcases family_descends (prefixWord ++ tailWord_949189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949226 : List Nat := [3, 1, 3, 1, 2, 2, 2, 3, 6]
def baseStart_949226 : Nat := 118140960795 + 949226 * 2 ^ 59
def prefixEnd_949226 : Nat := 4983230072969 + 3 ^ 40 * 949226 * 2
def baseEnd_949226 : Nat := 54156576416089820289955

theorem tailTrace_949226 : CollatzResearch.WordTrace tailWord_949226 prefixEnd_949226 54156576416089820289955 := by
  unfold tailWord_949226
  simp only [CollatzResearch.WordTrace]
  refine ⟨8655279114780947934820883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23080744306082527826189021 8655279114780947934820883)
  ·
    refine ⟨12982918672171421902231325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8655279114780947934820883 12982918672171421902231325)
    ·
      refine ⟨4868594502064283213336747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12982918672171421902231325 4868594502064283213336747)
      ·
        refine ⟨7302891753096424820005121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4868594502064283213336747 7302891753096424820005121)
        ·
          refine ⟨5477168814822318615003841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7302891753096424820005121 5477168814822318615003841)
          ·
            refine ⟨4107876611116738961252881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5477168814822318615003841 4107876611116738961252881)
            ·
              refine ⟨3080907458337554220939661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4107876611116738961252881 3080907458337554220939661)
              ·
                refine ⟨1155340296876582832852373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3080907458337554220939661 1155340296876582832852373)
                ·
                  refine ⟨54156576416089820289955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1155340296876582832852373 54156576416089820289955)
                  ·
                    rfl

theorem cell23_949226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 6].length) (baseStart_949226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949226 prefixEnd_949226 := by exact prefixLift 949226
  have htrace : WordTrace (prefixWord ++ tailWord_949226) baseStart_949226 baseEnd_949226 := by
    simpa [prefixWord, tailWord_949226, baseEnd_949226] using wordTrace_append hprefix tailTrace_949226
  have hstable : (prefixWord ++ tailWord_949226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949226).length < 2 ^ (prefixWord ++ tailWord_949226).sum := by decide
  have hdescent : baseEnd_949226 < baseStart_949226 := by decide
  rcases family_descends (prefixWord ++ tailWord_949226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949237 : List Nat := [1, 3, 5, 2, 1, 2, 1, 1, 2, 1, 4]
def baseStart_949237 : Nat := 118140960795 + 949237 * 2 ^ 59
def prefixEnd_949237 : Nat := 4983230072969 + 3 ^ 40 * 949237 * 2
def baseEnd_949237 : Nat := 487414836032007839572045

theorem tailTrace_949237 : CollatzResearch.WordTrace tailWord_949237 prefixEnd_949237 487414836032007839572045 := by
  unfold tailWord_949237
  simp only [CollatzResearch.WordTrace]
  refine ⟨34621517662083940617933965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23081011774722627078622643 34621517662083940617933965)
  ·
    refine ⟨12983069123281477731725237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34621517662083940617933965 12983069123281477731725237)
    ·
      refine ⟨1217162730307638537349241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12983069123281477731725237 1217162730307638537349241)
      ·
        refine ⟨912872047730728903011931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1217162730307638537349241 912872047730728903011931)
        ·
          refine ⟨1369308071596093354517897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 912872047730728903011931 1369308071596093354517897)
          ·
            refine ⟨1026981053697070015888423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1369308071596093354517897 1026981053697070015888423)
            ·
              refine ⟨1540471580545605023832635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1026981053697070015888423 1540471580545605023832635)
              ·
                refine ⟨2310707370818407535748953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1540471580545605023832635 2310707370818407535748953)
                ·
                  refine ⟨1733030528113805651811715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2310707370818407535748953 1733030528113805651811715)
                  ·
                    refine ⟨2599545792170708477717573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1733030528113805651811715 2599545792170708477717573)
                    ·
                      refine ⟨487414836032007839572045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2599545792170708477717573 487414836032007839572045)
                      ·
                        rfl

theorem cell23_949237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_949237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949237 prefixEnd_949237 := by exact prefixLift 949237
  have htrace : WordTrace (prefixWord ++ tailWord_949237) baseStart_949237 baseEnd_949237 := by
    simpa [prefixWord, tailWord_949237, baseEnd_949237] using wordTrace_append hprefix tailTrace_949237
  have hstable : (prefixWord ++ tailWord_949237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949237).length < 2 ^ (prefixWord ++ tailWord_949237).sum := by decide
  have hdescent : baseEnd_949237 < baseStart_949237 := by decide
  rcases family_descends (prefixWord ++ tailWord_949237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949290 : List Nat := [3, 1, 4, 1, 3, 1, 2, 2, 1, 5]
def baseStart_949290 : Nat := 118140960795 + 949290 * 2 ^ 59
def prefixEnd_949290 : Nat := 4983230072969 + 3 ^ 40 * 949290 * 2
def baseEnd_949290 : Nat := 162480683502232044069767

theorem tailTrace_949290 : CollatzResearch.WordTrace tailWord_949290 prefixEnd_949290 162480683502232044069767 := by
  unfold tailWord_949290
  simp only [CollatzResearch.WordTrace]
  refine ⟨8655862682722982667403331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23082300487261287113075549 8655862682722982667403331)
  ·
    refine ⟨12983794024084474001104997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8655862682722982667403331 12983794024084474001104997)
    ·
      refine ⟨2434461379515838875207187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12983794024084474001104997 2434461379515838875207187)
      ·
        refine ⟨3651692069273758312810781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2434461379515838875207187 3651692069273758312810781)
        ·
          refine ⟨1369384525977659367304043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3651692069273758312810781 1369384525977659367304043)
          ·
            refine ⟨2054076788966489050956065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1369384525977659367304043 2054076788966489050956065)
            ·
              refine ⟨1540557591724866788217049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2054076788966489050956065 1540557591724866788217049)
              ·
                refine ⟨1155418193793650091162787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1540557591724866788217049 1155418193793650091162787)
                ·
                  refine ⟨1733127290690475136744181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1155418193793650091162787 1733127290690475136744181)
                  ·
                    refine ⟨162480683502232044069767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1733127290690475136744181 162480683502232044069767)
                    ·
                      rfl

theorem cell23_949290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_949290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949290 prefixEnd_949290 := by exact prefixLift 949290
  have htrace : WordTrace (prefixWord ++ tailWord_949290) baseStart_949290 baseEnd_949290 := by
    simpa [prefixWord, tailWord_949290, baseEnd_949290] using wordTrace_append hprefix tailTrace_949290
  have hstable : (prefixWord ++ tailWord_949290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949290).length < 2 ^ (prefixWord ++ tailWord_949290).sum := by decide
  have hdescent : baseEnd_949290 < baseStart_949290 := by decide
  rcases family_descends (prefixWord ++ tailWord_949290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949306 : List Nat := [3, 1, 1, 1, 3, 1, 2, 4, 1, 2, 4]
def baseStart_949306 : Nat := 118140960795 + 949306 * 2 ^ 59
def prefixEnd_949306 : Nat := 4983230072969 + 3 ^ 40 * 949306 * 2
def baseEnd_949306 : Nat := 487450266197168069609227

theorem tailTrace_949306 : CollatzResearch.WordTrace tailWord_949306 prefixEnd_949306 487450266197168069609227 := by
  unfold tailWord_949306
  simp only [CollatzResearch.WordTrace]
  refine ⟨8656008574708491350548943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23082689532555976934797181 8656008574708491350548943)
  ·
    refine ⟨12984012862062737025823415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8656008574708491350548943 12984012862062737025823415)
    ·
      refine ⟨19476019293094105538735123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12984012862062737025823415 19476019293094105538735123)
      ·
        refine ⟨29214028939641158308102685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19476019293094105538735123 29214028939641158308102685)
        ·
          refine ⟨10955260852365434365538507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29214028939641158308102685 10955260852365434365538507)
          ·
            refine ⟨16432891278548151548307761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10955260852365434365538507 16432891278548151548307761)
            ·
              refine ⟨12324668458911113661230821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16432891278548151548307761 12324668458911113661230821)
              ·
                refine ⟨2310875336045833811480779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12324668458911113661230821 2310875336045833811480779)
                ·
                  refine ⟨3466313004068750717221169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2310875336045833811480779 3466313004068750717221169)
                  ·
                    refine ⟨2599734753051563037915877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3466313004068750717221169 2599734753051563037915877)
                    ·
                      refine ⟨487450266197168069609227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2599734753051563037915877 487450266197168069609227)
                      ·
                        rfl

theorem cell23_949306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 1, 2, 4].length) (baseStart_949306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949306 prefixEnd_949306 := by exact prefixLift 949306
  have htrace : WordTrace (prefixWord ++ tailWord_949306) baseStart_949306 baseEnd_949306 := by
    simpa [prefixWord, tailWord_949306, baseEnd_949306] using wordTrace_append hprefix tailTrace_949306
  have hstable : (prefixWord ++ tailWord_949306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949306).length < 2 ^ (prefixWord ++ tailWord_949306).sum := by decide
  have hdescent : baseEnd_949306 < baseStart_949306 := by decide
  rcases family_descends (prefixWord ++ tailWord_949306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949310 : List Nat := [4, 2, 1, 3, 1, 1, 2, 3, 1, 1, 4]
def baseStart_949310 : Nat := 118140960795 + 949310 * 2 ^ 59
def prefixEnd_949310 : Nat := 4983230072969 + 3 ^ 40 * 949310 * 2
def baseEnd_949310 : Nat := 487452320119786053959209

theorem tailTrace_949310 : CollatzResearch.WordTrace tailWord_949310 prefixEnd_949310 487452320119786053959209 := by
  unfold tailWord_949310
  simp only [CollatzResearch.WordTrace]
  refine ⟨4328022523852434260667673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23082786793879649390227589 4328022523852434260667673)
  ·
    refine ⟨3246016892889325695500755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4328022523852434260667673 3246016892889325695500755)
    ·
      refine ⟨4869025339333988543251133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3246016892889325695500755 4869025339333988543251133)
      ·
        refine ⟨1825884502250245703719175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4869025339333988543251133 1825884502250245703719175)
        ·
          refine ⟨2738826753375368555578763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1825884502250245703719175 2738826753375368555578763)
          ·
            refine ⟨4108240130063052833368145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2738826753375368555578763 4108240130063052833368145)
            ·
              refine ⟨3081180097547289625026109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4108240130063052833368145 3081180097547289625026109)
              ·
                refine ⟨1155442536580233609384791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3081180097547289625026109 1155442536580233609384791)
                ·
                  refine ⟨1733163804870350414077187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1155442536580233609384791 1733163804870350414077187)
                  ·
                    refine ⟨2599745707305525621115781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1733163804870350414077187 2599745707305525621115781)
                    ·
                      refine ⟨487452320119786053959209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2599745707305525621115781 487452320119786053959209)
                      ·
                        rfl

theorem cell23_949310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_949310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949310 prefixEnd_949310 := by exact prefixLift 949310
  have htrace : WordTrace (prefixWord ++ tailWord_949310) baseStart_949310 baseEnd_949310 := by
    simpa [prefixWord, tailWord_949310, baseEnd_949310] using wordTrace_append hprefix tailTrace_949310
  have hstable : (prefixWord ++ tailWord_949310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949310).length < 2 ^ (prefixWord ++ tailWord_949310).sum := by decide
  have hdescent : baseEnd_949310 < baseStart_949310 := by decide
  rcases family_descends (prefixWord ++ tailWord_949310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949377 : List Nat := [1, 2, 4, 2, 2, 2, 2, 2, 2, 1, 3]
def baseStart_949377 : Nat := 118140960795 + 949377 * 2 ^ 59
def prefixEnd_949377 : Nat := 4983230072969 + 3 ^ 40 * 949377 * 2
def baseEnd_949377 : Nat := 487486723323637291821401

theorem tailTrace_949377 : CollatzResearch.WordTrace tailWord_949377 prefixEnd_949377 487486723323637291821401 := by
  unfold tailWord_949377
  simp only [CollatzResearch.WordTrace]
  refine ⟨34626623881576744528030385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23084415921051163018686923 34626623881576744528030385)
  ·
    refine ⟨25969967911182558396022789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34626623881576744528030385 25969967911182558396022789)
    ·
      refine ⟨4869368983346729699254273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25969967911182558396022789 4869368983346729699254273)
      ·
        refine ⟨3652026737510047274440705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4869368983346729699254273 3652026737510047274440705)
        ·
          refine ⟨2739020053132535455830529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3652026737510047274440705 2739020053132535455830529)
          ·
            refine ⟨2054265039849401591872897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2739020053132535455830529 2054265039849401591872897)
            ·
              refine ⟨1540698779887051193904673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2054265039849401591872897 1540698779887051193904673)
              ·
                refine ⟨1155524084915288395428505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1540698779887051193904673 1155524084915288395428505)
                ·
                  refine ⟨866643063686466296571379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1155524084915288395428505 866643063686466296571379)
                  ·
                    refine ⟨1299964595529699444857069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 866643063686466296571379 1299964595529699444857069)
                    ·
                      refine ⟨487486723323637291821401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1299964595529699444857069 487486723323637291821401)
                      ·
                        rfl

theorem cell23_949377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_949377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949377 prefixEnd_949377 := by exact prefixLift 949377
  have htrace : WordTrace (prefixWord ++ tailWord_949377) baseStart_949377 baseEnd_949377 := by
    simpa [prefixWord, tailWord_949377, baseEnd_949377] using wordTrace_append hprefix tailTrace_949377
  have hstable : (prefixWord ++ tailWord_949377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949377).length < 2 ^ (prefixWord ++ tailWord_949377).sum := by decide
  have hdescent : baseEnd_949377 < baseStart_949377 := by decide
  rcases family_descends (prefixWord ++ tailWord_949377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949383 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 5, 4, 2]
def baseStart_949383 : Nat := 118140960795 + 949383 * 2 ^ 59
def prefixEnd_949383 : Nat := 4983230072969 + 3 ^ 40 * 949383 * 2
def baseEnd_949383 : Nat := 487489804207564268346373

theorem tailTrace_949383 : CollatzResearch.WordTrace tailWord_949383 prefixEnd_949383 487489804207564268346373 := by
  unfold tailWord_949383
  simp only [CollatzResearch.WordTrace]
  refine ⟨34626842719555007552748803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23084561813036671701832535 34626842719555007552748803)
  ·
    refine ⟨51940264079332511329123205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34626842719555007552748803 51940264079332511329123205)
    ·
      refine ⟨9738799514874845874210601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51940264079332511329123205 9738799514874845874210601)
      ·
        refine ⟨7304099636156134405657951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9738799514874845874210601 7304099636156134405657951)
        ·
          refine ⟨10956149454234201608486927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7304099636156134405657951 10956149454234201608486927)
          ·
            refine ⟨16434224181351302412730391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10956149454234201608486927 16434224181351302412730391)
            ·
              refine ⟨24651336272026953619095587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16434224181351302412730391 24651336272026953619095587)
              ·
                refine ⟨36977004408040430428643381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24651336272026953619095587 36977004408040430428643381)
                ·
                  refine ⟨3466594163253790352685317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36977004408040430428643381 3466594163253790352685317)
                  ·
                    refine ⟨649986405610085691128497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3466594163253790352685317 649986405610085691128497)
                    ·
                      refine ⟨487489804207564268346373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 649986405610085691128497 487489804207564268346373)
                      ·
                        rfl

theorem cell23_949383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_949383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949383 prefixEnd_949383 := by exact prefixLift 949383
  have htrace : WordTrace (prefixWord ++ tailWord_949383) baseStart_949383 baseEnd_949383 := by
    simpa [prefixWord, tailWord_949383, baseEnd_949383] using wordTrace_append hprefix tailTrace_949383
  have hstable : (prefixWord ++ tailWord_949383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949383).length < 2 ^ (prefixWord ++ tailWord_949383).sum := by decide
  have hdescent : baseEnd_949383 < baseStart_949383 := by decide
  rcases family_descends (prefixWord ++ tailWord_949383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949400 : List Nat := [2, 1, 2, 4, 2, 1, 1, 3, 1, 4, 2]
def baseStart_949400 : Nat := 118140960795 + 949400 * 2 ^ 59
def prefixEnd_949400 : Nat := 4983230072969 + 3 ^ 40 * 949400 * 2
def baseEnd_949400 : Nat := 487498533378690701833795

theorem tailTrace_949400 : CollatzResearch.WordTrace tailWord_949400 prefixEnd_949400 487498533378690701833795 := by
  unfold tailWord_949400
  simp only [CollatzResearch.WordTrace]
  refine ⟨17313731380246709728058827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23084975173662279637411769 17313731380246709728058827)
  ·
    refine ⟨25970597070370064592088241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17313731380246709728058827 25970597070370064592088241)
    ·
      refine ⟨19477947802777548444066181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25970597070370064592088241 19477947802777548444066181)
      ·
        refine ⟨3652115213020790333262409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19477947802777548444066181 3652115213020790333262409)
        ·
          refine ⟨2739086409765592749946807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3652115213020790333262409 2739086409765592749946807)
          ·
            refine ⟨4108629614648389124920211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2739086409765592749946807 4108629614648389124920211)
            ·
              refine ⟨6162944421972583687380317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4108629614648389124920211 6162944421972583687380317)
              ·
                refine ⟨2311104158239718882767619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6162944421972583687380317 2311104158239718882767619)
                ·
                  refine ⟨3466656237359578324151429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2311104158239718882767619 3466656237359578324151429)
                  ·
                    refine ⟨649998044504920935778393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3466656237359578324151429 649998044504920935778393)
                    ·
                      refine ⟨487498533378690701833795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 649998044504920935778393 487498533378690701833795)
                      ·
                        rfl

theorem cell23_949400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_949400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949400 prefixEnd_949400 := by exact prefixLift 949400
  have htrace : WordTrace (prefixWord ++ tailWord_949400) baseStart_949400 baseEnd_949400 := by
    simpa [prefixWord, tailWord_949400, baseEnd_949400] using wordTrace_append hprefix tailTrace_949400
  have hstable : (prefixWord ++ tailWord_949400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949400).length < 2 ^ (prefixWord ++ tailWord_949400).sum := by decide
  have hdescent : baseEnd_949400 < baseStart_949400 := by decide
  rcases family_descends (prefixWord ++ tailWord_949400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949421 : List Nat := [1, 5, 2, 1, 3, 2, 2, 1, 1, 3, 2]
def baseStart_949421 : Nat := 118140960795 + 949421 * 2 ^ 59
def prefixEnd_949421 : Nat := 4983230072969 + 3 ^ 40 * 949421 * 2
def baseEnd_949421 : Nat := 487509316472435119671199

theorem tailTrace_949421 : CollatzResearch.WordTrace tailWord_949421 prefixEnd_949421 487509316472435119671199 := by
  unfold tailWord_949421
  simp only [CollatzResearch.WordTrace]
  refine ⟨34628228693417340042632117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23085485795611560028421411 34628228693417340042632117)
  ·
    refine ⟨3246396440007875628996761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34628228693417340042632117 3246396440007875628996761)
    ·
      refine ⟨2434797330005906721747571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3246396440007875628996761 2434797330005906721747571)
      ·
        refine ⟨3652195995008860082621357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2434797330005906721747571 3652195995008860082621357)
        ·
          refine ⟨1369573498128322530983009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3652195995008860082621357 1369573498128322530983009)
          ·
            refine ⟨1027180123596241898237257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1369573498128322530983009 1027180123596241898237257)
            ·
              refine ⟨770385092697181423677943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1027180123596241898237257 770385092697181423677943)
              ·
                refine ⟨1155577639045772135516915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 770385092697181423677943 1155577639045772135516915)
                ·
                  refine ⟨1733366458568658203275373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1155577639045772135516915 1733366458568658203275373)
                  ·
                    refine ⟨650012421963246826228265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1733366458568658203275373 650012421963246826228265)
                    ·
                      refine ⟨487509316472435119671199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 650012421963246826228265 487509316472435119671199)
                      ·
                        rfl

theorem cell23_949421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_949421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949421 prefixEnd_949421 := by exact prefixLift 949421
  have htrace : WordTrace (prefixWord ++ tailWord_949421) baseStart_949421 baseEnd_949421 := by
    simpa [prefixWord, tailWord_949421, baseEnd_949421] using wordTrace_append hprefix tailTrace_949421
  have hstable : (prefixWord ++ tailWord_949421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949421).length < 2 ^ (prefixWord ++ tailWord_949421).sum := by decide
  have hdescent : baseEnd_949421 < baseStart_949421 := by decide
  rcases family_descends (prefixWord ++ tailWord_949421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949423 : List Nat := [1, 1, 2, 1, 2, 3, 3, 5, 5]
def baseStart_949423 : Nat := 118140960795 + 949423 * 2 ^ 59
def prefixEnd_949423 : Nat := 4983230072969 + 3 ^ 40 * 949423 * 2
def baseEnd_949423 : Nat := 54167815937082679094021

theorem tailTrace_949423 : CollatzResearch.WordTrace tailWord_949423 prefixEnd_949423 54167815937082679094021 := by
  unfold tailWord_949423
  simp only [CollatzResearch.WordTrace]
  refine ⟨34628301639410094384204923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23085534426273396256136615 34628301639410094384204923)
  ·
    refine ⟨51942452459115141576307385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34628301639410094384204923 51942452459115141576307385)
    ·
      refine ⟨38956839344336356182230539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51942452459115141576307385 38956839344336356182230539)
      ·
        refine ⟨58435259016504534273345809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38956839344336356182230539 58435259016504534273345809)
        ·
          refine ⟨43826444262378400705009357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58435259016504534273345809 43826444262378400705009357)
          ·
            refine ⟨16434916598391900264378509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43826444262378400705009357 16434916598391900264378509)
            ·
              refine ⟨6163093724396962599141941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16434916598391900264378509 6163093724396962599141941)
              ·
                refine ⟨577790036662215243669557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6163093724396962599141941 577790036662215243669557)
                ·
                  refine ⟨54167815937082679094021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 577790036662215243669557 54167815937082679094021)
                  ·
                    rfl

theorem cell23_949423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 5, 5].length) (baseStart_949423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949423 prefixEnd_949423 := by exact prefixLift 949423
  have htrace : WordTrace (prefixWord ++ tailWord_949423) baseStart_949423 baseEnd_949423 := by
    simpa [prefixWord, tailWord_949423, baseEnd_949423] using wordTrace_append hprefix tailTrace_949423
  have hstable : (prefixWord ++ tailWord_949423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949423).length < 2 ^ (prefixWord ++ tailWord_949423).sum := by decide
  have hdescent : baseEnd_949423 < baseStart_949423 := by decide
  rcases family_descends (prefixWord ++ tailWord_949423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949433 : List Nat := [1, 2, 1, 4, 1, 3, 1, 2, 2, 3, 3]
def baseStart_949433 : Nat := 118140960795 + 949433 * 2 ^ 59
def prefixEnd_949433 : Nat := 4983230072969 + 3 ^ 40 * 949433 * 2
def baseEnd_949433 : Nat := 487515478240289072721143

theorem tailTrace_949433 : CollatzResearch.WordTrace tailWord_949433 prefixEnd_949433 487515478240289072721143 := by
  unfold tailWord_949433
  simp only [CollatzResearch.WordTrace]
  refine ⟨34628666369373866092068953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23085777579582577394712635 34628666369373866092068953)
  ·
    refine ⟨25971499777030399569051715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34628666369373866092068953 25971499777030399569051715)
    ·
      refine ⟨38957249665545599353577573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25971499777030399569051715 38957249665545599353577573)
      ·
        refine ⟨7304484312289799878795795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38957249665545599353577573 7304484312289799878795795)
        ·
          refine ⟨10956726468434699818193693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7304484312289799878795795 10956726468434699818193693)
          ·
            refine ⟨4108772425663012431822635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10956726468434699818193693 4108772425663012431822635)
            ·
              refine ⟨6163158638494518647733953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4108772425663012431822635 6163158638494518647733953)
              ·
                refine ⟨4622368978870888985800465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6163158638494518647733953 4622368978870888985800465)
                ·
                  refine ⟨3466776734153166739350349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4622368978870888985800465 3466776734153166739350349)
                  ·
                    refine ⟨1300041275307437527256381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3466776734153166739350349 1300041275307437527256381)
                    ·
                      refine ⟨487515478240289072721143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1300041275307437527256381 487515478240289072721143)
                      ·
                        rfl

theorem cell23_949433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_949433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949433 prefixEnd_949433 := by exact prefixLift 949433
  have htrace : WordTrace (prefixWord ++ tailWord_949433) baseStart_949433 baseEnd_949433 := by
    simpa [prefixWord, tailWord_949433, baseEnd_949433] using wordTrace_append hprefix tailTrace_949433
  have hstable : (prefixWord ++ tailWord_949433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949433).length < 2 ^ (prefixWord ++ tailWord_949433).sum := by decide
  have hdescent : baseEnd_949433 < baseStart_949433 := by decide
  rcases family_descends (prefixWord ++ tailWord_949433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949443 : List Nat := [1, 1, 1, 3, 1, 1, 1, 5, 2, 5, 2]
def baseStart_949443 : Nat := 118140960795 + 949443 * 2 ^ 59
def prefixEnd_949443 : Nat := 4983230072969 + 3 ^ 40 * 949443 * 2
def baseEnd_949443 : Nat := 487520613046834033596097

theorem tailTrace_949443 : CollatzResearch.WordTrace tailWord_949443 prefixEnd_949443 487520613046834033596097 := by
  unfold tailWord_949443
  simp only [CollatzResearch.WordTrace]
  refine ⟨34629031099337637799932983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23086020732891758533288655 34629031099337637799932983)
  ·
    refine ⟨51943546649006456699899475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34629031099337637799932983 51943546649006456699899475)
    ·
      refine ⟨77915319973509685049849213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51943546649006456699899475 77915319973509685049849213)
      ·
        refine ⟨29218244990066131893693455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77915319973509685049849213 29218244990066131893693455)
        ·
          refine ⟨43827367485099197840540183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29218244990066131893693455 43827367485099197840540183)
          ·
            refine ⟨65741051227648796760810275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43827367485099197840540183 65741051227648796760810275)
            ·
              refine ⟨98611576841473195141215413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65741051227648796760810275 98611576841473195141215413)
              ·
                refine ⟨9244835328888112044488945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98611576841473195141215413 9244835328888112044488945)
                ·
                  refine ⟨6933626496666084033366709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9244835328888112044488945 6933626496666084033366709)
                  ·
                    refine ⟨650027484062445378128129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6933626496666084033366709 650027484062445378128129)
                    ·
                      refine ⟨487520613046834033596097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 650027484062445378128129 487520613046834033596097)
                      ·
                        rfl

theorem cell23_949443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 5, 2].length) (baseStart_949443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949443 prefixEnd_949443 := by exact prefixLift 949443
  have htrace : WordTrace (prefixWord ++ tailWord_949443) baseStart_949443 baseEnd_949443 := by
    simpa [prefixWord, tailWord_949443, baseEnd_949443] using wordTrace_append hprefix tailTrace_949443
  have hstable : (prefixWord ++ tailWord_949443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949443).length < 2 ^ (prefixWord ++ tailWord_949443).sum := by decide
  have hdescent : baseEnd_949443 < baseStart_949443 := by decide
  rcases family_descends (prefixWord ++ tailWord_949443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949466 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 1, 10]
def baseStart_949466 : Nat := 118140960795 + 949466 * 2 ^ 59
def prefixEnd_949466 : Nat := 4983230072969 + 3 ^ 40 * 949466 * 2
def baseEnd_949466 : Nat := 162510807700629147869497

theorem tailTrace_949466 : CollatzResearch.WordTrace tailWord_949466 prefixEnd_949466 162510807700629147869497 := by
  unfold tailWord_949466
  simp only [CollatzResearch.WordTrace]
  refine ⟨8657467494563578182005063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23086579985502875152013501 8657467494563578182005063)
  ·
    refine ⟨12986201241845367273007595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8657467494563578182005063 12986201241845367273007595)
    ·
      refine ⟨19479301862768050909511393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12986201241845367273007595 19479301862768050909511393)
      ·
        refine ⟨14609476397076038182133545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19479301862768050909511393 14609476397076038182133545)
        ·
          refine ⟨10957107297807028636600159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14609476397076038182133545 10957107297807028636600159)
          ·
            refine ⟨16435660946710542954900239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10957107297807028636600159 16435660946710542954900239)
            ·
              refine ⟨24653491420065814432350359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16435660946710542954900239 24653491420065814432350359)
              ·
                refine ⟨36980237130098721648525539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24653491420065814432350359 36980237130098721648525539)
                ·
                  refine ⟨55470355695148082472788309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36980237130098721648525539 55470355695148082472788309)
                  ·
                    refine ⟨162510807700629147869497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 55470355695148082472788309 162510807700629147869497)
                    ·
                      rfl

theorem cell23_949466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 1, 10].length) (baseStart_949466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949466 prefixEnd_949466 := by exact prefixLift 949466
  have htrace : WordTrace (prefixWord ++ tailWord_949466) baseStart_949466 baseEnd_949466 := by
    simpa [prefixWord, tailWord_949466, baseEnd_949466] using wordTrace_append hprefix tailTrace_949466
  have hstable : (prefixWord ++ tailWord_949466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949466).length < 2 ^ (prefixWord ++ tailWord_949466).sum := by decide
  have hdescent : baseEnd_949466 < baseStart_949466 := by decide
  rcases family_descends (prefixWord ++ tailWord_949466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949473 : List Nat := [1, 2, 3, 1, 3, 2, 2, 1, 1, 3, 4]
def baseStart_949473 : Nat := 118140960795 + 949473 * 2 ^ 59
def prefixEnd_949473 : Nat := 4983230072969 + 3 ^ 40 * 949473 * 2
def baseEnd_949473 : Nat := 487536017466468916220959

theorem tailTrace_949473 : CollatzResearch.WordTrace tailWord_949473 prefixEnd_949473 487536017466468916220959 := by
  unfold tailWord_949473
  simp only [CollatzResearch.WordTrace]
  refine ⟨34630125289228952923525073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23086750192819301949016715 34630125289228952923525073)
  ·
    refine ⟨25972593966921714692643805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34630125289228952923525073 25972593966921714692643805)
    ·
      refine ⟨9739722737595643009741427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25972593966921714692643805 9739722737595643009741427)
      ·
        refine ⟨14609584106393464514612141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9739722737595643009741427 14609584106393464514612141)
        ·
          refine ⟨5478594039897549192979553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14609584106393464514612141 5478594039897549192979553)
          ·
            refine ⟨4108945529923161894734665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5478594039897549192979553 4108945529923161894734665)
            ·
              refine ⟨3081709147442371421050999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4108945529923161894734665 3081709147442371421050999)
              ·
                refine ⟨4622563721163557131576499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3081709147442371421050999 4622563721163557131576499)
                ·
                  refine ⟨6933845581745335697364749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4622563721163557131576499 6933845581745335697364749)
                  ·
                    refine ⟨2600192093154500886511781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6933845581745335697364749 2600192093154500886511781)
                    ·
                      refine ⟨487536017466468916220959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2600192093154500886511781 487536017466468916220959)
                      ·
                        rfl

theorem cell23_949473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_949473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949473 prefixEnd_949473 := by exact prefixLift 949473
  have htrace : WordTrace (prefixWord ++ tailWord_949473) baseStart_949473 baseEnd_949473 := by
    simpa [prefixWord, tailWord_949473, baseEnd_949473] using wordTrace_append hprefix tailTrace_949473
  have hstable : (prefixWord ++ tailWord_949473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949473).length < 2 ^ (prefixWord ++ tailWord_949473).sum := by decide
  have hdescent : baseEnd_949473 < baseStart_949473 := by decide
  rcases family_descends (prefixWord ++ tailWord_949473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949513 : List Nat := [1, 2, 1, 1, 3, 3, 3, 3, 6]
def baseStart_949513 : Nat := 118140960795 + 949513 * 2 ^ 59
def prefixEnd_949513 : Nat := 4983230072969 + 3 ^ 40 * 949513 * 2
def baseEnd_949513 : Nat := 54172950743627639968975

theorem tailTrace_949513 : CollatzResearch.WordTrace tailWord_949513 prefixEnd_949513 54172950743627639968975 := by
  unfold tailWord_949513
  simp only [CollatzResearch.WordTrace]
  refine ⟨34631584209084039754981193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23087722806056026503320795 34631584209084039754981193)
  ·
    refine ⟨25973688156813029816235895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34631584209084039754981193 25973688156813029816235895)
    ·
      refine ⟨38960532235219544724353843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25973688156813029816235895 38960532235219544724353843)
      ·
        refine ⟨58440798352829317086530765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38960532235219544724353843 58440798352829317086530765)
        ·
          refine ⟨21915299382310993907449037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58440798352829317086530765 21915299382310993907449037)
          ·
            refine ⟨8218237268366622715293389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21915299382310993907449037 8218237268366622715293389)
            ·
              refine ⟨3081838975637483518235021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8218237268366622715293389 3081838975637483518235021)
              ·
                refine ⟨1155689615864056319338133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3081838975637483518235021 1155689615864056319338133)
                ·
                  refine ⟨54172950743627639968975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1155689615864056319338133 54172950743627639968975)
                  ·
                    rfl

theorem cell23_949513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 6].length) (baseStart_949513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949513 prefixEnd_949513 := by exact prefixLift 949513
  have htrace : WordTrace (prefixWord ++ tailWord_949513) baseStart_949513 baseEnd_949513 := by
    simpa [prefixWord, tailWord_949513, baseEnd_949513] using wordTrace_append hprefix tailTrace_949513
  have hstable : (prefixWord ++ tailWord_949513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949513).length < 2 ^ (prefixWord ++ tailWord_949513).sum := by decide
  have hdescent : baseEnd_949513 < baseStart_949513 := by decide
  rcases family_descends (prefixWord ++ tailWord_949513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949580 : List Nat := [2, 2, 1, 3, 2, 2, 2, 1, 3, 1, 4]
def baseStart_949580 : Nat := 118140960795 + 949580 * 2 ^ 59
def prefixEnd_949580 : Nat := 4983230072969 + 3 ^ 40 * 949580 * 2
def baseEnd_949580 : Nat := 487590959896499997582967

theorem tailTrace_949580 : CollatzResearch.WordTrace tailWord_949580 prefixEnd_949580 487590959896499997582967 := by
  unfold tailWord_949580
  simp only [CollatzResearch.WordTrace]
  refine ⟨17317013949920655098835097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23089351933227540131780129 17317013949920655098835097)
  ·
    refine ⟨12987760462440491324126323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17317013949920655098835097 12987760462440491324126323)
    ·
      refine ⟨19481640693660736986189485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12987760462440491324126323 19481640693660736986189485)
      ·
        refine ⟨7305615260122776369821057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19481640693660736986189485 7305615260122776369821057)
        ·
          refine ⟨5479211445092082277365793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7305615260122776369821057 5479211445092082277365793)
          ·
            refine ⟨4109408583819061708024345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5479211445092082277365793 4109408583819061708024345)
            ·
              refine ⟨3082056437864296281018259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4109408583819061708024345 3082056437864296281018259)
              ·
                refine ⟨4623084656796444421527389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3082056437864296281018259 4623084656796444421527389)
                ·
                  refine ⟨1733656746298666658072771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4623084656796444421527389 1733656746298666658072771)
                  ·
                    refine ⟨2600485119447999987109157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1733656746298666658072771 2600485119447999987109157)
                    ·
                      refine ⟨487590959896499997582967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2600485119447999987109157 487590959896499997582967)
                      ·
                        rfl

theorem cell23_949580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_949580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949580 prefixEnd_949580 := by exact prefixLift 949580
  have htrace : WordTrace (prefixWord ++ tailWord_949580) baseStart_949580 baseEnd_949580 := by
    simpa [prefixWord, tailWord_949580, baseEnd_949580] using wordTrace_append hprefix tailTrace_949580
  have hstable : (prefixWord ++ tailWord_949580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949580).length < 2 ^ (prefixWord ++ tailWord_949580).sum := by decide
  have hdescent : baseEnd_949580 < baseStart_949580 := by decide
  rcases family_descends (prefixWord ++ tailWord_949580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949603 : List Nat := [1, 1, 1, 5, 2, 3, 10]
def baseStart_949603 : Nat := 118140960795 + 949603 * 2 ^ 59
def prefixEnd_949603 : Nat := 4983230072969 + 3 ^ 40 * 949603 * 2
def baseEnd_949603 : Nat := 6019787283352511204881

theorem tailTrace_949603 : CollatzResearch.WordTrace tailWord_949603 prefixEnd_949603 6019787283352511204881 := by
  unfold tailWord_949603
  simp only [CollatzResearch.WordTrace]
  refine ⟨34634866778757985125757463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23089911185838656750504975 34634866778757985125757463)
  ·
    refine ⟨51952300168136977688636195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34634866778757985125757463 51952300168136977688636195)
    ·
      refine ⟨77928450252205466532954293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51952300168136977688636195 77928450252205466532954293)
      ·
        refine ⟨7305792211144262487464465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77928450252205466532954293 7305792211144262487464465)
        ·
          refine ⟨5479344158358196865598349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7305792211144262487464465 5479344158358196865598349)
          ·
            refine ⟨2054754059384323824599381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5479344158358196865598349 2054754059384323824599381)
            ·
              refine ⟨6019787283352511204881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2054754059384323824599381 6019787283352511204881)
              ·
                rfl

theorem cell23_949603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 10].length) (baseStart_949603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949603 prefixEnd_949603 := by exact prefixLift 949603
  have htrace : WordTrace (prefixWord ++ tailWord_949603) baseStart_949603 baseEnd_949603 := by
    simpa [prefixWord, tailWord_949603, baseEnd_949603] using wordTrace_append hprefix tailTrace_949603
  have hstable : (prefixWord ++ tailWord_949603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949603).length < 2 ^ (prefixWord ++ tailWord_949603).sum := by decide
  have hdescent : baseEnd_949603 < baseStart_949603 := by decide
  rcases family_descends (prefixWord ++ tailWord_949603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949607 : List Nat := [1, 1, 5, 1, 4, 1, 1, 1, 4, 4]
def baseStart_949607 : Nat := 118140960795 + 949607 * 2 ^ 59
def prefixEnd_949607 : Nat := 4983230072969 + 3 ^ 40 * 949607 * 2
def baseEnd_949607 : Nat := 162534941291390463981781

theorem tailTrace_949607 : CollatzResearch.WordTrace tailWord_949607 prefixEnd_949607 162534941291390463981781 := by
  unfold tailWord_949607
  simp only [CollatzResearch.WordTrace]
  refine ⟨34635012670743493808903075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23090008447162329205935383 34635012670743493808903075)
  ·
    refine ⟨51952519006115240713354613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34635012670743493808903075 51952519006115240713354613)
    ·
      refine ⟨4870548656823303816876995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51952519006115240713354613 4870548656823303816876995)
      ·
        refine ⟨7305822985234955725315493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4870548656823303816876995 7305822985234955725315493)
        ·
          refine ⟨1369841809731554198496655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7305822985234955725315493 1369841809731554198496655)
          ·
            refine ⟨2054762714597331297744983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1369841809731554198496655 2054762714597331297744983)
            ·
              refine ⟨3082144071895996946617475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2054762714597331297744983 3082144071895996946617475)
              ·
                refine ⟨4623216107843995419926213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3082144071895996946617475 4623216107843995419926213)
                ·
                  refine ⟨866853020220749141236165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4623216107843995419926213 866853020220749141236165)
                  ·
                    refine ⟨162534941291390463981781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 866853020220749141236165 162534941291390463981781)
                    ·
                      rfl

theorem cell23_949607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_949607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949607 prefixEnd_949607 := by exact prefixLift 949607
  have htrace : WordTrace (prefixWord ++ tailWord_949607) baseStart_949607 baseEnd_949607 := by
    simpa [prefixWord, tailWord_949607, baseEnd_949607] using wordTrace_append hprefix tailTrace_949607
  have hstable : (prefixWord ++ tailWord_949607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949607).length < 2 ^ (prefixWord ++ tailWord_949607).sum := by decide
  have hdescent : baseEnd_949607 < baseStart_949607 := by decide
  rcases family_descends (prefixWord ++ tailWord_949607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949643 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 5]
def baseStart_949643 : Nat := 118140960795 + 949643 * 2 ^ 59
def prefixEnd_949643 : Nat := 4983230072969 + 3 ^ 40 * 949643 * 2
def baseEnd_949643 : Nat := 487623309177733251095177

theorem tailTrace_949643 : CollatzResearch.WordTrace tailWord_949643 prefixEnd_949643 487623309177733251095177 := by
  unfold tailWord_949643
  simp only [CollatzResearch.WordTrace]
  refine ⟨34636325698613071957213583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23090883799075381304809055 34636325698613071957213583)
  ·
    refine ⟨51954488547919607935820375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34636325698613071957213583 51954488547919607935820375)
    ·
      refine ⟨77931732821879411903730563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51954488547919607935820375 77931732821879411903730563)
      ·
        refine ⟨116897599232819117855595845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77931732821879411903730563 116897599232819117855595845)
        ·
          refine ⟨21918299856153584597924221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116897599232819117855595845 21918299856153584597924221)
          ·
            refine ⟨8219362446057594224221583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21918299856153584597924221 8219362446057594224221583)
            ·
              refine ⟨12329043669086391336332375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8219362446057594224221583 12329043669086391336332375)
              ·
                refine ⟨18493565503629587004498563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12329043669086391336332375 18493565503629587004498563)
                ·
                  refine ⟨27740348255444380506747845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18493565503629587004498563 27740348255444380506747845)
                  ·
                    refine ⟨5201315297895821345015221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27740348255444380506747845 5201315297895821345015221)
                    ·
                      refine ⟨487623309177733251095177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5201315297895821345015221 487623309177733251095177)
                      ·
                        rfl

theorem cell23_949643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 5].length) (baseStart_949643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949643 prefixEnd_949643 := by exact prefixLift 949643
  have htrace : WordTrace (prefixWord ++ tailWord_949643) baseStart_949643 baseEnd_949643 := by
    simpa [prefixWord, tailWord_949643, baseEnd_949643] using wordTrace_append hprefix tailTrace_949643
  have hstable : (prefixWord ++ tailWord_949643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949643).length < 2 ^ (prefixWord ++ tailWord_949643).sum := by decide
  have hdescent : baseEnd_949643 < baseStart_949643 := by decide
  rcases family_descends (prefixWord ++ tailWord_949643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949683 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 6]
def baseStart_949683 : Nat := 118140960795 + 949683 * 2 ^ 59
def prefixEnd_949683 : Nat := 4983230072969 + 3 ^ 40 * 949683 * 2
def baseEnd_949683 : Nat := 487643848403913094594993

theorem tailTrace_949683 : CollatzResearch.WordTrace tailWord_949683 prefixEnd_949683 487643848403913094594993 := by
  unfold tailWord_949683
  simp only [CollatzResearch.WordTrace]
  refine ⟨34637784618468158788669703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23091856412312105859113135 34637784618468158788669703)
  ·
    refine ⟨51956676927702238183004555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34637784618468158788669703 51956676927702238183004555)
    ·
      refine ⟨77935015391553357274506833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51956676927702238183004555 77935015391553357274506833)
      ·
        refine ⟨58451261543665017955880125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77935015391553357274506833 58451261543665017955880125)
        ·
          refine ⟨21919223078874381733455047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58451261543665017955880125 21919223078874381733455047)
          ·
            refine ⟨32878834618311572600182571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21919223078874381733455047 32878834618311572600182571)
            ·
              refine ⟨49318251927467358900273857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32878834618311572600182571 49318251927467358900273857)
              ·
                refine ⟨36988688945600519175205393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49318251927467358900273857 36988688945600519175205393)
                ·
                  refine ⟨27741516709200389381404045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36988688945600519175205393 27741516709200389381404045)
                  ·
                    refine ⟨10403068765950146018026517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27741516709200389381404045 10403068765950146018026517)
                    ·
                      refine ⟨487643848403913094594993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10403068765950146018026517 487643848403913094594993)
                      ·
                        rfl

theorem cell23_949683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 6].length) (baseStart_949683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949683 prefixEnd_949683 := by exact prefixLift 949683
  have htrace : WordTrace (prefixWord ++ tailWord_949683) baseStart_949683 baseEnd_949683 := by
    simpa [prefixWord, tailWord_949683, baseEnd_949683] using wordTrace_append hprefix tailTrace_949683
  have hstable : (prefixWord ++ tailWord_949683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949683).length < 2 ^ (prefixWord ++ tailWord_949683).sum := by decide
  have hdescent : baseEnd_949683 < baseStart_949683 := by decide
  rcases family_descends (prefixWord ++ tailWord_949683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949687 : List Nat := [1, 1, 3, 1, 3, 2, 2, 3, 1, 4, 2]
def baseStart_949687 : Nat := 118140960795 + 949687 * 2 ^ 59
def prefixEnd_949687 : Nat := 4983230072969 + 3 ^ 40 * 949687 * 2
def baseEnd_949687 : Nat := 487645902326531078944975

theorem tailTrace_949687 : CollatzResearch.WordTrace tailWord_949687 prefixEnd_949687 487645902326531078944975 := by
  unfold tailWord_949687
  simp only [CollatzResearch.WordTrace]
  refine ⟨34637930510453667471815315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23091953673635778314543543 34637930510453667471815315)
  ·
    refine ⟨51956895765680501207722973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34637930510453667471815315 51956895765680501207722973)
    ·
      refine ⟨19483835912130187952896115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51956895765680501207722973 19483835912130187952896115)
      ·
        refine ⟨29225753868195281929344173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19483835912130187952896115 29225753868195281929344173)
        ·
          refine ⟨10959657700573230723504065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29225753868195281929344173 10959657700573230723504065)
          ·
            refine ⟨8219743275429923042628049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10959657700573230723504065 8219743275429923042628049)
            ·
              refine ⟨6164807456572442281971037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8219743275429923042628049 6164807456572442281971037)
              ·
                refine ⟨2311802796214665855739139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6164807456572442281971037 2311802796214665855739139)
                ·
                  refine ⟨3467704194321998783608709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2311802796214665855739139 3467704194321998783608709)
                  ·
                    refine ⟨650194536435374771926633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3467704194321998783608709 650194536435374771926633)
                    ·
                      refine ⟨487645902326531078944975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 650194536435374771926633 487645902326531078944975)
                      ·
                        rfl

theorem cell23_949687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 4, 2].length) (baseStart_949687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949687 prefixEnd_949687 := by exact prefixLift 949687
  have htrace : WordTrace (prefixWord ++ tailWord_949687) baseStart_949687 baseEnd_949687 := by
    simpa [prefixWord, tailWord_949687, baseEnd_949687] using wordTrace_append hprefix tailTrace_949687
  have hstable : (prefixWord ++ tailWord_949687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949687).length < 2 ^ (prefixWord ++ tailWord_949687).sum := by decide
  have hdescent : baseEnd_949687 < baseStart_949687 := by decide
  rcases family_descends (prefixWord ++ tailWord_949687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949721 : List Nat := [1, 2, 1, 2, 4, 3, 2, 2, 2, 2, 2]
def baseStart_949721 : Nat := 118140960795 + 949721 * 2 ^ 59
def prefixEnd_949721 : Nat := 4983230072969 + 3 ^ 40 * 949721 * 2
def baseEnd_949721 : Nat := 487663360668783945919819

theorem tailTrace_949721 : CollatzResearch.WordTrace tailWord_949721 prefixEnd_949721 487663360668783945919819 := by
  unfold tailWord_949721
  simp only [CollatzResearch.WordTrace]
  refine ⟨34639170592330491278553017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23092780394886994185702011 34639170592330491278553017)
  ·
    refine ⟨25979377944247868458914763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34639170592330491278553017 25979377944247868458914763)
    ·
      refine ⟨38969066916371802688372145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25979377944247868458914763 38969066916371802688372145)
      ·
        refine ⟨29226800187278852016279109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38969066916371802688372145 29226800187278852016279109)
        ·
          refine ⟨5480025035114784753052333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29226800187278852016279109 5480025035114784753052333)
          ·
            refine ⟨2055009388168044282394625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5480025035114784753052333 2055009388168044282394625)
            ·
              refine ⟨1541257041126033211795969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2055009388168044282394625 1541257041126033211795969)
              ·
                refine ⟨1155942780844524908846977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1541257041126033211795969 1155942780844524908846977)
                ·
                  refine ⟨866957085633393681635233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1155942780844524908846977 866957085633393681635233)
                  ·
                    refine ⟨650217814225045261226425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 866957085633393681635233 650217814225045261226425)
                    ·
                      refine ⟨487663360668783945919819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 650217814225045261226425 487663360668783945919819)
                      ·
                        rfl

theorem cell23_949721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 2, 2, 2].length) (baseStart_949721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949721 prefixEnd_949721 := by exact prefixLift 949721
  have htrace : WordTrace (prefixWord ++ tailWord_949721) baseStart_949721 baseEnd_949721 := by
    simpa [prefixWord, tailWord_949721, baseEnd_949721] using wordTrace_append hprefix tailTrace_949721
  have hstable : (prefixWord ++ tailWord_949721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949721).length < 2 ^ (prefixWord ++ tailWord_949721).sum := by decide
  have hdescent : baseEnd_949721 < baseStart_949721 := by decide
  rcases family_descends (prefixWord ++ tailWord_949721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949727 : List Nat := [1, 1, 2, 3, 3, 1, 3, 4, 5]
def baseStart_949727 : Nat := 118140960795 + 949727 * 2 ^ 59
def prefixEnd_949727 : Nat := 4983230072969 + 3 ^ 40 * 949727 * 2
def baseEnd_949727 : Nat := 54185160172523435827199

theorem tailTrace_949727 : CollatzResearch.WordTrace tailWord_949727 prefixEnd_949727 54185160172523435827199 := by
  unfold tailWord_949727
  simp only [CollatzResearch.WordTrace]
  refine ⟨34639389430308754303271435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23092926286872502868847623 34639389430308754303271435)
  ·
    refine ⟨51959084145463131454907153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34639389430308754303271435 51959084145463131454907153)
    ·
      refine ⟨38969313109097348591180365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51959084145463131454907153 38969313109097348591180365)
      ·
        refine ⟨14613492415911505721692637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38969313109097348591180365 14613492415911505721692637)
        ·
          refine ⟨5480059655966814645634739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14613492415911505721692637 5480059655966814645634739)
          ·
            refine ⟨8220089483950221968452109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5480059655966814645634739 8220089483950221968452109)
            ·
              refine ⟨3082533556481333238169541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8220089483950221968452109 3082533556481333238169541)
              ·
                refine ⟨577975041840249982156789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3082533556481333238169541 577975041840249982156789)
                ·
                  refine ⟨54185160172523435827199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 577975041840249982156789 54185160172523435827199)
                  ·
                    rfl

theorem cell23_949727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 4, 5].length) (baseStart_949727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949727 prefixEnd_949727 := by exact prefixLift 949727
  have htrace : WordTrace (prefixWord ++ tailWord_949727) baseStart_949727 baseEnd_949727 := by
    simpa [prefixWord, tailWord_949727, baseEnd_949727] using wordTrace_append hprefix tailTrace_949727
  have hstable : (prefixWord ++ tailWord_949727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949727).length < 2 ^ (prefixWord ++ tailWord_949727).sum := by decide
  have hdescent : baseEnd_949727 < baseStart_949727 := by decide
  rcases family_descends (prefixWord ++ tailWord_949727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949757 : List Nat := [1, 4, 1, 1, 1, 4, 3, 1, 2, 5]
def baseStart_949757 : Nat := 118140960795 + 949757 * 2 ^ 59
def prefixEnd_949757 : Nat := 4983230072969 + 3 ^ 40 * 949757 * 2
def baseEnd_949757 : Nat := 162560615324115268356551

theorem tailTrace_949757 : CollatzResearch.WordTrace tailWord_949757 prefixEnd_949757 162560615324115268356551 := by
  unfold tailWord_949757
  simp only [CollatzResearch.WordTrace]
  refine ⟨34640483620200069426863525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23093655746800046284575683 34640483620200069426863525)
  ·
    refine ⟨6495090678787513017536911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34640483620200069426863525 6495090678787513017536911)
    ·
      refine ⟨9742636018181269526305367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6495090678787513017536911 9742636018181269526305367)
      ·
        refine ⟨14613954027271904289458051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9742636018181269526305367 14613954027271904289458051)
        ·
          refine ⟨21920931040907856434187077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14613954027271904289458051 21920931040907856434187077)
          ·
            refine ⟨4110174570170223081410077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21920931040907856434187077 4110174570170223081410077)
            ·
              refine ⟨1541315463813833655528779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4110174570170223081410077 1541315463813833655528779)
              ·
                refine ⟨2311973195720750483293169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1541315463813833655528779 2311973195720750483293169)
                ·
                  refine ⟨1733979896790562862469877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2311973195720750483293169 1733979896790562862469877)
                  ·
                    refine ⟨162560615324115268356551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1733979896790562862469877 162560615324115268356551)
                    ·
                      rfl

theorem cell23_949757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_949757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949757 prefixEnd_949757 := by exact prefixLift 949757
  have htrace : WordTrace (prefixWord ++ tailWord_949757) baseStart_949757 baseEnd_949757 := by
    simpa [prefixWord, tailWord_949757, baseEnd_949757] using wordTrace_append hprefix tailTrace_949757
  have hstable : (prefixWord ++ tailWord_949757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949757).length < 2 ^ (prefixWord ++ tailWord_949757).sum := by decide
  have hdescent : baseEnd_949757 < baseStart_949757 := by decide
  rcases family_descends (prefixWord ++ tailWord_949757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949777 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 4, 4, 2]
def baseStart_949777 : Nat := 118140960795 + 949777 * 2 ^ 59
def prefixEnd_949777 : Nat := 4983230072969 + 3 ^ 40 * 949777 * 2
def baseEnd_949777 : Nat := 487692115585435726819561

theorem tailTrace_949777 : CollatzResearch.WordTrace tailWord_949777 prefixEnd_949777 487692115585435726819561 := by
  unfold tailWord_949777
  simp only [CollatzResearch.WordTrace]
  refine ⟨34641213080127612842591585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23094142053418408561727723 34641213080127612842591585)
  ·
    refine ⟨25980909810095709631943689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34641213080127612842591585 25980909810095709631943689)
    ·
      refine ⟨19485682357571782223957767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25980909810095709631943689 19485682357571782223957767)
      ·
        refine ⟨29228523536357673335936651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19485682357571782223957767 29228523536357673335936651)
        ·
          refine ⟨43842785304536510003904977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29228523536357673335936651 43842785304536510003904977)
          ·
            refine ⟨32882088978402382502928733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43842785304536510003904977 32882088978402382502928733)
            ·
              refine ⟨12330783366900893438598275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32882088978402382502928733 12330783366900893438598275)
              ·
                refine ⟨18496175050351340157897413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12330783366900893438598275 18496175050351340157897413)
                ·
                  refine ⟨3468032821940876279605765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18496175050351340157897413 3468032821940876279605765)
                  ·
                    refine ⟨650256154113914302426081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3468032821940876279605765 650256154113914302426081)
                    ·
                      refine ⟨487692115585435726819561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 650256154113914302426081 487692115585435726819561)
                      ·
                        rfl

theorem cell23_949777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 4, 2].length) (baseStart_949777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949777 prefixEnd_949777 := by exact prefixLift 949777
  have htrace : WordTrace (prefixWord ++ tailWord_949777) baseStart_949777 baseEnd_949777 := by
    simpa [prefixWord, tailWord_949777, baseEnd_949777] using wordTrace_append hprefix tailTrace_949777
  have hstable : (prefixWord ++ tailWord_949777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949777).length < 2 ^ (prefixWord ++ tailWord_949777).sum := by decide
  have hdescent : baseEnd_949777 < baseStart_949777 := by decide
  rcases family_descends (prefixWord ++ tailWord_949777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949794 : List Nat := [3, 3, 1, 1, 1, 1, 4, 1, 2, 4, 2]
def baseStart_949794 : Nat := 118140960795 + 949794 * 2 ^ 59
def prefixEnd_949794 : Nat := 4983230072969 + 3 ^ 40 * 949794 * 2
def baseEnd_949794 : Nat := 487700844756562160306983

theorem tailTrace_949794 : CollatzResearch.WordTrace tailWord_949794 prefixEnd_949794 487700844756562160306983 := by
  unfold tailWord_949794
  simp only [CollatzResearch.WordTrace]
  refine ⟨8660458280266506186490109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23094555414044016497306957 8660458280266506186490109)
  ·
    refine ⟨3247671855099939819933791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8660458280266506186490109 3247671855099939819933791)
    ·
      refine ⟨4871507782649909729900687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3247671855099939819933791 4871507782649909729900687)
      ·
        refine ⟨7307261673974864594851031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4871507782649909729900687 7307261673974864594851031)
        ·
          refine ⟨10960892510962296892276547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7307261673974864594851031 10960892510962296892276547)
          ·
            refine ⟨16441338766443445338414821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10960892510962296892276547 16441338766443445338414821)
            ·
              refine ⟨3082751018708146000952779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16441338766443445338414821 3082751018708146000952779)
              ·
                refine ⟨4624126528062219001429169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3082751018708146000952779 4624126528062219001429169)
                ·
                  refine ⟨3468094896046664251071877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4624126528062219001429169 3468094896046664251071877)
                  ·
                    refine ⟨650267793008749547075977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3468094896046664251071877 650267793008749547075977)
                    ·
                      refine ⟨487700844756562160306983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 650267793008749547075977 487700844756562160306983)
                      ·
                        rfl

theorem cell23_949794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_949794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949794 prefixEnd_949794 := by exact prefixLift 949794
  have htrace : WordTrace (prefixWord ++ tailWord_949794) baseStart_949794 baseEnd_949794 := by
    simpa [prefixWord, tailWord_949794, baseEnd_949794] using wordTrace_append hprefix tailTrace_949794
  have hstable : (prefixWord ++ tailWord_949794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949794).length < 2 ^ (prefixWord ++ tailWord_949794).sum := by decide
  have hdescent : baseEnd_949794 < baseStart_949794 := by decide
  rcases family_descends (prefixWord ++ tailWord_949794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949864 : List Nat := [2, 1, 4, 3, 1, 2, 1, 1, 3, 5]
def baseStart_949864 : Nat := 118140960795 + 949864 * 2 ^ 59
def prefixEnd_949864 : Nat := 4983230072969 + 3 ^ 40 * 949864 * 2
def baseEnd_949864 : Nat := 162578929467458962143887

theorem tailTrace_949864 : CollatzResearch.WordTrace tailWord_949864 prefixEnd_949864 162578929467458962143887 := by
  unfold tailWord_949864
  simp only [CollatzResearch.WordTrace]
  refine ⟨17322193115406213350504323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23096257487208284467339097 17322193115406213350504323)
  ·
    refine ⟨25983289673109320025756485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17322193115406213350504323 25983289673109320025756485)
    ·
      refine ⟨4871866813707997504829341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25983289673109320025756485 4871866813707997504829341)
      ·
        refine ⟨1826950055140499064311003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4871866813707997504829341 1826950055140499064311003)
        ·
          refine ⟨2740425082710748596466505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1826950055140499064311003 2740425082710748596466505)
          ·
            refine ⟨2055318812033061447349879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2740425082710748596466505 2055318812033061447349879)
            ·
              refine ⟨3082978218049592171024819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2055318812033061447349879 3082978218049592171024819)
              ·
                refine ⟨4624467327074388256537229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3082978218049592171024819 4624467327074388256537229)
                ·
                  refine ⟨1734175247652895596201461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4624467327074388256537229 1734175247652895596201461)
                  ·
                    refine ⟨162578929467458962143887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1734175247652895596201461 162578929467458962143887)
                    ·
                      rfl

theorem cell23_949864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_949864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949864 prefixEnd_949864 := by exact prefixLift 949864
  have htrace : WordTrace (prefixWord ++ tailWord_949864) baseStart_949864 baseEnd_949864 := by
    simpa [prefixWord, tailWord_949864, baseEnd_949864] using wordTrace_append hprefix tailTrace_949864
  have hstable : (prefixWord ++ tailWord_949864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949864).length < 2 ^ (prefixWord ++ tailWord_949864).sum := by decide
  have hdescent : baseEnd_949864 < baseStart_949864 := by decide
  rcases family_descends (prefixWord ++ tailWord_949864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949895 : List Nat := [1, 1, 4, 2, 1, 5, 2, 2, 1, 1, 3]
def baseStart_949895 : Nat := 118140960795 + 949895 * 2 ^ 59
def prefixEnd_949895 : Nat := 4983230072969 + 3 ^ 40 * 949895 * 2
def baseEnd_949895 : Nat := 487752706302666265144019

theorem tailTrace_949895 : CollatzResearch.WordTrace tailWord_949895 prefixEnd_949895 487752706302666265144019 := by
  unfold tailWord_949895
  simp only [CollatzResearch.WordTrace]
  refine ⟨34645516893700118995387139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23097011262466745996924759 34645516893700118995387139)
  ·
    refine ⟨51968275340550178493080709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34645516893700118995387139 51968275340550178493080709)
    ·
      refine ⟨9744051626353158467452633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51968275340550178493080709 9744051626353158467452633)
      ·
        refine ⟨7308038719764868850589475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9744051626353158467452633 7308038719764868850589475)
        ·
          refine ⟨10962058079647303275884213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7308038719764868850589475 10962058079647303275884213)
          ·
            refine ⟨1027692944966934682114145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10962058079647303275884213 1027692944966934682114145)
            ·
              refine ⟨770769708725201011585609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1027692944966934682114145 770769708725201011585609)
              ·
                refine ⟨578077281543900758689207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 770769708725201011585609 578077281543900758689207)
                ·
                  refine ⟨867115922315851138033811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 578077281543900758689207 867115922315851138033811)
                  ·
                    refine ⟨1300673883473776707050717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 867115922315851138033811 1300673883473776707050717)
                    ·
                      refine ⟨487752706302666265144019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1300673883473776707050717 487752706302666265144019)
                      ·
                        rfl

theorem cell23_949895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 2, 1, 1, 3].length) (baseStart_949895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949895 prefixEnd_949895 := by exact prefixLift 949895
  have htrace : WordTrace (prefixWord ++ tailWord_949895) baseStart_949895 baseEnd_949895 := by
    simpa [prefixWord, tailWord_949895, baseEnd_949895] using wordTrace_append hprefix tailTrace_949895
  have hstable : (prefixWord ++ tailWord_949895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949895).length < 2 ^ (prefixWord ++ tailWord_949895).sum := by decide
  have hdescent : baseEnd_949895 < baseStart_949895 := by decide
  rcases family_descends (prefixWord ++ tailWord_949895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949918 : List Nat := [4, 3, 1, 1, 1, 2, 1, 1, 5, 2, 2]
def baseStart_949918 : Nat := 118140960795 + 949918 * 2 ^ 59
def prefixEnd_949918 : Nat := 4983230072969 + 3 ^ 40 * 949918 * 2
def baseEnd_949918 : Nat := 487764516357719675156413

theorem tailTrace_949918 : CollatzResearch.WordTrace tailWord_949918 prefixEnd_949918 487764516357719675156413 := by
  unfold tailWord_949918
  simp only [CollatzResearch.WordTrace]
  refine ⟨4330794471577099240434301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23097570515077862615649605 4330794471577099240434301)
  ·
    refine ⟨1624047926841412215162863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4330794471577099240434301 1624047926841412215162863)
    ·
      refine ⟨2436071890262118322744295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1624047926841412215162863 2436071890262118322744295)
      ·
        refine ⟨3654107835393177484116443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2436071890262118322744295 3654107835393177484116443)
        ·
          refine ⟨5481161753089766226174665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3654107835393177484116443 5481161753089766226174665)
          ·
            refine ⟨4110871314817324669630999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5481161753089766226174665 4110871314817324669630999)
            ·
              refine ⟨6166306972225987004446499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4110871314817324669630999 6166306972225987004446499)
              ·
                refine ⟨9249460458338980506669749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6166306972225987004446499 9249460458338980506669749)
                ·
                  refine ⟨867136917969279422500289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9249460458338980506669749 867136917969279422500289)
                  ·
                    refine ⟨650352688476959566875217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 867136917969279422500289 650352688476959566875217)
                    ·
                      refine ⟨487764516357719675156413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 650352688476959566875217 487764516357719675156413)
                      ·
                        rfl

theorem cell23_949918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_949918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949918 prefixEnd_949918 := by exact prefixLift 949918
  have htrace : WordTrace (prefixWord ++ tailWord_949918) baseStart_949918 baseEnd_949918 := by
    simpa [prefixWord, tailWord_949918, baseEnd_949918] using wordTrace_append hprefix tailTrace_949918
  have hstable : (prefixWord ++ tailWord_949918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949918).length < 2 ^ (prefixWord ++ tailWord_949918).sum := by decide
  have hdescent : baseEnd_949918 < baseStart_949918 := by decide
  rcases family_descends (prefixWord ++ tailWord_949918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949922 : List Nat := [3, 3, 1, 4, 2, 1, 1, 1, 2, 3, 2]
def baseStart_949922 : Nat := 118140960795 + 949922 * 2 ^ 59
def prefixEnd_949922 : Nat := 4983230072969 + 3 ^ 40 * 949922 * 2
def baseEnd_949922 : Nat := 487766570280337659506395

theorem tailTrace_949922 : CollatzResearch.WordTrace tailWord_949922 prefixEnd_949922 487766570280337659506395 := by
  unfold tailWord_949922
  simp only [CollatzResearch.WordTrace]
  refine ⟨8661625416150575651655005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23097667776401535071080013 8661625416150575651655005)
  ·
    refine ⟨3248109531056465869370627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8661625416150575651655005 3248109531056465869370627)
    ·
      refine ⟨4872164296584698804055941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3248109531056465869370627 4872164296584698804055941)
      ·
        refine ⟨913530805609631025760489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4872164296584698804055941 913530805609631025760489)
        ·
          refine ⟨685148104207223269320367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 913530805609631025760489 685148104207223269320367)
          ·
            refine ⟨1027722156310834903980551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685148104207223269320367 1027722156310834903980551)
            ·
              refine ⟨1541583234466252355970827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1027722156310834903980551 1541583234466252355970827)
              ·
                refine ⟨2312374851699378533956241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1541583234466252355970827 2312374851699378533956241)
                ·
                  refine ⟨1734281138774533900467181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2312374851699378533956241 1734281138774533900467181)
                  ·
                    refine ⟨650355427040450212675193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1734281138774533900467181 650355427040450212675193)
                    ·
                      refine ⟨487766570280337659506395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 650355427040450212675193 487766570280337659506395)
                      ·
                        rfl

theorem cell23_949922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_949922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949922 prefixEnd_949922 := by exact prefixLift 949922
  have htrace : WordTrace (prefixWord ++ tailWord_949922) baseStart_949922 baseEnd_949922 := by
    simpa [prefixWord, tailWord_949922, baseEnd_949922] using wordTrace_append hprefix tailTrace_949922
  have hstable : (prefixWord ++ tailWord_949922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949922).length < 2 ^ (prefixWord ++ tailWord_949922).sum := by decide
  have hdescent : baseEnd_949922 < baseStart_949922 := by decide
  rcases family_descends (prefixWord ++ tailWord_949922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949924 : List Nat := [2, 3, 1, 2, 2, 3, 3, 7]
def baseStart_949924 : Nat := 118140960795 + 949924 * 2 ^ 59
def prefixEnd_949924 : Nat := 4983230072969 + 3 ^ 40 * 949924 * 2
def baseEnd_949924 : Nat := 18065466564505431543755

theorem tailTrace_949924 : CollatzResearch.WordTrace tailWord_949924 prefixEnd_949924 18065466564505431543755 := by
  unfold tailWord_949924
  simp only [CollatzResearch.WordTrace]
  refine ⟨17323287305297528474096413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23097716407063371298795217 17323287305297528474096413)
  ·
    refine ⟨6496232739486573177786155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17323287305297528474096413 6496232739486573177786155)
    ·
      refine ⟨9744349109229859766679233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6496232739486573177786155 9744349109229859766679233)
      ·
        refine ⟨7308261831922394825009425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9744349109229859766679233 7308261831922394825009425)
        ·
          refine ⟨5481196373941796118757069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7308261831922394825009425 5481196373941796118757069)
          ·
            refine ⟨2055448640228173544533901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5481196373941796118757069 2055448640228173544533901)
            ·
              refine ⟨770793240085565079200213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2055448640228173544533901 770793240085565079200213)
              ·
                refine ⟨18065466564505431543755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 770793240085565079200213 18065466564505431543755)
                ·
                  rfl

theorem cell23_949924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 7].length) (baseStart_949924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949924 prefixEnd_949924 := by exact prefixLift 949924
  have htrace : WordTrace (prefixWord ++ tailWord_949924) baseStart_949924 baseEnd_949924 := by
    simpa [prefixWord, tailWord_949924, baseEnd_949924] using wordTrace_append hprefix tailTrace_949924
  have hstable : (prefixWord ++ tailWord_949924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949924).length < 2 ^ (prefixWord ++ tailWord_949924).sum := by decide
  have hdescent : baseEnd_949924 < baseStart_949924 := by decide
  rcases family_descends (prefixWord ++ tailWord_949924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949978 : List Nat := [3, 1, 1, 2, 2, 4, 2, 2, 1, 3, 2]
def baseStart_949978 : Nat := 118140960795 + 949978 * 2 ^ 59
def prefixEnd_949978 : Nat := 4983230072969 + 3 ^ 40 * 949978 * 2
def baseEnd_949978 : Nat := 487795325196989440406137

theorem tailTrace_949978 : CollatzResearch.WordTrace tailWord_949978 prefixEnd_949978 487795325196989440406137 := by
  unfold tailWord_949978
  simp only [CollatzResearch.WordTrace]
  refine ⟨8662136038099856042664647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23099029434932949447105725 8662136038099856042664647)
  ·
    refine ⟨12993204057149784063996971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8662136038099856042664647 12993204057149784063996971)
    ·
      refine ⟨19489806085724676095995457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12993204057149784063996971 19489806085724676095995457)
      ·
        refine ⟨14617354564293507071996593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19489806085724676095995457 14617354564293507071996593)
        ·
          refine ⟨10963015923220130303997445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14617354564293507071996593 10963015923220130303997445)
          ·
            refine ⟨2055565485603774431999521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10963015923220130303997445 2055565485603774431999521)
            ·
              refine ⟨1541674114202830823999641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2055565485603774431999521 1541674114202830823999641)
              ·
                refine ⟨1156255585652123117999731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1541674114202830823999641 1156255585652123117999731)
                ·
                  refine ⟨1734383378478184676999597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1156255585652123117999731 1734383378478184676999597)
                  ·
                    refine ⟨650393766929319253874849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1734383378478184676999597 650393766929319253874849)
                    ·
                      refine ⟨487795325196989440406137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 650393766929319253874849 487795325196989440406137)
                      ·
                        rfl

theorem cell23_949978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 1, 3, 2].length) (baseStart_949978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_949978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_949978 prefixEnd_949978 := by exact prefixLift 949978
  have htrace : WordTrace (prefixWord ++ tailWord_949978) baseStart_949978 baseEnd_949978 := by
    simpa [prefixWord, tailWord_949978, baseEnd_949978] using wordTrace_append hprefix tailTrace_949978
  have hstable : (prefixWord ++ tailWord_949978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949978).length < 2 ^ (prefixWord ++ tailWord_949978).sum := by decide
  have hdescent : baseEnd_949978 < baseStart_949978 := by decide
  rcases family_descends (prefixWord ++ tailWord_949978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950024 : List Nat := [2, 1, 3, 2, 2, 1, 2, 1, 1, 5, 3]
def baseStart_950024 : Nat := 118140960795 + 950024 * 2 ^ 59
def prefixEnd_950024 : Nat := 4983230072969 + 3 ^ 40 * 950024 * 2
def baseEnd_950024 : Nat := 487818945307096260430925

theorem tailTrace_950024 : CollatzResearch.WordTrace tailWord_950024 prefixEnd_950024 487818945307096260430925 := by
  unfold tailWord_950024
  simp only [CollatzResearch.WordTrace]
  refine ⟨17325110955116387013416563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23100147940155182684555417 17325110955116387013416563)
  ·
    refine ⟨25987666432674580520124845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17325110955116387013416563 25987666432674580520124845)
    ·
      refine ⟨9745374912252967695046817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25987666432674580520124845 9745374912252967695046817)
      ·
        refine ⟨7309031184189725771285113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9745374912252967695046817 7309031184189725771285113)
        ·
          refine ⟨5481773388142294328463835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7309031184189725771285113 5481773388142294328463835)
          ·
            refine ⟨8222660082213441492695753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5481773388142294328463835 8222660082213441492695753)
            ·
              refine ⟨6166995061660081119521815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8222660082213441492695753 6166995061660081119521815)
              ·
                refine ⟨9250492592490121679282723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6166995061660081119521815 9250492592490121679282723)
                ·
                  refine ⟨13875738888735182518924085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9250492592490121679282723 13875738888735182518924085)
                  ·
                    refine ⟨1300850520818923361149133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13875738888735182518924085 1300850520818923361149133)
                    ·
                      refine ⟨487818945307096260430925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1300850520818923361149133 487818945307096260430925)
                      ·
                        rfl

theorem cell23_950024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_950024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950024 prefixEnd_950024 := by exact prefixLift 950024
  have htrace : WordTrace (prefixWord ++ tailWord_950024) baseStart_950024 baseEnd_950024 := by
    simpa [prefixWord, tailWord_950024, baseEnd_950024] using wordTrace_append hprefix tailTrace_950024
  have hstable : (prefixWord ++ tailWord_950024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950024).length < 2 ^ (prefixWord ++ tailWord_950024).sum := by decide
  have hdescent : baseEnd_950024 < baseStart_950024 := by decide
  rcases family_descends (prefixWord ++ tailWord_950024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950027 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 3, 7]
def baseStart_950027 : Nat := 118140960795 + 950027 * 2 ^ 59
def prefixEnd_950027 : Nat := 4983230072969 + 3 ^ 40 * 950027 * 2
def baseEnd_950027 : Nat := 162606828583019916231137

theorem tailTrace_950027 : CollatzResearch.WordTrace tailWord_950027 prefixEnd_950027 162606828583019916231137 := by
  unfold tailWord_950027
  simp only [CollatzResearch.WordTrace]
  refine ⟨34650331329221905539192335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23100220886147937026128223 34650331329221905539192335)
  ·
    refine ⟨51975496993832858308788503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34650331329221905539192335 51975496993832858308788503)
    ·
      refine ⟨77963245490749287463182755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51975496993832858308788503 77963245490749287463182755)
      ·
        refine ⟨116944868236123931194774133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77963245490749287463182755 116944868236123931194774133)
        ·
          refine ⟨10963581397136618549510075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116944868236123931194774133 10963581397136618549510075)
          ·
            refine ⟨16445372095704927824265113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10963581397136618549510075 16445372095704927824265113)
            ·
              refine ⟨12334029071778695868198835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16445372095704927824265113 12334029071778695868198835)
              ·
                refine ⟨18501043607668043802298253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12334029071778695868198835 18501043607668043802298253)
                ·
                  refine ⟨6937891352875516425861845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18501043607668043802298253 6937891352875516425861845)
                  ·
                    refine ⟨162606828583019916231137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6937891352875516425861845 162606828583019916231137)
                    ·
                      rfl

theorem cell23_950027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 7].length) (baseStart_950027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950027 prefixEnd_950027 := by exact prefixLift 950027
  have htrace : WordTrace (prefixWord ++ tailWord_950027) baseStart_950027 baseEnd_950027 := by
    simpa [prefixWord, tailWord_950027, baseEnd_950027] using wordTrace_append hprefix tailTrace_950027
  have hstable : (prefixWord ++ tailWord_950027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950027).length < 2 ^ (prefixWord ++ tailWord_950027).sum := by decide
  have hdescent : baseEnd_950027 < baseStart_950027 := by decide
  rcases family_descends (prefixWord ++ tailWord_950027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950029 : List Nat := [1, 7, 2, 1, 1, 1, 1, 1, 3, 3, 2]
def baseStart_950029 : Nat := 118140960795 + 950029 * 2 ^ 59
def prefixEnd_950029 : Nat := 4983230072969 + 3 ^ 40 * 950029 * 2
def baseEnd_950029 : Nat := 487821512710368740868403

theorem tailTrace_950029 : CollatzResearch.WordTrace tailWord_950029 prefixEnd_950029 487821512710368740868403 := by
  unfold tailWord_950029
  simp only [CollatzResearch.WordTrace]
  refine ⟨34650404275214659880765141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23100269516809773253843427 34650404275214659880765141)
  ·
    refine ⟨812118850200343590955433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 34650404275214659880765141 812118850200343590955433)
    ·
      refine ⟨609089137650257693216575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 812118850200343590955433 609089137650257693216575)
      ·
        refine ⟨913633706475386539824863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609089137650257693216575 913633706475386539824863)
        ·
          refine ⟨1370450559713079809737295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 913633706475386539824863 1370450559713079809737295)
          ·
            refine ⟨2055675839569619714605943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1370450559713079809737295 2055675839569619714605943)
            ·
              refine ⟨3083513759354429571908915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2055675839569619714605943 3083513759354429571908915)
              ·
                refine ⟨4625270639031644357863373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3083513759354429571908915 4625270639031644357863373)
                ·
                  refine ⟨1734476489636866634198765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4625270639031644357863373 1734476489636866634198765)
                  ·
                    refine ⟨650428683613824987824537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1734476489636866634198765 650428683613824987824537)
                    ·
                      refine ⟨487821512710368740868403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 650428683613824987824537 487821512710368740868403)
                      ·
                        rfl

theorem cell23_950029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_950029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950029 prefixEnd_950029 := by exact prefixLift 950029
  have htrace : WordTrace (prefixWord ++ tailWord_950029) baseStart_950029 baseEnd_950029 := by
    simpa [prefixWord, tailWord_950029, baseEnd_950029] using wordTrace_append hprefix tailTrace_950029
  have hstable : (prefixWord ++ tailWord_950029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950029).length < 2 ^ (prefixWord ++ tailWord_950029).sum := by decide
  have hdescent : baseEnd_950029 < baseStart_950029 := by decide
  rcases family_descends (prefixWord ++ tailWord_950029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950068 : List Nat := [2, 5, 1, 1, 2, 1, 1, 1, 2, 5, 2]
def baseStart_950068 : Nat := 118140960795 + 950068 * 2 ^ 59
def prefixEnd_950068 : Nat := 4983230072969 + 3 ^ 40 * 950068 * 2
def baseEnd_950068 : Nat := 487841538455894088280723

theorem tailTrace_950068 : CollatzResearch.WordTrace tailWord_950068 prefixEnd_950068 487841538455894088280723 := by
  unfold tailWord_950068
  simp only [CollatzResearch.WordTrace]
  refine ⟨17325913361036684770717429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23101217814715579694289905 17325913361036684770717429)
  ·
    refine ⟨1624304377597189197254759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17325913361036684770717429 1624304377597189197254759)
    ·
      refine ⟨2436456566395783795882139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1624304377597189197254759 2436456566395783795882139)
      ·
        refine ⟨3654684849593675693823209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2436456566395783795882139 3654684849593675693823209)
        ·
          refine ⟨2741013637195256770367407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3654684849593675693823209 2741013637195256770367407)
          ·
            refine ⟨4111520455792885155551111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2741013637195256770367407 4111520455792885155551111)
            ·
              refine ⟨6167280683689327733326667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4111520455792885155551111 6167280683689327733326667)
              ·
                refine ⟨9250921025533991599990001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6167280683689327733326667 9250921025533991599990001)
                ·
                  refine ⟨6938190769150493699992501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9250921025533991599990001 6938190769150493699992501)
                  ·
                    refine ⟨650455384607858784374297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6938190769150493699992501 650455384607858784374297)
                    ·
                      refine ⟨487841538455894088280723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 650455384607858784374297 487841538455894088280723)
                      ·
                        rfl

theorem cell23_950068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_950068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950068 prefixEnd_950068 := by exact prefixLift 950068
  have htrace : WordTrace (prefixWord ++ tailWord_950068) baseStart_950068 baseEnd_950068 := by
    simpa [prefixWord, tailWord_950068, baseEnd_950068] using wordTrace_append hprefix tailTrace_950068
  have hstable : (prefixWord ++ tailWord_950068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950068).length < 2 ^ (prefixWord ++ tailWord_950068).sum := by decide
  have hdescent : baseEnd_950068 < baseStart_950068 := by decide
  rcases family_descends (prefixWord ++ tailWord_950068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950098 : List Nat := [3, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4]
def baseStart_950098 : Nat := 118140960795 + 950098 * 2 ^ 59
def prefixEnd_950098 : Nat := 4983230072969 + 3 ^ 40 * 950098 * 2
def baseEnd_950098 : Nat := 487856942875528970905585

theorem tailTrace_950098 : CollatzResearch.WordTrace tailWord_950098 prefixEnd_950098 487856942875528970905585 := by
  unfold tailWord_950098
  simp only [CollatzResearch.WordTrace]
  refine ⟨8663230227991171166256737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23101947274643123110017965 8663230227991171166256737)
  ·
    refine ⟨6497422670993378374692553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8663230227991171166256737 6497422670993378374692553)
    ·
      refine ⟨4873067003245033781019415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6497422670993378374692553 4873067003245033781019415)
      ·
        refine ⟨7309600504867550671529123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4873067003245033781019415 7309600504867550671529123)
        ·
          refine ⟨10964400757301326007293685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7309600504867550671529123 10964400757301326007293685)
          ·
            refine ⟨1027912570996999313183783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10964400757301326007293685 1027912570996999313183783)
            ·
              refine ⟨1541868856495498969775675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1027912570996999313183783 1541868856495498969775675)
              ·
                refine ⟨2312803284743248454663513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1541868856495498969775675 2312803284743248454663513)
                ·
                  refine ⟨1734602463557436340997635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2312803284743248454663513 1734602463557436340997635)
                  ·
                    refine ⟨2601903695336154511496453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1734602463557436340997635 2601903695336154511496453)
                    ·
                      refine ⟨487856942875528970905585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2601903695336154511496453 487856942875528970905585)
                      ·
                        rfl

theorem cell23_950098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_950098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950098 prefixEnd_950098 := by exact prefixLift 950098
  have htrace : WordTrace (prefixWord ++ tailWord_950098) baseStart_950098 baseEnd_950098 := by
    simpa [prefixWord, tailWord_950098, baseEnd_950098] using wordTrace_append hprefix tailTrace_950098
  have hstable : (prefixWord ++ tailWord_950098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950098).length < 2 ^ (prefixWord ++ tailWord_950098).sum := by decide
  have hdescent : baseEnd_950098 < baseStart_950098 := by decide
  rcases family_descends (prefixWord ++ tailWord_950098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950101 : List Nat := [1, 3, 2, 2, 2, 3, 1, 1, 1, 4, 3]
def baseStart_950101 : Nat := 118140960795 + 950101 * 2 ^ 59
def prefixEnd_950101 : Nat := 4983230072969 + 3 ^ 40 * 950101 * 2
def baseEnd_950101 : Nat := 487858483317492459168071

theorem tailTrace_950101 : CollatzResearch.WordTrace tailWord_950101 prefixEnd_950101 487858483317492459168071 := by
  unfold tailWord_950101
  simp only [CollatzResearch.WordTrace]
  refine ⟨34653030330953816177386157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23102020220635877451590771 34653030330953816177386157)
  ·
    refine ⟨12994886374107681066519809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34653030330953816177386157 12994886374107681066519809)
    ·
      refine ⟨9746164780580760799889857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12994886374107681066519809 9746164780580760799889857)
      ·
        refine ⟨7309623585435570599917393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9746164780580760799889857 7309623585435570599917393)
        ·
          refine ⟨5482217689076677949938045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7309623585435570599917393 5482217689076677949938045)
          ·
            refine ⟨2055831633403754231226767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5482217689076677949938045 2055831633403754231226767)
            ·
              refine ⟨3083747450105631346840151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2055831633403754231226767 3083747450105631346840151)
              ·
                refine ⟨4625621175158447020260227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3083747450105631346840151 4625621175158447020260227)
                ·
                  refine ⟨6938431762737670530390341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4625621175158447020260227 6938431762737670530390341)
                  ·
                    refine ⟨1300955955513313224448189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6938431762737670530390341 1300955955513313224448189)
                    ·
                      refine ⟨487858483317492459168071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1300955955513313224448189 487858483317492459168071)
                      ·
                        rfl

theorem cell23_950101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_950101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950101 prefixEnd_950101 := by exact prefixLift 950101
  have htrace : WordTrace (prefixWord ++ tailWord_950101) baseStart_950101 baseEnd_950101 := by
    simpa [prefixWord, tailWord_950101, baseEnd_950101] using wordTrace_append hprefix tailTrace_950101
  have hstable : (prefixWord ++ tailWord_950101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950101).length < 2 ^ (prefixWord ++ tailWord_950101).sum := by decide
  have hdescent : baseEnd_950101 < baseStart_950101 := by decide
  rcases family_descends (prefixWord ++ tailWord_950101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950124 : List Nat := [2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 6]
def baseStart_950124 : Nat := 118140960795 + 950124 * 2 ^ 59
def prefixEnd_950124 : Nat := 4983230072969 + 3 ^ 40 * 950124 * 2
def baseEnd_950124 : Nat := 487870293372545869180465

theorem tailTrace_950124 : CollatzResearch.WordTrace tailWord_950124 prefixEnd_950124 487870293372545869180465 := by
  unfold tailWord_950124
  simp only [CollatzResearch.WordTrace]
  refine ⟨17326934604935245552736713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23102579473246994070315617 17326934604935245552736713)
  ·
    refine ⟨12995200953701434164552535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17326934604935245552736713 12995200953701434164552535)
    ·
      refine ⟨19492801430552151246828803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12995200953701434164552535 19492801430552151246828803)
      ·
        refine ⟨29239202145828226870243205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19492801430552151246828803 29239202145828226870243205)
        ·
          refine ⟨5482350402342792538170601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29239202145828226870243205 5482350402342792538170601)
          ·
            refine ⟨4111762801757094403627951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5482350402342792538170601 4111762801757094403627951)
            ·
              refine ⟨6167644202635641605441927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4111762801757094403627951 6167644202635641605441927)
              ·
                refine ⟨9251466303953462408162891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6167644202635641605441927 9251466303953462408162891)
                ·
                  refine ⟨13877199455930193612244337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9251466303953462408162891 13877199455930193612244337)
                  ·
                    refine ⟨10407899591947645209183253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13877199455930193612244337 10407899591947645209183253)
                    ·
                      refine ⟨487870293372545869180465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10407899591947645209183253 487870293372545869180465)
                      ·
                        rfl

theorem cell23_950124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_950124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950124 prefixEnd_950124 := by exact prefixLift 950124
  have htrace : WordTrace (prefixWord ++ tailWord_950124) baseStart_950124 baseEnd_950124 := by
    simpa [prefixWord, tailWord_950124, baseEnd_950124] using wordTrace_append hprefix tailTrace_950124
  have hstable : (prefixWord ++ tailWord_950124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950124).length < 2 ^ (prefixWord ++ tailWord_950124).sum := by decide
  have hdescent : baseEnd_950124 < baseStart_950124 := by decide
  rcases family_descends (prefixWord ++ tailWord_950124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950148 : List Nat := [2, 3, 2, 1, 1, 1, 4, 2, 3, 1, 3]
def baseStart_950148 : Nat := 118140960795 + 950148 * 2 ^ 59
def prefixEnd_950148 : Nat := 4983230072969 + 3 ^ 40 * 950148 * 2
def baseEnd_950148 : Nat := 487882616908253775280355

theorem tailTrace_950148 : CollatzResearch.WordTrace tailWord_950148 prefixEnd_950148 487882616908253775280355 := by
  unfold tailWord_950148
  simp only [CollatzResearch.WordTrace]
  refine ⟨17327372280891771602173549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23103163041189028802898065 17327372280891771602173549)
  ·
    refine ⟨6497764605334414350815081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17327372280891771602173549 6497764605334414350815081)
    ·
      refine ⟨4873323454000810763111311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6497764605334414350815081 4873323454000810763111311)
      ·
        refine ⟨7309985181001216144666967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4873323454000810763111311 7309985181001216144666967)
        ·
          refine ⟨10964977771501824217000451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7309985181001216144666967 10964977771501824217000451)
          ·
            refine ⟨16447466657252736325500677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10964977771501824217000451 16447466657252736325500677)
            ·
              refine ⟨3083899998234888061031377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16447466657252736325500677 3083899998234888061031377)
              ·
                refine ⟨2312924998676166045773533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3083899998234888061031377 2312924998676166045773533)
                ·
                  refine ⟨867346874503562267165075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2312924998676166045773533 867346874503562267165075)
                  ·
                    refine ⟨1301020311755343400747613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 867346874503562267165075 1301020311755343400747613)
                    ·
                      refine ⟨487882616908253775280355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1301020311755343400747613 487882616908253775280355)
                      ·
                        rfl

theorem cell23_950148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_950148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950148 prefixEnd_950148 := by exact prefixLift 950148
  have htrace : WordTrace (prefixWord ++ tailWord_950148) baseStart_950148 baseEnd_950148 := by
    simpa [prefixWord, tailWord_950148, baseEnd_950148] using wordTrace_append hprefix tailTrace_950148
  have hstable : (prefixWord ++ tailWord_950148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950148).length < 2 ^ (prefixWord ++ tailWord_950148).sum := by decide
  have hdescent : baseEnd_950148 < baseStart_950148 := by decide
  rcases family_descends (prefixWord ++ tailWord_950148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950175 : List Nat := [1, 1, 2, 5, 3, 1, 1, 2, 2, 3, 2]
def baseStart_950175 : Nat := 118140960795 + 950175 * 2 ^ 59
def prefixEnd_950175 : Nat := 4983230072969 + 3 ^ 40 * 950175 * 2
def baseEnd_950175 : Nat := 487896480885925169642731

theorem tailTrace_950175 : CollatzResearch.WordTrace tailWord_950175 prefixEnd_950175 487896480885925169642731 := by
  unfold tailWord_950175
  simp only [CollatzResearch.WordTrace]
  refine ⟨34655729332685726815579979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23103819555123817877053319 34655729332685726815579979)
  ·
    refine ⟨51983593999028590223369969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34655729332685726815579979 51983593999028590223369969)
    ·
      refine ⟨38987695499271442667527477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51983593999028590223369969 38987695499271442667527477)
      ·
        refine ⟨3655096453056697750080701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38987695499271442667527477 3655096453056697750080701)
        ·
          refine ⟨1370661169896261656280263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3655096453056697750080701 1370661169896261656280263)
          ·
            refine ⟨2055991754844392484420395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1370661169896261656280263 2055991754844392484420395)
            ·
              refine ⟨3083987632266588726630593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2055991754844392484420395 3083987632266588726630593)
              ·
                refine ⟨2312990724199941544972945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3083987632266588726630593 2312990724199941544972945)
                ·
                  refine ⟨1734743043149956158729709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2312990724199941544972945 1734743043149956158729709)
                  ·
                    refine ⟨650528641181233559523641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1734743043149956158729709 650528641181233559523641)
                    ·
                      refine ⟨487896480885925169642731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 650528641181233559523641 487896480885925169642731)
                      ·
                        rfl

theorem cell23_950175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_950175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950175 prefixEnd_950175 := by exact prefixLift 950175
  have htrace : WordTrace (prefixWord ++ tailWord_950175) baseStart_950175 baseEnd_950175 := by
    simpa [prefixWord, tailWord_950175, baseEnd_950175] using wordTrace_append hprefix tailTrace_950175
  have hstable : (prefixWord ++ tailWord_950175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950175).length < 2 ^ (prefixWord ++ tailWord_950175).sum := by decide
  have hdescent : baseEnd_950175 < baseStart_950175 := by decide
  rcases family_descends (prefixWord ++ tailWord_950175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950191 : List Nat := [1, 1, 2, 1, 2, 2, 4, 2, 3, 2, 3]
def baseStart_950191 : Nat := 118140960795 + 950191 * 2 ^ 59
def prefixEnd_950191 : Nat := 4983230072969 + 3 ^ 40 * 950191 * 2
def baseEnd_950191 : Nat := 487904696576397107042657

theorem tailTrace_950191 : CollatzResearch.WordTrace tailWord_950191 prefixEnd_950191 487904696576397107042657 := by
  unfold tailWord_950191
  simp only [CollatzResearch.WordTrace]
  refine ⟨34656312900627761548162427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23104208600418507698774951 34656312900627761548162427)
  ·
    refine ⟨51984469350941642322243641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34656312900627761548162427 51984469350941642322243641)
    ·
      refine ⟨38988352013206231741682731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51984469350941642322243641 38988352013206231741682731)
      ·
        refine ⟨58482528019809347612524097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38988352013206231741682731 58482528019809347612524097)
        ·
          refine ⟨43861896014857010709393073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58482528019809347612524097 43861896014857010709393073)
          ·
            refine ⟨32896422011142758032044805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43861896014857010709393073 32896422011142758032044805)
            ·
              refine ⟨6168079127089267131008401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32896422011142758032044805 6168079127089267131008401)
              ·
                refine ⟨4626059345316950348256301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6168079127089267131008401 4626059345316950348256301)
                ·
                  refine ⟨1734772254493856380596113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4626059345316950348256301 1734772254493856380596113)
                  ·
                    refine ⟨1301079190870392285447085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1734772254493856380596113 1301079190870392285447085)
                    ·
                      refine ⟨487904696576397107042657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1301079190870392285447085 487904696576397107042657)
                      ·
                        rfl

theorem cell23_950191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 2, 3].length) (baseStart_950191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950191 prefixEnd_950191 := by exact prefixLift 950191
  have htrace : WordTrace (prefixWord ++ tailWord_950191) baseStart_950191 baseEnd_950191 := by
    simpa [prefixWord, tailWord_950191, baseEnd_950191] using wordTrace_append hprefix tailTrace_950191
  have hstable : (prefixWord ++ tailWord_950191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950191).length < 2 ^ (prefixWord ++ tailWord_950191).sum := by decide
  have hdescent : baseEnd_950191 < baseStart_950191 := by decide
  rcases family_descends (prefixWord ++ tailWord_950191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950201 : List Nat := [1, 2, 1, 4, 2, 1, 2, 3, 1, 2, 4]
def baseStart_950201 : Nat := 118140960795 + 950201 * 2 ^ 59
def prefixEnd_950201 : Nat := 4983230072969 + 3 ^ 40 * 950201 * 2
def baseEnd_950201 : Nat := 487909831382942067917611

theorem tailTrace_950201 : CollatzResearch.WordTrace tailWord_950201 prefixEnd_950201 487909831382942067917611 := by
  unfold tailWord_950201
  simp only [CollatzResearch.WordTrace]
  refine ⟨34656677630591533256026457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23104451753727688837350971 34656677630591533256026457)
  ·
    refine ⟨25992508222943649942019843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34656677630591533256026457 25992508222943649942019843)
    ·
      refine ⟨38988762334415474913029765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25992508222943649942019843 38988762334415474913029765)
      ·
        refine ⟨7310392937702901546193081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38988762334415474913029765 7310392937702901546193081)
        ·
          refine ⟨5482794703277176159644811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7310392937702901546193081 5482794703277176159644811)
          ·
            refine ⟨8224192054915764239467217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5482794703277176159644811 8224192054915764239467217)
            ·
              refine ⟨6168144041186823179600413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8224192054915764239467217 6168144041186823179600413)
              ·
                refine ⟨2313054015445058692350155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6168144041186823179600413 2313054015445058692350155)
                ·
                  refine ⟨3469581023167588038525233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2313054015445058692350155 3469581023167588038525233)
                  ·
                    refine ⟨2602185767375691028893925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3469581023167588038525233 2602185767375691028893925)
                    ·
                      refine ⟨487909831382942067917611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2602185767375691028893925 487909831382942067917611)
                      ·
                        rfl

theorem cell23_950201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_950201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950201 prefixEnd_950201 := by exact prefixLift 950201
  have htrace : WordTrace (prefixWord ++ tailWord_950201) baseStart_950201 baseEnd_950201 := by
    simpa [prefixWord, tailWord_950201, baseEnd_950201] using wordTrace_append hprefix tailTrace_950201
  have hstable : (prefixWord ++ tailWord_950201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950201).length < 2 ^ (prefixWord ++ tailWord_950201).sum := by decide
  have hdescent : baseEnd_950201 < baseStart_950201 := by decide
  rcases family_descends (prefixWord ++ tailWord_950201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950205 : List Nat := [1, 4, 1, 2, 3, 3, 1, 2, 1, 1, 4]
def baseStart_950205 : Nat := 118140960795 + 950205 * 2 ^ 59
def prefixEnd_950205 : Nat := 4983230072969 + 3 ^ 40 * 950205 * 2
def baseEnd_950205 : Nat := 487911885305560052267593

theorem tailTrace_950205 : CollatzResearch.WordTrace tailWord_950205 prefixEnd_950205 487911885305560052267593 := by
  unfold tailWord_950205
  simp only [CollatzResearch.WordTrace]
  refine ⟨34656823522577041939172069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23104549015051361292781379 34656823522577041939172069)
  ·
    refine ⟨6498154410483195363594763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34656823522577041939172069 6498154410483195363594763)
    ·
      refine ⟨9747231615724793045392145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6498154410483195363594763 9747231615724793045392145)
      ·
        refine ⟨7310423711793594784044109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9747231615724793045392145 7310423711793594784044109)
        ·
          refine ⟨2741408891922598044016541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7310423711793594784044109 2741408891922598044016541)
          ·
            refine ⟨1028028334470974266506203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2741408891922598044016541 1028028334470974266506203)
            ·
              refine ⟨1542042501706461399759305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1028028334470974266506203 1542042501706461399759305)
              ·
                refine ⟨1156531876279846049819479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1542042501706461399759305 1156531876279846049819479)
                ·
                  refine ⟨1734797814419769074729219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1156531876279846049819479 1734797814419769074729219)
                  ·
                    refine ⟨2602196721629653612093829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1734797814419769074729219 2602196721629653612093829)
                    ·
                      refine ⟨487911885305560052267593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2602196721629653612093829 487911885305560052267593)
                      ·
                        rfl

theorem cell23_950205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_950205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950205 prefixEnd_950205 := by exact prefixLift 950205
  have htrace : WordTrace (prefixWord ++ tailWord_950205) baseStart_950205 baseEnd_950205 := by
    simpa [prefixWord, tailWord_950205, baseEnd_950205] using wordTrace_append hprefix tailTrace_950205
  have hstable : (prefixWord ++ tailWord_950205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950205).length < 2 ^ (prefixWord ++ tailWord_950205).sum := by decide
  have hdescent : baseEnd_950205 < baseStart_950205 := by decide
  rcases family_descends (prefixWord ++ tailWord_950205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950222 : List Nat := [4, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2]
def baseStart_950222 : Nat := 118140960795 + 950222 * 2 ^ 59
def prefixEnd_950222 : Nat := 4983230072969 + 3 ^ 40 * 950222 * 2
def baseEnd_950222 : Nat := 487920614476686485755015

theorem tailTrace_950222 : CollatzResearch.WordTrace tailWord_950222 prefixEnd_950222 487920614476686485755015 := by
  unfold tailWord_950222
  simp only [CollatzResearch.WordTrace]
  refine ⟨4332180445439431730317615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23104962375676969228360613 4332180445439431730317615)
  ·
    refine ⟨6498270668159147595476423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4332180445439431730317615 6498270668159147595476423)
    ·
      refine ⟨9747406002238721393214635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6498270668159147595476423 9747406002238721393214635)
      ·
        refine ⟨14621109003358082089821953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9747406002238721393214635 14621109003358082089821953)
        ·
          refine ⟨10965831752518561567366465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14621109003358082089821953 10965831752518561567366465)
          ·
            refine ⟨8224373814388921175524849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10965831752518561567366465 8224373814388921175524849)
            ·
              refine ⟨6168280360791690881643637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8224373814388921175524849 6168280360791690881643637)
              ·
                refine ⟨578276283824221020154091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6168280360791690881643637 578276283824221020154091)
                ·
                  refine ⟨867414425736331530231137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 578276283824221020154091 867414425736331530231137)
                  ·
                    refine ⟨650560819302248647673353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 867414425736331530231137 650560819302248647673353)
                    ·
                      refine ⟨487920614476686485755015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 650560819302248647673353 487920614476686485755015)
                      ·
                        rfl

theorem cell23_950222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2].length) (baseStart_950222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950222 prefixEnd_950222 := by exact prefixLift 950222
  have htrace : WordTrace (prefixWord ++ tailWord_950222) baseStart_950222 baseEnd_950222 := by
    simpa [prefixWord, tailWord_950222, baseEnd_950222] using wordTrace_append hprefix tailTrace_950222
  have hstable : (prefixWord ++ tailWord_950222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950222).length < 2 ^ (prefixWord ++ tailWord_950222).sum := by decide
  have hdescent : baseEnd_950222 < baseStart_950222 := by decide
  rcases family_descends (prefixWord ++ tailWord_950222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950239 : List Nat := [1, 1, 2, 3, 4, 1, 4, 2, 1, 2, 2]
def baseStart_950239 : Nat := 118140960795 + 950239 * 2 ^ 59
def prefixEnd_950239 : Nat := 4983230072969 + 3 ^ 40 * 950239 * 2
def baseEnd_950239 : Nat := 487929343647812919242437

theorem tailTrace_950239 : CollatzResearch.WordTrace tailWord_950239 prefixEnd_950239 487929343647812919242437 := by
  unfold tailWord_950239
  simp only [CollatzResearch.WordTrace]
  refine ⟨34658063604453865745909771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23105375736302577163939847 34658063604453865745909771)
  ·
    refine ⟨51987095406680798618864657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34658063604453865745909771 51987095406680798618864657)
    ·
      refine ⟨38990321555010598964148493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51987095406680798618864657 38990321555010598964148493)
      ·
        refine ⟨14621370583128974611555685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38990321555010598964148493 14621370583128974611555685)
        ·
          refine ⟨2741506984336682739666691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14621370583128974611555685 2741506984336682739666691)
          ·
            refine ⟨4112260476505024109500037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2741506984336682739666691 4112260476505024109500037)
            ·
              refine ⟨771048839344692020531257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4112260476505024109500037 771048839344692020531257)
              ·
                refine ⟨578286629508519015398443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 771048839344692020531257 578286629508519015398443)
                ·
                  refine ⟨867429944262778523097665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 578286629508519015398443 867429944262778523097665)
                  ·
                    refine ⟨650572458197083892323249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 867429944262778523097665 650572458197083892323249)
                    ·
                      refine ⟨487929343647812919242437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 650572458197083892323249 487929343647812919242437)
                      ·
                        rfl

theorem cell23_950239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 2, 1, 2, 2].length) (baseStart_950239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950239 prefixEnd_950239 := by exact prefixLift 950239
  have htrace : WordTrace (prefixWord ++ tailWord_950239) baseStart_950239 baseEnd_950239 := by
    simpa [prefixWord, tailWord_950239, baseEnd_950239] using wordTrace_append hprefix tailTrace_950239
  have hstable : (prefixWord ++ tailWord_950239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950239).length < 2 ^ (prefixWord ++ tailWord_950239).sum := by decide
  have hdescent : baseEnd_950239 < baseStart_950239 := by decide
  rcases family_descends (prefixWord ++ tailWord_950239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950276 : List Nat := [2, 3, 2, 4, 2, 1, 2, 1, 1, 2, 3]
def baseStart_950276 : Nat := 118140960795 + 950276 * 2 ^ 59
def prefixEnd_950276 : Nat := 4983230072969 + 3 ^ 40 * 950276 * 2
def baseEnd_950276 : Nat := 487948342432029274479767

theorem tailTrace_950276 : CollatzResearch.WordTrace tailWord_950276 prefixEnd_950276 487948342432029274479767 := by
  unfold tailWord_950276
  simp only [CollatzResearch.WordTrace]
  refine ⟨17329706552659910532503341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23106275403546547376671121 17329706552659910532503341)
  ·
    refine ⟨6498639957247466449688753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17329706552659910532503341 6498639957247466449688753)
    ·
      refine ⟨4873979967935599837266565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6498639957247466449688753 4873979967935599837266565)
      ·
        refine ⟨913871243987924969487481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4873979967935599837266565 913871243987924969487481)
        ·
          refine ⟨685403432990943727115611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 913871243987924969487481 685403432990943727115611)
          ·
            refine ⟨1028105149486415590673417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685403432990943727115611 1028105149486415590673417)
            ·
              refine ⟨771078862114811693005063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1028105149486415590673417 771078862114811693005063)
              ·
                refine ⟨1156618293172217539507595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 771078862114811693005063 1156618293172217539507595)
                ·
                  refine ⟨1734927439758326309261393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1156618293172217539507595 1734927439758326309261393)
                  ·
                    refine ⟨1301195579818744731946045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1734927439758326309261393 1301195579818744731946045)
                    ·
                      refine ⟨487948342432029274479767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1301195579818744731946045 487948342432029274479767)
                      ·
                        rfl

theorem cell23_950276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_950276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950276 prefixEnd_950276 := by exact prefixLift 950276
  have htrace : WordTrace (prefixWord ++ tailWord_950276) baseStart_950276 baseEnd_950276 := by
    simpa [prefixWord, tailWord_950276, baseEnd_950276] using wordTrace_append hprefix tailTrace_950276
  have hstable : (prefixWord ++ tailWord_950276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950276).length < 2 ^ (prefixWord ++ tailWord_950276).sum := by decide
  have hdescent : baseEnd_950276 < baseStart_950276 := by decide
  rcases family_descends (prefixWord ++ tailWord_950276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950282 : List Nat := [3, 1, 2, 2, 4, 1, 1, 3, 1, 3, 2]
def baseStart_950282 : Nat := 118140960795 + 950282 * 2 ^ 59
def prefixEnd_950282 : Nat := 4983230072969 + 3 ^ 40 * 950282 * 2
def baseEnd_950282 : Nat := 487951423315956251004739

theorem tailTrace_950282 : CollatzResearch.WordTrace tailWord_950282 prefixEnd_950282 487951423315956251004739 := by
  unfold tailWord_950282
  simp only [CollatzResearch.WordTrace]
  refine ⟨8664907985824521022431275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23106421295532056059816733 8664907985824521022431275)
  ·
    refine ⟨12997361978736781533646913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8664907985824521022431275 12997361978736781533646913)
    ·
      refine ⟨9748021484052586150235185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12997361978736781533646913 9748021484052586150235185)
      ·
        refine ⟨7311016113039439612676389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9748021484052586150235185 7311016113039439612676389)
        ·
          refine ⟨1370815521194894927376823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7311016113039439612676389 1370815521194894927376823)
          ·
            refine ⟨2056223281792342391065235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1370815521194894927376823 2056223281792342391065235)
            ·
              refine ⟨3084334922688513586597853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2056223281792342391065235 3084334922688513586597853)
              ·
                refine ⟨1156625596008192594974195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3084334922688513586597853 1156625596008192594974195)
                ·
                  refine ⟨1734938394012288892461293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1156625596008192594974195 1734938394012288892461293)
                  ·
                    refine ⟨650601897754608334672985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1734938394012288892461293 650601897754608334672985)
                    ·
                      refine ⟨487951423315956251004739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 650601897754608334672985 487951423315956251004739)
                      ·
                        rfl

theorem cell23_950282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_950282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950282 prefixEnd_950282 := by exact prefixLift 950282
  have htrace : WordTrace (prefixWord ++ tailWord_950282) baseStart_950282 baseEnd_950282 := by
    simpa [prefixWord, tailWord_950282, baseEnd_950282] using wordTrace_append hprefix tailTrace_950282
  have hstable : (prefixWord ++ tailWord_950282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950282).length < 2 ^ (prefixWord ++ tailWord_950282).sum := by decide
  have hdescent : baseEnd_950282 < baseStart_950282 := by decide
  rcases family_descends (prefixWord ++ tailWord_950282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950291 : List Nat := [1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 4]
def baseStart_950291 : Nat := 118140960795 + 950291 * 2 ^ 59
def prefixEnd_950291 : Nat := 4983230072969 + 3 ^ 40 * 950291 * 2
def baseEnd_950291 : Nat := 487956044641846715792197

theorem tailTrace_950291 : CollatzResearch.WordTrace tailWord_950291 prefixEnd_950291 487956044641846715792197 := by
  unfold tailWord_950291
  simp only [CollatzResearch.WordTrace]
  refine ⟨34659960200265478626802727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23106640133510319084535151 34659960200265478626802727)
  ·
    refine ⟨51989940300398217940204091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34659960200265478626802727 51989940300398217940204091)
    ·
      refine ⟨77984910450597326910306137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51989940300398217940204091 77984910450597326910306137)
      ·
        refine ⟨58488682837947995182729603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77984910450597326910306137 58488682837947995182729603)
        ·
          refine ⟨87733024256921992774094405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58488682837947995182729603 87733024256921992774094405)
          ·
            refine ⟨16449942048172873645142701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87733024256921992774094405 16449942048172873645142701)
            ·
              refine ⟨6168728268064827616928513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16449942048172873645142701 6168728268064827616928513)
              ·
                refine ⟨4626546201048620712696385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6168728268064827616928513 4626546201048620712696385)
                ·
                  refine ⟨3469909650786465534522289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4626546201048620712696385 3469909650786465534522289)
                  ·
                    refine ⟨2602432238089849150891717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3469909650786465534522289 2602432238089849150891717)
                    ·
                      refine ⟨487956044641846715792197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2602432238089849150891717 487956044641846715792197)
                      ·
                        rfl

theorem cell23_950291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 4].length) (baseStart_950291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950291 prefixEnd_950291 := by exact prefixLift 950291
  have htrace : WordTrace (prefixWord ++ tailWord_950291) baseStart_950291 baseEnd_950291 := by
    simpa [prefixWord, tailWord_950291, baseEnd_950291] using wordTrace_append hprefix tailTrace_950291
  have hstable : (prefixWord ++ tailWord_950291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950291).length < 2 ^ (prefixWord ++ tailWord_950291).sum := by decide
  have hdescent : baseEnd_950291 < baseStart_950291 := by decide
  rcases family_descends (prefixWord ++ tailWord_950291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950318 : List Nat := [4, 1, 3, 1, 1, 2, 2, 2, 7]
def baseStart_950318 : Nat := 118140960795 + 950318 * 2 ^ 59
def prefixEnd_950318 : Nat := 4983230072969 + 3 ^ 40 * 950318 * 2
def baseEnd_950318 : Nat := 54218878735502012239397

theorem tailTrace_950318 : CollatzResearch.WordTrace tailWord_950318 prefixEnd_950318 54218878735502012239397 := by
  unfold tailWord_950318
  simp only [CollatzResearch.WordTrace]
  refine ⟨4332618121395957779754451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23107296647445108158690405 4332618121395957779754451)
  ·
    refine ⟨6498927182093936669631677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4332618121395957779754451 6498927182093936669631677)
    ·
      refine ⟨2437097693285226251111879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6498927182093936669631677 2437097693285226251111879)
      ·
        refine ⟨3655646539927839376667819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2437097693285226251111879 3655646539927839376667819)
        ·
          refine ⟨5483469809891759065001729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3655646539927839376667819 5483469809891759065001729)
          ·
            refine ⟨4112602357418819298751297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5483469809891759065001729 4112602357418819298751297)
            ·
              refine ⟨3084451768064114474063473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4112602357418819298751297 3084451768064114474063473)
              ·
                refine ⟨2313338826048085855547605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3084451768064114474063473 2313338826048085855547605)
                ·
                  refine ⟨54218878735502012239397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2313338826048085855547605 54218878735502012239397)
                  ·
                    rfl

theorem cell23_950318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 7].length) (baseStart_950318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950318 prefixEnd_950318 := by exact prefixLift 950318
  have htrace : WordTrace (prefixWord ++ tailWord_950318) baseStart_950318 baseEnd_950318 := by
    simpa [prefixWord, tailWord_950318, baseEnd_950318] using wordTrace_append hprefix tailTrace_950318
  have hstable : (prefixWord ++ tailWord_950318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950318).length < 2 ^ (prefixWord ++ tailWord_950318).sum := by decide
  have hdescent : baseEnd_950318 < baseStart_950318 := by decide
  rcases family_descends (prefixWord ++ tailWord_950318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950341 : List Nat := [1, 3, 1, 1, 1, 3, 1, 4, 1, 2, 5]
def baseStart_950341 : Nat := 118140960795 + 950341 * 2 ^ 59
def prefixEnd_950341 : Nat := 4983230072969 + 3 ^ 40 * 950341 * 2
def baseEnd_950341 : Nat := 487981718674571520166967

theorem tailTrace_950341 : CollatzResearch.WordTrace tailWord_950341 prefixEnd_950341 487981718674571520166967 := by
  unfold tailWord_950341
  simp only [CollatzResearch.WordTrace]
  refine ⟨34661783850084337166122877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23107855900056224777415251 34661783850084337166122877)
  ·
    refine ⟨12998168943781626437296079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34661783850084337166122877 12998168943781626437296079)
    ·
      refine ⟨19497253415672439655944119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12998168943781626437296079 19497253415672439655944119)
      ·
        refine ⟨29245880123508659483916179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19497253415672439655944119 29245880123508659483916179)
        ·
          refine ⟨43868820185262989225874269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29245880123508659483916179 43868820185262989225874269)
          ·
            refine ⟨16450807569473620959702851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43868820185262989225874269 16450807569473620959702851)
            ·
              refine ⟨24676211354210431439554277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16450807569473620959702851 24676211354210431439554277)
              ·
                refine ⟨4626789628914455894916427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24676211354210431439554277 4626789628914455894916427)
                ·
                  refine ⟨6940184443371683842374641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4626789628914455894916427 6940184443371683842374641)
                  ·
                    refine ⟨5205138332528762881780981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6940184443371683842374641 5205138332528762881780981)
                    ·
                      refine ⟨487981718674571520166967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5205138332528762881780981 487981718674571520166967)
                      ·
                        rfl

theorem cell23_950341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_950341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950341 prefixEnd_950341 := by exact prefixLift 950341
  have htrace : WordTrace (prefixWord ++ tailWord_950341) baseStart_950341 baseEnd_950341 := by
    simpa [prefixWord, tailWord_950341, baseEnd_950341] using wordTrace_append hprefix tailTrace_950341
  have hstable : (prefixWord ++ tailWord_950341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950341).length < 2 ^ (prefixWord ++ tailWord_950341).sum := by decide
  have hdescent : baseEnd_950341 < baseStart_950341 := by decide
  rcases family_descends (prefixWord ++ tailWord_950341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950405 : List Nat := [1, 3, 1, 1, 5, 1, 2, 2, 2, 2, 3]
def baseStart_950405 : Nat := 118140960795 + 950405 * 2 ^ 59
def prefixEnd_950405 : Nat := 4983230072969 + 3 ^ 40 * 950405 * 2
def baseEnd_950405 : Nat := 488014581436459269766673

theorem tailTrace_950405 : CollatzResearch.WordTrace tailWord_950405 prefixEnd_950405 488014581436459269766673 := by
  unfold tailWord_950405
  simp only [CollatzResearch.WordTrace]
  refine ⟨34664118121852476096452669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23109412081234984064301779 34664118121852476096452669)
  ·
    refine ⟨12999044295694678536169751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34664118121852476096452669 12999044295694678536169751)
    ·
      refine ⟨19498566443542017804254627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12999044295694678536169751 19498566443542017804254627)
      ·
        refine ⟨29247849665313026706381941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19498566443542017804254627 29247849665313026706381941)
        ·
          refine ⟨2741985906123096253723307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29247849665313026706381941 2741985906123096253723307)
          ·
            refine ⟨4112978859184644380584961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2741985906123096253723307 4112978859184644380584961)
            ·
              refine ⟨3084734144388483285438721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4112978859184644380584961 3084734144388483285438721)
              ·
                refine ⟨2313550608291362464079041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3084734144388483285438721 2313550608291362464079041)
                ·
                  refine ⟨1735162956218521848059281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2313550608291362464079041 1735162956218521848059281)
                  ·
                    refine ⟨1301372217163891386044461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1735162956218521848059281 1301372217163891386044461)
                    ·
                      refine ⟨488014581436459269766673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1301372217163891386044461 488014581436459269766673)
                      ·
                        rfl

theorem cell23_950405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 2, 3].length) (baseStart_950405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950405 prefixEnd_950405 := by exact prefixLift 950405
  have htrace : WordTrace (prefixWord ++ tailWord_950405) baseStart_950405 baseEnd_950405 := by
    simpa [prefixWord, tailWord_950405, baseEnd_950405] using wordTrace_append hprefix tailTrace_950405
  have hstable : (prefixWord ++ tailWord_950405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950405).length < 2 ^ (prefixWord ++ tailWord_950405).sum := by decide
  have hdescent : baseEnd_950405 < baseStart_950405 := by decide
  rcases family_descends (prefixWord ++ tailWord_950405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950439 : List Nat := [1, 1, 6, 2, 2, 2, 1, 1, 2, 2, 3]
def baseStart_950439 : Nat := 118140960795 + 950439 * 2 ^ 59
def prefixEnd_950439 : Nat := 4983230072969 + 3 ^ 40 * 950439 * 2
def baseEnd_950439 : Nat := 488032039778712136741517

theorem tailTrace_950439 : CollatzResearch.WordTrace tailWord_950439 prefixEnd_950439 488032039778712136741517 := by
  unfold tailWord_950439
  simp only [CollatzResearch.WordTrace]
  refine ⟨34665358203729299903190371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23110238802486199935460247 34665358203729299903190371)
  ·
    refine ⟨51998037305593949854785557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34665358203729299903190371 51998037305593949854785557)
    ·
      refine ⟨2437407998699716399443073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51998037305593949854785557 2437407998699716399443073)
      ·
        refine ⟨1828055999024787299582305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2437407998699716399443073 1828055999024787299582305)
        ·
          refine ⟨1371041999268590474686729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1828055999024787299582305 1371041999268590474686729)
          ·
            refine ⟨1028281499451442856015047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1371041999268590474686729 1028281499451442856015047)
            ·
              refine ⟨1542422249177164284022571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1028281499451442856015047 1542422249177164284022571)
              ·
                refine ⟨2313633373765746426033857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1542422249177164284022571 2313633373765746426033857)
                ·
                  refine ⟨1735225030324309819525393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2313633373765746426033857 1735225030324309819525393)
                  ·
                    refine ⟨1301418772743232364644045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1735225030324309819525393 1301418772743232364644045)
                    ·
                      refine ⟨488032039778712136741517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1301418772743232364644045 488032039778712136741517)
                      ·
                        rfl

theorem cell23_950439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_950439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950439 prefixEnd_950439 := by exact prefixLift 950439
  have htrace : WordTrace (prefixWord ++ tailWord_950439) baseStart_950439 baseEnd_950439 := by
    simpa [prefixWord, tailWord_950439, baseEnd_950439] using wordTrace_append hprefix tailTrace_950439
  have hstable : (prefixWord ++ tailWord_950439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950439).length < 2 ^ (prefixWord ++ tailWord_950439).sum := by decide
  have hdescent : baseEnd_950439 < baseStart_950439 := by decide
  rcases family_descends (prefixWord ++ tailWord_950439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950455 : List Nat := [1, 1, 3, 1, 4, 3, 1, 3, 1, 5]
def baseStart_950455 : Nat := 118140960795 + 950455 * 2 ^ 59
def prefixEnd_950455 : Nat := 4983230072969 + 3 ^ 40 * 950455 * 2
def baseEnd_950455 : Nat := 162680085156394691380481

theorem tailTrace_950455 : CollatzResearch.WordTrace tailWord_950455 prefixEnd_950455 162680085156394691380481 := by
  unfold tailWord_950455
  simp only [CollatzResearch.WordTrace]
  refine ⟨34665941771671334635772819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23110627847780889757181879 34665941771671334635772819)
  ·
    refine ⟨51998912657507001953659229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34665941771671334635772819 51998912657507001953659229)
    ·
      refine ⟨19499592246565125732622211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51998912657507001953659229 19499592246565125732622211)
      ·
        refine ⟨29249388369847688598933317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19499592246565125732622211 29249388369847688598933317)
        ·
          refine ⟨5484260319346441612299997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29249388369847688598933317 5484260319346441612299997)
          ·
            refine ⟨2056597619754915604612499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5484260319346441612299997 2056597619754915604612499)
            ·
              refine ⟨3084896429632373406918749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2056597619754915604612499 3084896429632373406918749)
              ·
                refine ⟨1156836161112140027594531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3084896429632373406918749 1156836161112140027594531)
                ·
                  refine ⟨1735254241668210041391797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1156836161112140027594531 1735254241668210041391797)
                  ·
                    refine ⟨162680085156394691380481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1735254241668210041391797 162680085156394691380481)
                    ·
                      rfl

theorem cell23_950455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 5].length) (baseStart_950455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950455 prefixEnd_950455 := by exact prefixLift 950455
  have htrace : WordTrace (prefixWord ++ tailWord_950455) baseStart_950455 baseEnd_950455 := by
    simpa [prefixWord, tailWord_950455, baseEnd_950455] using wordTrace_append hprefix tailTrace_950455
  have hstable : (prefixWord ++ tailWord_950455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950455).length < 2 ^ (prefixWord ++ tailWord_950455).sum := by decide
  have hdescent : baseEnd_950455 < baseStart_950455 := by decide
  rcases family_descends (prefixWord ++ tailWord_950455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950552 : List Nat := [2, 1, 2, 3, 1, 2, 3, 1, 3, 3, 2]
def baseStart_950552 : Nat := 118140960795 + 950552 * 2 ^ 59
def prefixEnd_950552 : Nat := 4983230072969 + 3 ^ 40 * 950552 * 2
def baseEnd_950552 : Nat := 488090063092670194628497

theorem tailTrace_950552 : CollatzResearch.WordTrace tailWord_950552 prefixEnd_950552 488090063092670194628497 := by
  unfold tailWord_950552
  simp only [CollatzResearch.WordTrace]
  refine ⟨17334739826159960101026955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23112986434879946801369273 17334739826159960101026955)
  ·
    refine ⟨26002109739239940151540433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17334739826159960101026955 26002109739239940151540433)
    ·
      refine ⟨19501582304429955113655325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26002109739239940151540433 19501582304429955113655325)
      ·
        refine ⟨7313093364161233167620747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19501582304429955113655325 7313093364161233167620747)
        ·
          refine ⟨10969640046241849751431121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7313093364161233167620747 10969640046241849751431121)
          ·
            refine ⟨8227230034681387313573341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10969640046241849751431121 8227230034681387313573341)
            ·
              refine ⟨3085211263005520242590003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8227230034681387313573341 3085211263005520242590003)
              ·
                refine ⟨4627816894508280363885005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3085211263005520242590003 4627816894508280363885005)
                ·
                  refine ⟨1735431335440605136456877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4627816894508280363885005 1735431335440605136456877)
                  ·
                    refine ⟨650786750790226926171329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1735431335440605136456877 650786750790226926171329)
                    ·
                      refine ⟨488090063092670194628497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 650786750790226926171329 488090063092670194628497)
                      ·
                        rfl

theorem cell23_950552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_950552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950552 prefixEnd_950552 := by exact prefixLift 950552
  have htrace : WordTrace (prefixWord ++ tailWord_950552) baseStart_950552 baseEnd_950552 := by
    simpa [prefixWord, tailWord_950552, baseEnd_950552] using wordTrace_append hprefix tailTrace_950552
  have hstable : (prefixWord ++ tailWord_950552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950552).length < 2 ^ (prefixWord ++ tailWord_950552).sum := by decide
  have hdescent : baseEnd_950552 < baseStart_950552 := by decide
  rcases family_descends (prefixWord ++ tailWord_950552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950599 : List Nat := [1, 1, 4, 1, 2, 2, 1, 5, 2, 2, 2]
def baseStart_950599 : Nat := 118140960795 + 950599 * 2 ^ 59
def prefixEnd_950599 : Nat := 4983230072969 + 3 ^ 40 * 950599 * 2
def baseEnd_950599 : Nat := 488114196683431510740781

theorem tailTrace_950599 : CollatzResearch.WordTrace tailWord_950599 prefixEnd_950599 488114196683431510740781 := by
  unfold tailWord_950599
  simp only [CollatzResearch.WordTrace]
  refine ⟨34671193883149647229014851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23114129255433098152676567 34671193883149647229014851)
  ·
    refine ⟨52006790824724470843522277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34671193883149647229014851 52006790824724470843522277)
    ·
      refine ⟨9751273279635838283160427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52006790824724470843522277 9751273279635838283160427)
      ·
        refine ⟨14626909919453757424740641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9751273279635838283160427 14626909919453757424740641)
        ·
          refine ⟨10970182439590318068555481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14626909919453757424740641 10970182439590318068555481)
          ·
            refine ⟨8227636829692738551416611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10970182439590318068555481 8227636829692738551416611)
            ·
              refine ⟨12341455244539107827124917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8227636829692738551416611 12341455244539107827124917)
              ·
                refine ⟨1157011429175541358792961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12341455244539107827124917 1157011429175541358792961)
                ·
                  refine ⟨867758571881656019094721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1157011429175541358792961 867758571881656019094721)
                  ·
                    refine ⟨650818928911242014321041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 867758571881656019094721 650818928911242014321041)
                    ·
                      refine ⟨488114196683431510740781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 650818928911242014321041 488114196683431510740781)
                      ·
                        rfl

theorem cell23_950599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 2, 2, 2].length) (baseStart_950599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950599 prefixEnd_950599 := by exact prefixLift 950599
  have htrace : WordTrace (prefixWord ++ tailWord_950599) baseStart_950599 baseEnd_950599 := by
    simpa [prefixWord, tailWord_950599, baseEnd_950599] using wordTrace_append hprefix tailTrace_950599
  have hstable : (prefixWord ++ tailWord_950599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950599).length < 2 ^ (prefixWord ++ tailWord_950599).sum := by decide
  have hdescent : baseEnd_950599 < baseStart_950599 := by decide
  rcases family_descends (prefixWord ++ tailWord_950599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950615 : List Nat := [1, 1, 3, 2, 3, 1, 1, 2, 1, 5, 3]
def baseStart_950615 : Nat := 118140960795 + 950615 * 2 ^ 59
def prefixEnd_950615 : Nat := 4983230072969 + 3 ^ 40 * 950615 * 2
def baseEnd_950615 : Nat := 488122412373903448140707

theorem tailTrace_950615 : CollatzResearch.WordTrace tailWord_950615 prefixEnd_950615 488122412373903448140707 := by
  unfold tailWord_950615
  simp only [CollatzResearch.WordTrace]
  refine ⟨34671777451091681961597299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23114518300727787974398199 34671777451091681961597299)
  ·
    refine ⟨52007666176637522942395949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34671777451091681961597299 52007666176637522942395949)
    ·
      refine ⟨19502874816239071103398481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52007666176637522942395949 19502874816239071103398481)
      ·
        refine ⟨14627156112179303327548861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19502874816239071103398481 14627156112179303327548861)
        ·
          refine ⟨5485183542067238747830823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14627156112179303327548861 5485183542067238747830823)
          ·
            refine ⟨8227775313100858121746235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5485183542067238747830823 8227775313100858121746235)
            ·
              refine ⟨12341662969651287182619353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8227775313100858121746235 12341662969651287182619353)
              ·
                refine ⟨9256247227238465386964515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12341662969651287182619353 9256247227238465386964515)
                ·
                  refine ⟨13884370840857698080446773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9256247227238465386964515 13884370840857698080446773)
                  ·
                    refine ⟨1301659766330409195041885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13884370840857698080446773 1301659766330409195041885)
                    ·
                      refine ⟨488122412373903448140707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1301659766330409195041885 488122412373903448140707)
                      ·
                        rfl

theorem cell23_950615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_950615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950615 prefixEnd_950615 := by exact prefixLift 950615
  have htrace : WordTrace (prefixWord ++ tailWord_950615) baseStart_950615 baseEnd_950615 := by
    simpa [prefixWord, tailWord_950615, baseEnd_950615] using wordTrace_append hprefix tailTrace_950615
  have hstable : (prefixWord ++ tailWord_950615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950615).length < 2 ^ (prefixWord ++ tailWord_950615).sum := by decide
  have hdescent : baseEnd_950615 < baseStart_950615 := by decide
  rcases family_descends (prefixWord ++ tailWord_950615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950620 : List Nat := [2, 2, 4, 3, 1, 2, 2, 1, 1, 3, 2]
def baseStart_950620 : Nat := 118140960795 + 950620 * 2 ^ 59
def prefixEnd_950620 : Nat := 4983230072969 + 3 ^ 40 * 950620 * 2
def baseEnd_950620 : Nat := 488124979777175928578185

theorem tailTrace_950620 : CollatzResearch.WordTrace tailWord_950620 prefixEnd_950620 488124979777175928578185 := by
  unfold tailWord_950620
  simp only [CollatzResearch.WordTrace]
  refine ⟨17335979908036783907764657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23114639877382378543686209 17335979908036783907764657)
  ·
    refine ⟨13001984931027587930823493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17335979908036783907764657 13001984931027587930823493)
    ·
      refine ⟨2437872174567672737029405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13001984931027587930823493 2437872174567672737029405)
      ·
        refine ⟨914202065462877276386027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2437872174567672737029405 914202065462877276386027)
        ·
          refine ⟨1371303098194315914579041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 914202065462877276386027 1371303098194315914579041)
          ·
            refine ⟨1028477323645736935934281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1371303098194315914579041 1028477323645736935934281)
            ·
              refine ⟨771357992734302701950711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1028477323645736935934281 771357992734302701950711)
              ·
                refine ⟨1157036989101454052926067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 771357992734302701950711 1157036989101454052926067)
                ·
                  refine ⟨1735555483652181079389101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1157036989101454052926067 1735555483652181079389101)
                  ·
                    refine ⟨650833306369567904770913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1735555483652181079389101 650833306369567904770913)
                    ·
                      refine ⟨488124979777175928578185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 650833306369567904770913 488124979777175928578185)
                      ·
                        rfl

theorem cell23_950620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_950620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950620 prefixEnd_950620 := by exact prefixLift 950620
  have htrace : WordTrace (prefixWord ++ tailWord_950620) baseStart_950620 baseEnd_950620 := by
    simpa [prefixWord, tailWord_950620, baseEnd_950620] using wordTrace_append hprefix tailTrace_950620
  have hstable : (prefixWord ++ tailWord_950620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950620).length < 2 ^ (prefixWord ++ tailWord_950620).sum := by decide
  have hdescent : baseEnd_950620 < baseStart_950620 := by decide
  rcases family_descends (prefixWord ++ tailWord_950620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950632 : List Nat := [2, 1, 4, 2, 2, 1, 1, 2, 2, 3, 3]
def baseStart_950632 : Nat := 118140960795 + 950632 * 2 ^ 59
def prefixEnd_950632 : Nat := 4983230072969 + 3 ^ 40 * 950632 * 2
def baseEnd_950632 : Nat := 488131141545029881628129

theorem tailTrace_950632 : CollatzResearch.WordTrace tailWord_950632 prefixEnd_950632 488131141545029881628129 := by
  unfold tailWord_950632
  simp only [CollatzResearch.WordTrace]
  refine ⟨17336198746015046932483075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23114931661353395909977433 17336198746015046932483075)
  ·
    refine ⟨26004298119022570398724613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17336198746015046932483075 26004298119022570398724613)
    ·
      refine ⟨4875805897316731949760865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26004298119022570398724613 4875805897316731949760865)
      ·
        refine ⟨3656854422987548962320649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4875805897316731949760865 3656854422987548962320649)
        ·
          refine ⟨2742640817240661721740487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3656854422987548962320649 2742640817240661721740487)
          ·
            refine ⟨4113961225860992582610731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2742640817240661721740487 4113961225860992582610731)
            ·
              refine ⟨6170941838791488873916097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4113961225860992582610731 6170941838791488873916097)
              ·
                refine ⟨4628206379093616655437073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6170941838791488873916097 4628206379093616655437073)
                ·
                  refine ⟨3471154784320212491577805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4628206379093616655437073 3471154784320212491577805)
                  ·
                    refine ⟨1301683044120079684341677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3471154784320212491577805 1301683044120079684341677)
                    ·
                      refine ⟨488131141545029881628129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1301683044120079684341677 488131141545029881628129)
                      ·
                        rfl

theorem cell23_950632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_950632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950632 prefixEnd_950632 := by exact prefixLift 950632
  have htrace : WordTrace (prefixWord ++ tailWord_950632) baseStart_950632 baseEnd_950632 := by
    simpa [prefixWord, tailWord_950632, baseEnd_950632] using wordTrace_append hprefix tailTrace_950632
  have hstable : (prefixWord ++ tailWord_950632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950632).length < 2 ^ (prefixWord ++ tailWord_950632).sum := by decide
  have hdescent : baseEnd_950632 < baseStart_950632 := by decide
  rcases family_descends (prefixWord ++ tailWord_950632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950655 : List Nat := [1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 4]
def baseStart_950655 : Nat := 118140960795 + 950655 * 2 ^ 59
def prefixEnd_950655 : Nat := 4983230072969 + 3 ^ 40 * 950655 * 2
def baseEnd_950655 : Nat := 488142951600083291640523

theorem tailTrace_950655 : CollatzResearch.WordTrace tailWord_950655 prefixEnd_950655 488142951600083291640523 := by
  unfold tailWord_950655
  simp only [CollatzResearch.WordTrace]
  refine ⟨34673236370946768793053419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23115490913964512528702279 34673236370946768793053419)
  ·
    refine ⟨52009854556420153189580129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34673236370946768793053419 52009854556420153189580129)
    ·
      refine ⟨39007390917315114892185097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52009854556420153189580129 39007390917315114892185097)
      ·
        refine ⟨29255543187986336169138823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39007390917315114892185097 29255543187986336169138823)
        ·
          refine ⟨43883314781979504253708235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29255543187986336169138823 43883314781979504253708235)
          ·
            refine ⟨65824972172969256380562353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43883314781979504253708235 65824972172969256380562353)
            ·
              refine ⟨49368729129726942285421765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65824972172969256380562353 49368729129726942285421765)
              ·
                refine ⟨9256636711823801678516581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49368729129726942285421765 9256636711823801678516581)
                ·
                  refine ⟨1735619383466962814721859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9256636711823801678516581 1735619383466962814721859)
                  ·
                    refine ⟨2603429075200444222082789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1735619383466962814721859 2603429075200444222082789)
                    ·
                      refine ⟨488142951600083291640523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2603429075200444222082789 488142951600083291640523)
                      ·
                        rfl

theorem cell23_950655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 4].length) (baseStart_950655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950655 prefixEnd_950655 := by exact prefixLift 950655
  have htrace : WordTrace (prefixWord ++ tailWord_950655) baseStart_950655 baseEnd_950655 := by
    simpa [prefixWord, tailWord_950655, baseEnd_950655] using wordTrace_append hprefix tailTrace_950655
  have hstable : (prefixWord ++ tailWord_950655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950655).length < 2 ^ (prefixWord ++ tailWord_950655).sum := by decide
  have hdescent : baseEnd_950655 < baseStart_950655 := by decide
  rcases family_descends (prefixWord ++ tailWord_950655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950692 : List Nat := [2, 3, 1, 2, 1, 1, 3, 1, 4, 2, 3]
def baseStart_950692 : Nat := 118140960795 + 950692 * 2 ^ 59
def prefixEnd_950692 : Nat := 4983230072969 + 3 ^ 40 * 950692 * 2
def baseEnd_950692 : Nat := 488161950384299646877853

theorem tailTrace_950692 : CollatzResearch.WordTrace tailWord_950692 prefixEnd_950692 488161950384299646877853 := by
  unfold tailWord_950692
  simp only [CollatzResearch.WordTrace]
  refine ⟨17337292935906362056075165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23116390581208482741433553 17337292935906362056075165)
  ·
    refine ⟨6501484850964885771028187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17337292935906362056075165 6501484850964885771028187)
    ·
      refine ⟨9752227276447328656542281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6501484850964885771028187 9752227276447328656542281)
      ·
        refine ⟨7314170457335496492406711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9752227276447328656542281 7314170457335496492406711)
        ·
          refine ⟨10971255686003244738610067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7314170457335496492406711 10971255686003244738610067)
          ·
            refine ⟨16456883529004867107915101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10971255686003244738610067 16456883529004867107915101)
            ·
              refine ⟨6171331323376825165468163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16456883529004867107915101 6171331323376825165468163)
              ·
                refine ⟨9256996985065237748202245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6171331323376825165468163 9256996985065237748202245)
                ·
                  refine ⟨1735686934699732077787921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9256996985065237748202245 1735686934699732077787921)
                  ·
                    refine ⟨1301765201024799058340941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1735686934699732077787921 1301765201024799058340941)
                    ·
                      refine ⟨488161950384299646877853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1301765201024799058340941 488161950384299646877853)
                      ·
                        rfl

theorem cell23_950692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_950692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950692 prefixEnd_950692 := by exact prefixLift 950692
  have htrace : WordTrace (prefixWord ++ tailWord_950692) baseStart_950692 baseEnd_950692 := by
    simpa [prefixWord, tailWord_950692, baseEnd_950692] using wordTrace_append hprefix tailTrace_950692
  have hstable : (prefixWord ++ tailWord_950692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950692).length < 2 ^ (prefixWord ++ tailWord_950692).sum := by decide
  have hdescent : baseEnd_950692 < baseStart_950692 := by decide
  rcases family_descends (prefixWord ++ tailWord_950692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950773 : List Nat := [1, 3, 5, 1, 2, 1, 1, 2, 3, 1, 3]
def baseStart_950773 : Nat := 118140960795 + 950773 * 2 ^ 59
def prefixEnd_950773 : Nat := 4983230072969 + 3 ^ 40 * 950773 * 2
def baseEnd_950773 : Nat := 488203542317313829964981

theorem tailTrace_950773 : CollatzResearch.WordTrace tailWord_950773 prefixEnd_950773 488203542317313829964981 := by
  unfold tailWord_950773
  simp only [CollatzResearch.WordTrace]
  refine ⟨34677540184519274945848973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23118360123012849963899315 34677540184519274945848973)
  ·
    refine ⟨13004077569194728104693365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34677540184519274945848973 13004077569194728104693365)
    ·
      refine ⟨1219132272112005759815003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13004077569194728104693365 1219132272112005759815003)
      ·
        refine ⟨1828698408168008639722505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1219132272112005759815003 1828698408168008639722505)
        ·
          refine ⟨1371523806126006479791879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1828698408168008639722505 1371523806126006479791879)
          ·
            refine ⟨2057285709189009719687819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1371523806126006479791879 2057285709189009719687819)
            ·
              refine ⟨3085928563783514579531729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2057285709189009719687819 3085928563783514579531729)
              ·
                refine ⟨2314446422837635934648797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3085928563783514579531729 2314446422837635934648797)
                ·
                  refine ⟨867917408564113475493299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2314446422837635934648797 867917408564113475493299)
                  ·
                    refine ⟨1301876112846170213239949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 867917408564113475493299 1301876112846170213239949)
                    ·
                      refine ⟨488203542317313829964981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1301876112846170213239949 488203542317313829964981)
                      ·
                        rfl

theorem cell23_950773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_950773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950773 prefixEnd_950773 := by exact prefixLift 950773
  have htrace : WordTrace (prefixWord ++ tailWord_950773) baseStart_950773 baseEnd_950773 := by
    simpa [prefixWord, tailWord_950773, baseEnd_950773] using wordTrace_append hprefix tailTrace_950773
  have hstable : (prefixWord ++ tailWord_950773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950773).length < 2 ^ (prefixWord ++ tailWord_950773).sum := by decide
  have hdescent : baseEnd_950773 < baseStart_950773 := by decide
  rcases family_descends (prefixWord ++ tailWord_950773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950775 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 6]
def baseStart_950775 : Nat := 118140960795 + 950775 * 2 ^ 59
def prefixEnd_950775 : Nat := 4983230072969 + 3 ^ 40 * 950775 * 2
def baseEnd_950775 : Nat := 488204569278622822139971

theorem tailTrace_950775 : CollatzResearch.WordTrace tailWord_950775 prefixEnd_950775 488204569278622822139971 := by
  unfold tailWord_950775
  simp only [CollatzResearch.WordTrace]
  refine ⟨34677613130512029287421779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23118408753674686191614519 34677613130512029287421779)
  ·
    refine ⟨52016419695768043931132669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34677613130512029287421779 52016419695768043931132669)
    ·
      refine ⟨19506157385913016474174751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52016419695768043931132669 19506157385913016474174751)
      ·
        refine ⟨29259236078869524711262127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19506157385913016474174751 29259236078869524711262127)
        ·
          refine ⟨43888854118304287066893191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29259236078869524711262127 43888854118304287066893191)
          ·
            refine ⟨65833281177456430600339787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43888854118304287066893191 65833281177456430600339787)
            ·
              refine ⟨98749921766184645900509681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65833281177456430600339787 98749921766184645900509681)
              ·
                refine ⟨74062441324638484425382261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98749921766184645900509681 74062441324638484425382261)
                ·
                  refine ⟨6943353874184857914879587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74062441324638484425382261 6943353874184857914879587)
                  ·
                    refine ⟨10415030811277286872319381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6943353874184857914879587 10415030811277286872319381)
                    ·
                      refine ⟨488204569278622822139971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10415030811277286872319381 488204569278622822139971)
                      ·
                        rfl

theorem cell23_950775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_950775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950775 prefixEnd_950775 := by exact prefixLift 950775
  have htrace : WordTrace (prefixWord ++ tailWord_950775) baseStart_950775 baseEnd_950775 := by
    simpa [prefixWord, tailWord_950775, baseEnd_950775] using wordTrace_append hprefix tailTrace_950775
  have hstable : (prefixWord ++ tailWord_950775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950775).length < 2 ^ (prefixWord ++ tailWord_950775).sum := by decide
  have hdescent : baseEnd_950775 < baseStart_950775 := by decide
  rcases family_descends (prefixWord ++ tailWord_950775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950796 : List Nat := [2, 2, 1, 2, 4, 1, 4, 1, 1, 1, 4]
def baseStart_950796 : Nat := 118140960795 + 950796 * 2 ^ 59
def prefixEnd_950796 : Nat := 4983230072969 + 3 ^ 40 * 950796 * 2
def baseEnd_950796 : Nat := 488215352372367239977375

theorem tailTrace_950796 : CollatzResearch.WordTrace tailWord_950796 prefixEnd_950796 488215352372367239977375 := by
  unfold tailWord_950796
  simp only [CollatzResearch.WordTrace]
  refine ⟨17339189531717974936968121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23118919375623966582624161 17339189531717974936968121)
  ·
    refine ⟨13004392148788481202726091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17339189531717974936968121 13004392148788481202726091)
    ·
      refine ⟨19506588223182721804089137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13004392148788481202726091 19506588223182721804089137)
      ·
        refine ⟨14629941167387041353066853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19506588223182721804089137 14629941167387041353066853)
        ·
          refine ⟨2743113968885070253700035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14629941167387041353066853 2743113968885070253700035)
          ·
            refine ⟨4114670953327605380550053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2743113968885070253700035 4114670953327605380550053)
            ·
              refine ⟨771500803748926008853135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4114670953327605380550053 771500803748926008853135)
              ·
                refine ⟨1157251205623389013279703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 771500803748926008853135 1157251205623389013279703)
                ·
                  refine ⟨1735876808435083519919555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1157251205623389013279703 1735876808435083519919555)
                  ·
                    refine ⟨2603815212652625279879333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1735876808435083519919555 2603815212652625279879333)
                    ·
                      refine ⟨488215352372367239977375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2603815212652625279879333 488215352372367239977375)
                      ·
                        rfl

theorem cell23_950796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 1, 1, 4].length) (baseStart_950796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950796 prefixEnd_950796 := by exact prefixLift 950796
  have htrace : WordTrace (prefixWord ++ tailWord_950796) baseStart_950796 baseEnd_950796 := by
    simpa [prefixWord, tailWord_950796, baseEnd_950796] using wordTrace_append hprefix tailTrace_950796
  have hstable : (prefixWord ++ tailWord_950796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950796).length < 2 ^ (prefixWord ++ tailWord_950796).sum := by decide
  have hdescent : baseEnd_950796 < baseStart_950796 := by decide
  rcases family_descends (prefixWord ++ tailWord_950796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950813 : List Nat := [1, 4, 2, 2, 1, 3, 2, 1, 3, 2, 2]
def baseStart_950813 : Nat := 118140960795 + 950813 * 2 ^ 59
def prefixEnd_950813 : Nat := 4983230072969 + 3 ^ 40 * 950813 * 2
def baseEnd_950813 : Nat := 488224081543493673464797

theorem tailTrace_950813 : CollatzResearch.WordTrace tailWord_950813 prefixEnd_950813 488224081543493673464797 := by
  unfold tailWord_950813
  simp only [CollatzResearch.WordTrace]
  refine ⟨34678999104374361777305093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23119332736249574518203395 34678999104374361777305093)
  ·
    refine ⟨6502312332070192833244705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34678999104374361777305093 6502312332070192833244705)
    ·
      refine ⟨4876734249052644624933529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6502312332070192833244705 4876734249052644624933529)
      ·
        refine ⟨3657550686789483468700147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4876734249052644624933529 3657550686789483468700147)
        ·
          refine ⟨5486326030184225203050221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3657550686789483468700147 5486326030184225203050221)
          ·
            refine ⟨2057372261319084451143833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5486326030184225203050221 2057372261319084451143833)
            ·
              refine ⟨1543029195989313338357875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2057372261319084451143833 1543029195989313338357875)
              ·
                refine ⟨2314543793983970007536813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1543029195989313338357875 2314543793983970007536813)
                ·
                  refine ⟨867953922743988752826305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2314543793983970007536813 867953922743988752826305)
                  ·
                    refine ⟨650965442057991564619729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 867953922743988752826305 650965442057991564619729)
                    ·
                      refine ⟨488224081543493673464797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 650965442057991564619729 488224081543493673464797)
                      ·
                        rfl

theorem cell23_950813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_950813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950813 prefixEnd_950813 := by exact prefixLift 950813
  have htrace : WordTrace (prefixWord ++ tailWord_950813) baseStart_950813 baseEnd_950813 := by
    simpa [prefixWord, tailWord_950813, baseEnd_950813] using wordTrace_append hprefix tailTrace_950813
  have hstable : (prefixWord ++ tailWord_950813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950813).length < 2 ^ (prefixWord ++ tailWord_950813).sum := by decide
  have hdescent : baseEnd_950813 < baseStart_950813 := by decide
  rcases family_descends (prefixWord ++ tailWord_950813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950823 : List Nat := [1, 1, 7, 2, 1, 2, 1, 1, 1, 6]
def baseStart_950823 : Nat := 118140960795 + 950823 * 2 ^ 59
def prefixEnd_950823 : Nat := 4983230072969 + 3 ^ 40 * 950823 * 2
def baseEnd_950823 : Nat := 162743072116679544779917

theorem tailTrace_950823 : CollatzResearch.WordTrace tailWord_950823 prefixEnd_950823 162743072116679544779917 := by
  unfold tailWord_950823
  simp only [CollatzResearch.WordTrace]
  refine ⟨34679363834338133485169123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23119575889558755656779415 34679363834338133485169123)
  ·
    refine ⟨52019045751507200227753685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34679363834338133485169123 52019045751507200227753685)
    ·
      refine ⟨1219196384800950005337977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 52019045751507200227753685 1219196384800950005337977)
      ·
        refine ⟨914397288600712504003483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1219196384800950005337977 914397288600712504003483)
        ·
          refine ⟨1371595932901068756005225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 914397288600712504003483 1371595932901068756005225)
          ·
            refine ⟨1028696949675801567003919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1371595932901068756005225 1028696949675801567003919)
            ·
              refine ⟨1543045424513702350505879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1028696949675801567003919 1543045424513702350505879)
              ·
                refine ⟨2314568136770553525758819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1543045424513702350505879 2314568136770553525758819)
                ·
                  refine ⟨3471852205155830288638229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2314568136770553525758819 3471852205155830288638229)
                  ·
                    refine ⟨162743072116679544779917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3471852205155830288638229 162743072116679544779917)
                    ·
                      rfl

theorem cell23_950823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_950823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950823 prefixEnd_950823 := by exact prefixLift 950823
  have htrace : WordTrace (prefixWord ++ tailWord_950823) baseStart_950823 baseEnd_950823 := by
    simpa [prefixWord, tailWord_950823, baseEnd_950823] using wordTrace_append hprefix tailTrace_950823
  have hstable : (prefixWord ++ tailWord_950823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950823).length < 2 ^ (prefixWord ++ tailWord_950823).sum := by decide
  have hdescent : baseEnd_950823 < baseStart_950823 := by decide
  rcases family_descends (prefixWord ++ tailWord_950823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950826 : List Nat := [3, 1, 4, 1, 1, 4, 1, 1, 1, 2, 4]
def baseStart_950826 : Nat := 118140960795 + 950826 * 2 ^ 59
def prefixEnd_950826 : Nat := 4983230072969 + 3 ^ 40 * 950826 * 2
def baseEnd_950826 : Nat := 488230756792002122602237

theorem tailTrace_950826 : CollatzResearch.WordTrace tailWord_950826 prefixEnd_950826 488230756792002122602237 := by
  unfold tailWord_950826
  simp only [CollatzResearch.WordTrace]
  refine ⟨8669868313331816249382083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23119648835551509998352221 8669868313331816249382083)
  ·
    refine ⟨13004802469997724374073125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8669868313331816249382083 13004802469997724374073125)
    ·
      refine ⟨2438400463124573320138711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13004802469997724374073125 2438400463124573320138711)
      ·
        refine ⟨3657600694686859980208067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2438400463124573320138711 3657600694686859980208067)
        ·
          refine ⟨5486401042030289970312101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3657600694686859980208067 5486401042030289970312101)
          ·
            refine ⟨1028700195380679369433519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5486401042030289970312101 1028700195380679369433519)
            ·
              refine ⟨1543050293071019054150279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1028700195380679369433519 1543050293071019054150279)
              ·
                refine ⟨2314575439606528581225419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1543050293071019054150279 2314575439606528581225419)
                ·
                  refine ⟨3471863159409792871838129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2314575439606528581225419 3471863159409792871838129)
                  ·
                    refine ⟨2603897369557344653878597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3471863159409792871838129 2603897369557344653878597)
                    ·
                      refine ⟨488230756792002122602237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2603897369557344653878597 488230756792002122602237)
                      ·
                        rfl

theorem cell23_950826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_950826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950826 prefixEnd_950826 := by exact prefixLift 950826
  have htrace : WordTrace (prefixWord ++ tailWord_950826) baseStart_950826 baseEnd_950826 := by
    simpa [prefixWord, tailWord_950826, baseEnd_950826] using wordTrace_append hprefix tailTrace_950826
  have hstable : (prefixWord ++ tailWord_950826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950826).length < 2 ^ (prefixWord ++ tailWord_950826).sum := by decide
  have hdescent : baseEnd_950826 < baseStart_950826 := by decide
  rcases family_descends (prefixWord ++ tailWord_950826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950836 : List Nat := [2, 5, 1, 3, 1, 1, 1, 9]
def baseStart_950836 : Nat := 118140960795 + 950836 * 2 ^ 59
def prefixEnd_950836 : Nat := 4983230072969 + 3 ^ 40 * 950836 * 2
def baseEnd_950836 : Nat := 18082810799946188276933

theorem tailTrace_950836 : CollatzResearch.WordTrace tailWord_950836 prefixEnd_950836 18082810799946188276933 := by
  unfold tailWord_950836
  simp only [CollatzResearch.WordTrace]
  refine ⟨17339918991645518352696181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23119891988860691136928241 17339918991645518352696181)
  ·
    refine ⟨1625617405466767345565267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17339918991645518352696181 1625617405466767345565267)
    ·
      refine ⟨2438426108200151018347901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1625617405466767345565267 2438426108200151018347901)
      ·
        refine ⟨914409790575056631880463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2438426108200151018347901 914409790575056631880463)
        ·
          refine ⟨1371614685862584947820695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 914409790575056631880463 1371614685862584947820695)
          ·
            refine ⟨2057422028793877421731043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1371614685862584947820695 2057422028793877421731043)
            ·
              refine ⟨3086133043190816132596565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2057422028793877421731043 3086133043190816132596565)
              ·
                refine ⟨18082810799946188276933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3086133043190816132596565 18082810799946188276933)
                ·
                  rfl

theorem cell23_950836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 9].length) (baseStart_950836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950836 prefixEnd_950836 := by exact prefixLift 950836
  have htrace : WordTrace (prefixWord ++ tailWord_950836) baseStart_950836 baseEnd_950836 := by
    simpa [prefixWord, tailWord_950836, baseEnd_950836] using wordTrace_append hprefix tailTrace_950836
  have hstable : (prefixWord ++ tailWord_950836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950836).length < 2 ^ (prefixWord ++ tailWord_950836).sum := by decide
  have hdescent : baseEnd_950836 < baseStart_950836 := by decide
  rcases family_descends (prefixWord ++ tailWord_950836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950842 : List Nat := [3, 1, 1, 1, 3, 3, 1, 1, 2, 2, 5]
def baseStart_950842 : Nat := 118140960795 + 950842 * 2 ^ 59
def prefixEnd_950842 : Nat := 4983230072969 + 3 ^ 40 * 950842 * 2
def baseEnd_950842 : Nat := 488238972482474060002163

theorem tailTrace_950842 : CollatzResearch.WordTrace tailWord_950842 prefixEnd_950842 488238972482474060002163 := by
  unfold tailWord_950842
  simp only [CollatzResearch.WordTrace]
  refine ⟨8670014205317324932527695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23120037880846199820073853 8670014205317324932527695)
  ·
    refine ⟨13005021307975987398791543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8670014205317324932527695 13005021307975987398791543)
    ·
      refine ⟨19507531961963981098187315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13005021307975987398791543 19507531961963981098187315)
      ·
        refine ⟨29261297942945971647280973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19507531961963981098187315 29261297942945971647280973)
        ·
          refine ⟨10972986728604739367730365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29261297942945971647280973 10972986728604739367730365)
          ·
            refine ⟨4114870023226777262898887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10972986728604739367730365 4114870023226777262898887)
            ·
              refine ⟨6172305034840165894348331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4114870023226777262898887 6172305034840165894348331)
              ·
                refine ⟨9258457552260248841522497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6172305034840165894348331 9258457552260248841522497)
                ·
                  refine ⟨6943843164195186631141873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9258457552260248841522497 6943843164195186631141873)
                  ·
                    refine ⟨5207882373146389973356405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6943843164195186631141873 5207882373146389973356405)
                    ·
                      refine ⟨488238972482474060002163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5207882373146389973356405 488238972482474060002163)
                      ·
                        rfl

theorem cell23_950842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_950842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950842 prefixEnd_950842 := by exact prefixLift 950842
  have htrace : WordTrace (prefixWord ++ tailWord_950842) baseStart_950842 baseEnd_950842 := by
    simpa [prefixWord, tailWord_950842, baseEnd_950842] using wordTrace_append hprefix tailTrace_950842
  have hstable : (prefixWord ++ tailWord_950842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950842).length < 2 ^ (prefixWord ++ tailWord_950842).sum := by decide
  have hdescent : baseEnd_950842 < baseStart_950842 := by decide
  rcases family_descends (prefixWord ++ tailWord_950842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950862 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 4, 6]
def baseStart_950862 : Nat := 118140960795 + 950862 * 2 ^ 59
def prefixEnd_950862 : Nat := 4983230072969 + 3 ^ 40 * 950862 * 2
def baseEnd_950862 : Nat := 162749747365187993917357

theorem tailTrace_950862 : CollatzResearch.WordTrace tailWord_950862 prefixEnd_950862 162749747365187993917357 := by
  unfold tailWord_950862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4335098285149605393229855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23120524187464562097225893 4335098285149605393229855)
  ·
    refine ⟨6502647427724408089844783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4335098285149605393229855 6502647427724408089844783)
    ·
      refine ⟨9753971141586612134767175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6502647427724408089844783 9753971141586612134767175)
      ·
        refine ⟨14630956712379918202150763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9753971141586612134767175 14630956712379918202150763)
        ·
          refine ⟨21946435068569877303226145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14630956712379918202150763 21946435068569877303226145)
          ·
            refine ⟨16459826301427407977419609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21946435068569877303226145 16459826301427407977419609)
            ·
              refine ⟨12344869726070555983064707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16459826301427407977419609 12344869726070555983064707)
              ·
                refine ⟨18517304589105833974597061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12344869726070555983064707 18517304589105833974597061)
                ·
                  refine ⟨3471994610457343870236949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18517304589105833974597061 3471994610457343870236949)
                  ·
                    refine ⟨162749747365187993917357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3471994610457343870236949 162749747365187993917357)
                    ·
                      rfl

theorem cell23_950862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_950862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950862 prefixEnd_950862 := by exact prefixLift 950862
  have htrace : WordTrace (prefixWord ++ tailWord_950862) baseStart_950862 baseEnd_950862 := by
    simpa [prefixWord, tailWord_950862, baseEnd_950862] using wordTrace_append hprefix tailTrace_950862
  have hstable : (prefixWord ++ tailWord_950862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950862).length < 2 ^ (prefixWord ++ tailWord_950862).sum := by decide
  have hdescent : baseEnd_950862 < baseStart_950862 := by decide
  rcases family_descends (prefixWord ++ tailWord_950862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950892 : List Nat := [2, 2, 1, 1, 3, 1, 2, 4, 7]
def baseStart_950892 : Nat := 118140960795 + 950892 * 2 ^ 59
def prefixEnd_950892 : Nat := 4983230072969 + 3 ^ 40 * 950892 * 2
def baseEnd_950892 : Nat := 54251627390577651597437

theorem tailTrace_950892 : CollatzResearch.WordTrace tailWord_950892 prefixEnd_950892 54251627390577651597437 := by
  unfold tailWord_950892
  simp only [CollatzResearch.WordTrace]
  refine ⟨17340940235544079134715465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23121253647392105512953953 17340940235544079134715465)
  ·
    refine ⟨13005705176658059351036599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17340940235544079134715465 13005705176658059351036599)
    ·
      refine ⟨19508557764987089026554899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13005705176658059351036599 19508557764987089026554899)
      ·
        refine ⟨29262836647480633539832349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19508557764987089026554899 29262836647480633539832349)
        ·
          refine ⟨10973563742805237577437131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29262836647480633539832349 10973563742805237577437131)
          ·
            refine ⟨16460345614207856366155697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10973563742805237577437131 16460345614207856366155697)
            ·
              refine ⟨12345259210655892274616773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16460345614207856366155697 12345259210655892274616773)
              ·
                refine ⟨2314736101997979801490645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12345259210655892274616773 2314736101997979801490645)
                ·
                  refine ⟨54251627390577651597437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2314736101997979801490645 54251627390577651597437)
                  ·
                    rfl

theorem cell23_950892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 7].length) (baseStart_950892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950892 prefixEnd_950892 := by exact prefixLift 950892
  have htrace : WordTrace (prefixWord ++ tailWord_950892) baseStart_950892 baseEnd_950892 := by
    simpa [prefixWord, tailWord_950892, baseEnd_950892] using wordTrace_append hprefix tailTrace_950892
  have hstable : (prefixWord ++ tailWord_950892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950892).length < 2 ^ (prefixWord ++ tailWord_950892).sum := by decide
  have hdescent : baseEnd_950892 < baseStart_950892 := by decide
  rcases family_descends (prefixWord ++ tailWord_950892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950914 : List Nat := [3, 4, 3, 1, 1, 1, 2, 2, 2, 1, 3]
def baseStart_950914 : Nat := 118140960795 + 950914 * 2 ^ 59
def prefixEnd_950914 : Nat := 4983230072969 + 3 ^ 40 * 950914 * 2
def baseEnd_950914 : Nat := 488275943089597778301833

theorem tailTrace_950914 : CollatzResearch.WordTrace tailWord_950914 prefixEnd_950914 488275943089597778301833 := by
  unfold tailWord_950914
  simp only [CollatzResearch.WordTrace]
  refine ⟨8670670719252114006682949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23121788584672304017821197 8670670719252114006682949)
  ·
    refine ⟨1625750759859771376253053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8670670719252114006682949 1625750759859771376253053)
    ·
      refine ⟨609656534947414266094895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1625750759859771376253053 609656534947414266094895)
      ·
        refine ⟨914484802421121399142343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609656534947414266094895 914484802421121399142343)
        ·
          refine ⟨1371727203631682098713515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 914484802421121399142343 1371727203631682098713515)
          ·
            refine ⟨2057590805447523148070273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1371727203631682098713515 2057590805447523148070273)
            ·
              refine ⟨1543193104085642361052705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2057590805447523148070273 1543193104085642361052705)
              ·
                refine ⟨1157394828064231770789529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1543193104085642361052705 1157394828064231770789529)
                ·
                  refine ⟨868046121048173828092147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1157394828064231770789529 868046121048173828092147)
                  ·
                    refine ⟨1302069181572260742138221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 868046121048173828092147 1302069181572260742138221)
                    ·
                      refine ⟨488275943089597778301833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1302069181572260742138221 488275943089597778301833)
                      ·
                        rfl

theorem cell23_950914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_950914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950914 prefixEnd_950914 := by exact prefixLift 950914
  have htrace : WordTrace (prefixWord ++ tailWord_950914) baseStart_950914 baseEnd_950914 := by
    simpa [prefixWord, tailWord_950914, baseEnd_950914] using wordTrace_append hprefix tailTrace_950914
  have hstable : (prefixWord ++ tailWord_950914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950914).length < 2 ^ (prefixWord ++ tailWord_950914).sum := by decide
  have hdescent : baseEnd_950914 < baseStart_950914 := by decide
  rcases family_descends (prefixWord ++ tailWord_950914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950919 : List Nat := [1, 1, 4, 2, 1, 2, 2, 2, 2, 3, 3]
def baseStart_950919 : Nat := 118140960795 + 950919 * 2 ^ 59
def prefixEnd_950919 : Nat := 4983230072969 + 3 ^ 40 * 950919 * 2
def baseEnd_950919 : Nat := 488278510492870258739309

theorem tailTrace_950919 : CollatzResearch.WordTrace tailWord_950919 prefixEnd_950919 488278510492870258739309 := by
  unfold tailWord_950919
  simp only [CollatzResearch.WordTrace]
  refine ⟨34682865241990341880663811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23121910161326894587109207 34682865241990341880663811)
  ·
    refine ⟨52024297862985512820995717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34682865241990341880663811 52024297862985512820995717)
    ·
      refine ⟨9754555849309783653936697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52024297862985512820995717 9754555849309783653936697)
      ·
        refine ⟨7315916886982337740452523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9754555849309783653936697 7315916886982337740452523)
        ·
          refine ⟨10973875330473506610678785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7315916886982337740452523 10973875330473506610678785)
          ·
            refine ⟨8230406497855129958009089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10973875330473506610678785 8230406497855129958009089)
            ·
              refine ⟨6172804873391347468506817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8230406497855129958009089 6172804873391347468506817)
              ·
                refine ⟨4629603655043510601380113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6172804873391347468506817 4629603655043510601380113)
                ·
                  refine ⟨3472202741282632951035085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4629603655043510601380113 3472202741282632951035085)
                  ·
                    refine ⟨1302076027980987356638157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3472202741282632951035085 1302076027980987356638157)
                    ·
                      refine ⟨488278510492870258739309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1302076027980987356638157 488278510492870258739309)
                      ·
                        rfl

theorem cell23_950919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_950919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950919 prefixEnd_950919 := by exact prefixLift 950919
  have htrace : WordTrace (prefixWord ++ tailWord_950919) baseStart_950919 baseEnd_950919 := by
    simpa [prefixWord, tailWord_950919, baseEnd_950919] using wordTrace_append hprefix tailTrace_950919
  have hstable : (prefixWord ++ tailWord_950919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950919).length < 2 ^ (prefixWord ++ tailWord_950919).sum := by decide
  have hdescent : baseEnd_950919 < baseStart_950919 := by decide
  rcases family_descends (prefixWord ++ tailWord_950919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950926 : List Nat := [4, 1, 1, 3, 1, 1, 3, 4, 5]
def baseStart_950926 : Nat := 118140960795 + 950926 * 2 ^ 59
def prefixEnd_950926 : Nat := 4983230072969 + 3 ^ 40 * 950926 * 2
def baseEnd_950926 : Nat := 54253567206383525705753

theorem tailTrace_950926 : CollatzResearch.WordTrace tailWord_950926 prefixEnd_950926 54253567206383525705753 := by
  unfold tailWord_950926
  simp only [CollatzResearch.WordTrace]
  refine ⟨4335390069120622759521079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23122080368643321384112421 4335390069120622759521079)
  ·
    refine ⟨6503085103680934139281619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4335390069120622759521079 6503085103680934139281619)
    ·
      refine ⟨9754627655521401208922429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6503085103680934139281619 9754627655521401208922429)
      ·
        refine ⟨3657985370820525453345911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9754627655521401208922429 3657985370820525453345911)
        ·
          refine ⟨5486978056230788180018867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3657985370820525453345911 5486978056230788180018867)
          ·
            refine ⟨8230467084346182270028301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5486978056230788180018867 8230467084346182270028301)
            ·
              refine ⟨3086425156629818351260613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8230467084346182270028301 3086425156629818351260613)
              ·
                refine ⟨578704716868090940861365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3086425156629818351260613 578704716868090940861365)
                ·
                  refine ⟨54253567206383525705753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 578704716868090940861365 54253567206383525705753)
                  ·
                    rfl

theorem cell23_950926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 4, 5].length) (baseStart_950926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950926 prefixEnd_950926 := by exact prefixLift 950926
  have htrace : WordTrace (prefixWord ++ tailWord_950926) baseStart_950926 baseEnd_950926 := by
    simpa [prefixWord, tailWord_950926, baseEnd_950926] using wordTrace_append hprefix tailTrace_950926
  have hstable : (prefixWord ++ tailWord_950926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950926).length < 2 ^ (prefixWord ++ tailWord_950926).sum := by decide
  have hdescent : baseEnd_950926 < baseStart_950926 := by decide
  rcases family_descends (prefixWord ++ tailWord_950926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950959 : List Nat := [1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 4]
def baseStart_950959 : Nat := 118140960795 + 950959 * 2 ^ 59
def prefixEnd_950959 : Nat := 4983230072969 + 3 ^ 40 * 950959 * 2
def baseEnd_950959 : Nat := 488299049719050102239125

theorem tailTrace_950959 : CollatzResearch.WordTrace tailWord_950959 prefixEnd_950959 488299049719050102239125 := by
  unfold tailWord_950959
  simp only [CollatzResearch.WordTrace]
  refine ⟨34684324161845428712119931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23122882774563619141413287 34684324161845428712119931)
  ·
    refine ⟨52026486242768143068179897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34684324161845428712119931 52026486242768143068179897)
    ·
      refine ⟨39019864682076107301134923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52026486242768143068179897 39019864682076107301134923)
      ·
        refine ⟨58529797023114160951702385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39019864682076107301134923 58529797023114160951702385)
        ·
          refine ⟨43897347767335620713776789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58529797023114160951702385 43897347767335620713776789)
          ·
            refine ⟨2057688176593857220958287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43897347767335620713776789 2057688176593857220958287)
            ·
              refine ⟨3086532264890785831437431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2057688176593857220958287 3086532264890785831437431)
              ·
                refine ⟨4629798397336178747156147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3086532264890785831437431 4629798397336178747156147)
                ·
                  refine ⟨6944697596004268120734221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4629798397336178747156147 6944697596004268120734221)
                  ·
                    refine ⟨2604261598501600545275333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6944697596004268120734221 2604261598501600545275333)
                    ·
                      refine ⟨488299049719050102239125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2604261598501600545275333 488299049719050102239125)
                      ·
                        rfl

theorem cell23_950959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 4].length) (baseStart_950959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950959 prefixEnd_950959 := by exact prefixLift 950959
  have htrace : WordTrace (prefixWord ++ tailWord_950959) baseStart_950959 baseEnd_950959 := by
    simpa [prefixWord, tailWord_950959, baseEnd_950959] using wordTrace_append hprefix tailTrace_950959
  have hstable : (prefixWord ++ tailWord_950959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950959).length < 2 ^ (prefixWord ++ tailWord_950959).sum := by decide
  have hdescent : baseEnd_950959 < baseStart_950959 := by decide
  rcases family_descends (prefixWord ++ tailWord_950959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950969 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 7, 4]
def baseStart_950969 : Nat := 118140960795 + 950969 * 2 ^ 59
def prefixEnd_950969 : Nat := 4983230072969 + 3 ^ 40 * 950969 * 2
def baseEnd_950969 : Nat := 162768061508531687704693

theorem tailTrace_950969 : CollatzResearch.WordTrace tailWord_950969 prefixEnd_950969 162768061508531687704693 := by
  unfold tailWord_950969
  simp only [CollatzResearch.WordTrace]
  refine ⟨34684688891809200419983961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23123125927872800279989307 34684688891809200419983961)
  ·
    refine ⟨26013516668856900314987971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34684688891809200419983961 26013516668856900314987971)
    ·
      refine ⟨39020275003285350472481957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26013516668856900314987971 39020275003285350472481957)
      ·
        refine ⟨7316301563116003213590367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39020275003285350472481957 7316301563116003213590367)
        ·
          refine ⟨10974452344674004820385551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7316301563116003213590367 10974452344674004820385551)
          ·
            refine ⟨16461678517011007230578327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10974452344674004820385551 16461678517011007230578327)
            ·
              refine ⟨24692517775516510845867491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16461678517011007230578327 24692517775516510845867491)
              ·
                refine ⟨37038776663274766268801237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24692517775516510845867491 37038776663274766268801237)
                ·
                  refine ⟨868096328045502334425029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 37038776663274766268801237 868096328045502334425029)
                  ·
                    refine ⟨162768061508531687704693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 868096328045502334425029 162768061508531687704693)
                    ·
                      rfl

theorem cell23_950969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 7, 4].length) (baseStart_950969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950969 prefixEnd_950969 := by exact prefixLift 950969
  have htrace : WordTrace (prefixWord ++ tailWord_950969) baseStart_950969 baseEnd_950969 := by
    simpa [prefixWord, tailWord_950969, baseEnd_950969] using wordTrace_append hprefix tailTrace_950969
  have hstable : (prefixWord ++ tailWord_950969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950969).length < 2 ^ (prefixWord ++ tailWord_950969).sum := by decide
  have hdescent : baseEnd_950969 < baseStart_950969 := by decide
  rcases family_descends (prefixWord ++ tailWord_950969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950976 : List Nat := [2, 1, 1, 2, 4, 2, 1, 2, 2, 4, 2]
def baseStart_950976 : Nat := 118140960795 + 950976 * 2 ^ 59
def prefixEnd_950976 : Nat := 4983230072969 + 3 ^ 40 * 950976 * 2
def baseEnd_950976 : Nat := 488307778890176535726547

theorem tailTrace_950976 : CollatzResearch.WordTrace tailWord_950976 prefixEnd_950976 488307778890176535726547 := by
  unfold tailWord_950976
  simp only [CollatzResearch.WordTrace]
  refine ⟨17342472101391920307744391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23123296135189227076992521 17342472101391920307744391)
  ·
    refine ⟨26013708152087880461616587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17342472101391920307744391 26013708152087880461616587)
    ·
      refine ⟨39020562228131820692424881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26013708152087880461616587 39020562228131820692424881)
      ·
        refine ⟨29265421671098865519318661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39020562228131820692424881 29265421671098865519318661)
        ·
          refine ⟨5487266563331037284872249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29265421671098865519318661 5487266563331037284872249)
          ·
            refine ⟨4115449922498277963654187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5487266563331037284872249 4115449922498277963654187)
            ·
              refine ⟨6173174883747416945481281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4115449922498277963654187 6173174883747416945481281)
              ·
                refine ⟨4629881162810562709110961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6173174883747416945481281 4629881162810562709110961)
                ·
                  refine ⟨3472410872107922031833221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4629881162810562709110961 3472410872107922031833221)
                  ·
                    refine ⟨651077038520235380968729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3472410872107922031833221 651077038520235380968729)
                    ·
                      refine ⟨488307778890176535726547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 651077038520235380968729 488307778890176535726547)
                      ·
                        rfl

theorem cell23_950976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 2, 4, 2].length) (baseStart_950976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950976 prefixEnd_950976 := by exact prefixLift 950976
  have htrace : WordTrace (prefixWord ++ tailWord_950976) baseStart_950976 baseEnd_950976 := by
    simpa [prefixWord, tailWord_950976, baseEnd_950976] using wordTrace_append hprefix tailTrace_950976
  have hstable : (prefixWord ++ tailWord_950976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950976).length < 2 ^ (prefixWord ++ tailWord_950976).sum := by decide
  have hdescent : baseEnd_950976 < baseStart_950976 := by decide
  rcases family_descends (prefixWord ++ tailWord_950976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950986 : List Nat := [3, 1, 2, 1, 4, 1, 1, 3, 3, 4]
def baseStart_950986 : Nat := 118140960795 + 950986 * 2 ^ 59
def prefixEnd_950986 : Nat := 4983230072969 + 3 ^ 40 * 950986 * 2
def baseEnd_950986 : Nat := 162770971232240498867167

theorem tailTrace_950986 : CollatzResearch.WordTrace tailWord_950986 prefixEnd_950986 162770971232240498867167 := by
  unfold tailWord_950986
  simp only [CollatzResearch.WordTrace]
  refine ⟨8671327233186903080838203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23123539288498408215568541 8671327233186903080838203)
  ·
    refine ⟨13006990849780354621257305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8671327233186903080838203 13006990849780354621257305)
    ·
      refine ⟨9755243137335265965942979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13006990849780354621257305 9755243137335265965942979)
      ·
        refine ⟨14632864706002898948914469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9755243137335265965942979 14632864706002898948914469)
        ·
          refine ⟨2743662132375543552921463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14632864706002898948914469 2743662132375543552921463)
          ·
            refine ⟨4115493198563315329382195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2743662132375543552921463 4115493198563315329382195)
            ·
              refine ⟨6173239797844972994073293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4115493198563315329382195 6173239797844972994073293)
              ·
                refine ⟨2314964924191864872777485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6173239797844972994073293 2314964924191864872777485)
                ·
                  refine ⟨868111846571949327291557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2314964924191864872777485 868111846571949327291557)
                  ·
                    refine ⟨162770971232240498867167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 868111846571949327291557 162770971232240498867167)
                    ·
                      rfl

theorem cell23_950986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_950986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950986 prefixEnd_950986 := by exact prefixLift 950986
  have htrace : WordTrace (prefixWord ++ tailWord_950986) baseStart_950986 baseEnd_950986 := by
    simpa [prefixWord, tailWord_950986, baseEnd_950986] using wordTrace_append hprefix tailTrace_950986
  have hstable : (prefixWord ++ tailWord_950986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950986).length < 2 ^ (prefixWord ++ tailWord_950986).sum := by decide
  have hdescent : baseEnd_950986 < baseStart_950986 := by decide
  rcases family_descends (prefixWord ++ tailWord_950986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950992 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 9]
def baseStart_950992 : Nat := 118140960795 + 950992 * 2 ^ 59
def prefixEnd_950992 : Nat := 4983230072969 + 3 ^ 40 * 950992 * 2
def baseEnd_950992 : Nat := 488315994580648473126473

theorem tailTrace_950992 : CollatzResearch.WordTrace tailWord_950992 prefixEnd_950992 488315994580648473126473 := by
  unfold tailWord_950992
  simp only [CollatzResearch.WordTrace]
  refine ⟨17342763885362937674035615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23123685180483916898714153 17342763885362937674035615)
  ·
    refine ⟨26014145828044406511053423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17342763885362937674035615 26014145828044406511053423)
    ·
      refine ⟨39021218742066609766580135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26014145828044406511053423 39021218742066609766580135)
      ·
        refine ⟨58531828113099914649870203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39021218742066609766580135 58531828113099914649870203)
        ·
          refine ⟨87797742169649871974805305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58531828113099914649870203 87797742169649871974805305)
          ·
            refine ⟨65848306627237403981103979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87797742169649871974805305 65848306627237403981103979)
            ·
              refine ⟨98772459940856105971655969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65848306627237403981103979 98772459940856105971655969)
              ·
                refine ⟨74079344955642079478741977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98772459940856105971655969 74079344955642079478741977)
                ·
                  refine ⟨55559508716731559609056483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74079344955642079478741977 55559508716731559609056483)
                  ·
                    refine ⟨83339263075097339413584725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55559508716731559609056483 83339263075097339413584725)
                    ·
                      refine ⟨488315994580648473126473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 83339263075097339413584725 488315994580648473126473)
                      ·
                        rfl

theorem cell23_950992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 9].length) (baseStart_950992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_950992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_950992 prefixEnd_950992 := by exact prefixLift 950992
  have htrace : WordTrace (prefixWord ++ tailWord_950992) baseStart_950992 baseEnd_950992 := by
    simpa [prefixWord, tailWord_950992, baseEnd_950992] using wordTrace_append hprefix tailTrace_950992
  have hstable : (prefixWord ++ tailWord_950992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950992).length < 2 ^ (prefixWord ++ tailWord_950992).sum := by decide
  have hdescent : baseEnd_950992 < baseStart_950992 := by decide
  rcases family_descends (prefixWord ++ tailWord_950992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951059 : List Nat := [1, 1, 1, 2, 1, 3, 4, 3, 1, 6]
def baseStart_951059 : Nat := 118140960795 + 951059 * 2 ^ 59
def prefixEnd_951059 : Nat := 4983230072969 + 3 ^ 40 * 951059 * 2
def baseEnd_951059 : Nat := 162783465928166570329555

theorem tailTrace_951059 : CollatzResearch.WordTrace tailWord_951059 prefixEnd_951059 162783465928166570329555 := by
  unfold tailWord_951059
  simp only [CollatzResearch.WordTrace]
  refine ⟨34687971461483145790760231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23125314307655430527173487 34687971461483145790760231)
  ·
    refine ⟨52031957192224718686140347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34687971461483145790760231 52031957192224718686140347)
    ·
      refine ⟨78047935788337078029210521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52031957192224718686140347 78047935788337078029210521)
      ·
        refine ⟨58535951841252808521907891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78047935788337078029210521 58535951841252808521907891)
        ·
          refine ⟨87803927761879212782861837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58535951841252808521907891 87803927761879212782861837)
          ·
            refine ⟨32926472910704704793573189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87803927761879212782861837 32926472910704704793573189)
            ·
              refine ⟨6173713670757132148794973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32926472910704704793573189 6173713670757132148794973)
              ·
                refine ⟨2315142626533924555798115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6173713670757132148794973 2315142626533924555798115)
                ·
                  refine ⟨3472713939800886833697173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2315142626533924555798115 3472713939800886833697173)
                  ·
                    refine ⟨162783465928166570329555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3472713939800886833697173 162783465928166570329555)
                    ·
                      rfl

theorem cell23_951059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 6].length) (baseStart_951059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951059 prefixEnd_951059 := by exact prefixLift 951059
  have htrace : WordTrace (prefixWord ++ tailWord_951059) baseStart_951059 baseEnd_951059 := by
    simpa [prefixWord, tailWord_951059, baseEnd_951059] using wordTrace_append hprefix tailTrace_951059
  have hstable : (prefixWord ++ tailWord_951059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951059).length < 2 ^ (prefixWord ++ tailWord_951059).sum := by decide
  have hdescent : baseEnd_951059 < baseStart_951059 := by decide
  rcases family_descends (prefixWord ++ tailWord_951059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951066 : List Nat := [3, 1, 1, 3, 2, 1, 3, 1, 3, 1, 4]
def baseStart_951066 : Nat := 118140960795 + 951066 * 2 ^ 59
def prefixEnd_951066 : Nat := 4983230072969 + 3 ^ 40 * 951066 * 2
def baseEnd_951066 : Nat := 488353992149081183601133

theorem tailTrace_951066 : CollatzResearch.WordTrace tailWord_951066 prefixEnd_951066 488353992149081183601133 := by
  unfold tailWord_951066
  simp only [CollatzResearch.WordTrace]
  refine ⟨8672056693114446496566263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23125484514971857324176701 8672056693114446496566263)
  ·
    refine ⟨13008085039671669744849395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8672056693114446496566263 13008085039671669744849395)
    ·
      refine ⟨19512127559507504617274093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13008085039671669744849395 19512127559507504617274093)
      ·
        refine ⟨7317047834815314231477785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19512127559507504617274093 7317047834815314231477785)
        ·
          refine ⟨5487785876111485673608339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7317047834815314231477785 5487785876111485673608339)
          ·
            refine ⟨8231678814167228510412509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5487785876111485673608339 8231678814167228510412509)
            ·
              refine ⟨3086879555312710691404691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8231678814167228510412509 3086879555312710691404691)
              ·
                refine ⟨4630319332969066037107037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3086879555312710691404691 4630319332969066037107037)
                ·
                  refine ⟨1736369749863399763915139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4630319332969066037107037 1736369749863399763915139)
                  ·
                    refine ⟨2604554624795099645872709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1736369749863399763915139 2604554624795099645872709)
                    ·
                      refine ⟨488353992149081183601133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2604554624795099645872709 488353992149081183601133)
                      ·
                        rfl

theorem cell23_951066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_951066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951066 prefixEnd_951066 := by exact prefixLift 951066
  have htrace : WordTrace (prefixWord ++ tailWord_951066) baseStart_951066 baseEnd_951066 := by
    simpa [prefixWord, tailWord_951066, baseEnd_951066] using wordTrace_append hprefix tailTrace_951066
  have hstable : (prefixWord ++ tailWord_951066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951066).length < 2 ^ (prefixWord ++ tailWord_951066).sum := by decide
  have hdescent : baseEnd_951066 < baseStart_951066 := by decide
  rcases family_descends (prefixWord ++ tailWord_951066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951093 : List Nat := [1, 3, 3, 1, 3, 1, 1, 4, 2, 4]
def baseStart_951093 : Nat := 118140960795 + 951093 * 2 ^ 59
def prefixEnd_951093 : Nat := 4983230072969 + 3 ^ 40 * 951093 * 2
def baseEnd_951093 : Nat := 162789285375584192654503

theorem tailTrace_951093 : CollatzResearch.WordTrace tailWord_951093 prefixEnd_951093 162789285375584192654503 := by
  unfold tailWord_951093
  simp only [CollatzResearch.WordTrace]
  refine ⟨34689211543359969597497933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23126141028906646398331955 34689211543359969597497933)
  ·
    refine ⟨13008454328759988599061725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34689211543359969597497933 13008454328759988599061725)
    ·
      refine ⟨4878170373284995724648147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13008454328759988599061725 4878170373284995724648147)
      ·
        refine ⟨7317255559927493586972221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4878170373284995724648147 7317255559927493586972221)
        ·
          refine ⟨2743970834972810095114583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7317255559927493586972221 2743970834972810095114583)
          ·
            refine ⟨4115956252459215142671875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2743970834972810095114583 4115956252459215142671875)
            ·
              refine ⟨6173934378688822714007813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4115956252459215142671875 6173934378688822714007813)
              ·
                refine ⟨1157612696004154258876465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6173934378688822714007813 1157612696004154258876465)
                ·
                  refine ⟨868209522003115694157349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1157612696004154258876465 868209522003115694157349)
                  ·
                    refine ⟨162789285375584192654503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 868209522003115694157349 162789285375584192654503)
                    ·
                      rfl

theorem cell23_951093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_951093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951093 prefixEnd_951093 := by exact prefixLift 951093
  have htrace : WordTrace (prefixWord ++ tailWord_951093) baseStart_951093 baseEnd_951093 := by
    simpa [prefixWord, tailWord_951093, baseEnd_951093] using wordTrace_append hprefix tailTrace_951093
  have hstable : (prefixWord ++ tailWord_951093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951093).length < 2 ^ (prefixWord ++ tailWord_951093).sum := by decide
  have hdescent : baseEnd_951093 < baseStart_951093 := by decide
  rcases family_descends (prefixWord ++ tailWord_951093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951094 : List Nat := [5, 1, 2, 2, 2, 1, 1, 4, 1, 1, 3]
def baseStart_951094 : Nat := 118140960795 + 951094 * 2 ^ 59
def prefixEnd_951094 : Nat := 4983230072969 + 3 ^ 40 * 951094 * 2
def baseEnd_951094 : Nat := 488368369607407074051005

theorem tailTrace_951094 : CollatzResearch.WordTrace tailWord_951094 prefixEnd_951094 488368369607407074051005 := by
  unfold tailWord_951094
  simp only [CollatzResearch.WordTrace]
  refine ⟨2168078001022271673017771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23126165344237564512189557 2168078001022271673017771)
  ·
    refine ⟨3252117001533407509526657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2168078001022271673017771 3252117001533407509526657)
    ·
      refine ⟨2439087751150055632144993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3252117001533407509526657 2439087751150055632144993)
      ·
        refine ⟨1829315813362541724108745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2439087751150055632144993 1829315813362541724108745)
        ·
          refine ⟨1371986860021906293081559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1829315813362541724108745 1371986860021906293081559)
          ·
            refine ⟨2057980290032859439622339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1371986860021906293081559 2057980290032859439622339)
            ·
              refine ⟨3086970435049289159433509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2057980290032859439622339 3086970435049289159433509)
              ·
                refine ⟨578806956571741717393783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3086970435049289159433509 578806956571741717393783)
                ·
                  refine ⟨868210434857612576090675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 578806956571741717393783 868210434857612576090675)
                  ·
                    refine ⟨1302315652286418864136013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 868210434857612576090675 1302315652286418864136013)
                    ·
                      refine ⟨488368369607407074051005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1302315652286418864136013 488368369607407074051005)
                      ·
                        rfl

theorem cell23_951094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_951094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951094 prefixEnd_951094 := by exact prefixLift 951094
  have htrace : WordTrace (prefixWord ++ tailWord_951094) baseStart_951094 baseEnd_951094 := by
    simpa [prefixWord, tailWord_951094, baseEnd_951094] using wordTrace_append hprefix tailTrace_951094
  have hstable : (prefixWord ++ tailWord_951094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951094).length < 2 ^ (prefixWord ++ tailWord_951094).sum := by decide
  have hdescent : baseEnd_951094 < baseStart_951094 := by decide
  rcases family_descends (prefixWord ++ tailWord_951094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951224 : List Nat := [2, 1, 2, 1, 2, 6, 2, 1, 2, 2, 2]
def baseStart_951224 : Nat := 118140960795 + 951224 * 2 ^ 59
def prefixEnd_951224 : Nat := 4983230072969 + 3 ^ 40 * 951224 * 2
def baseEnd_951224 : Nat := 488435122092491565425407

theorem tailTrace_951224 : CollatzResearch.WordTrace tailWord_951224 prefixEnd_951224 488435122092491565425407 := by
  unfold tailWord_951224
  simp only [CollatzResearch.WordTrace]
  refine ⟨17346994752942689485258363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23129326337256919313677817 17346994752942689485258363)
  ·
    refine ⟨26020492129414034227887545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17346994752942689485258363 26020492129414034227887545)
    ·
      refine ⟨19515369097060525670915659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26020492129414034227887545 19515369097060525670915659)
      ·
        refine ⟨29273053645590788506373489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19515369097060525670915659 29273053645590788506373489)
        ·
          refine ⟨21954790234193091379780117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29273053645590788506373489 21954790234193091379780117)
          ·
            refine ⟨1029130792227801158427193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21954790234193091379780117 1029130792227801158427193)
            ·
              refine ⟨771848094170850868820395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1029130792227801158427193 771848094170850868820395)
              ·
                refine ⟨1157772141256276303230593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 771848094170850868820395 1157772141256276303230593)
                ·
                  refine ⟨868329105942207227422945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1157772141256276303230593 868329105942207227422945)
                  ·
                    refine ⟨651246829456655420567209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 868329105942207227422945 651246829456655420567209)
                    ·
                      refine ⟨488435122092491565425407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 651246829456655420567209 488435122092491565425407)
                      ·
                        rfl

theorem cell23_951224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 2, 2, 2].length) (baseStart_951224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951224 prefixEnd_951224 := by exact prefixLift 951224
  have htrace : WordTrace (prefixWord ++ tailWord_951224) baseStart_951224 baseEnd_951224 := by
    simpa [prefixWord, tailWord_951224, baseEnd_951224] using wordTrace_append hprefix tailTrace_951224
  have hstable : (prefixWord ++ tailWord_951224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951224).length < 2 ^ (prefixWord ++ tailWord_951224).sum := by decide
  have hdescent : baseEnd_951224 < baseStart_951224 := by decide
  rcases family_descends (prefixWord ++ tailWord_951224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951226 : List Nat := [3, 1, 1, 1, 2, 1, 3, 2, 4, 5]
def baseStart_951226 : Nat := 118140960795 + 951226 * 2 ^ 59
def prefixEnd_951226 : Nat := 4983230072969 + 3 ^ 40 * 951226 * 2
def baseEnd_951226 : Nat := 162812049684600185866799

theorem tailTrace_951226 : CollatzResearch.WordTrace tailWord_951226 prefixEnd_951226 162812049684600185866799 := by
  unfold tailWord_951226
  simp only [CollatzResearch.WordTrace]
  refine ⟨8673515612969533328022383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23129374967918755541393021 8673515612969533328022383)
  ·
    refine ⟨13010273419454299992033575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8673515612969533328022383 13010273419454299992033575)
    ·
      refine ⟨19515410129181449988050363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13010273419454299992033575 19515410129181449988050363)
      ·
        refine ⟨29273115193772174982075545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19515410129181449988050363 29273115193772174982075545)
        ·
          refine ⟨21954836395329131236556659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29273115193772174982075545 21954836395329131236556659)
          ·
            refine ⟨32932254592993696854834989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21954836395329131236556659 32932254592993696854834989)
            ·
              refine ⟨12349595472372636320563121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32932254592993696854834989 12349595472372636320563121)
              ·
                refine ⟨9262196604279477240422341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12349595472372636320563121 9262196604279477240422341)
                ·
                  refine ⟨1736661863302401982579189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9262196604279477240422341 1736661863302401982579189)
                  ·
                    refine ⟨162812049684600185866799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1736661863302401982579189 162812049684600185866799)
                    ·
                      rfl

theorem cell23_951226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 4, 5].length) (baseStart_951226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951226 prefixEnd_951226 := by exact prefixLift 951226
  have htrace : WordTrace (prefixWord ++ tailWord_951226) baseStart_951226 baseEnd_951226 := by
    simpa [prefixWord, tailWord_951226, baseEnd_951226] using wordTrace_append hprefix tailTrace_951226
  have hstable : (prefixWord ++ tailWord_951226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951226).length < 2 ^ (prefixWord ++ tailWord_951226).sum := by decide
  have hdescent : baseEnd_951226 < baseStart_951226 := by decide
  rcases family_descends (prefixWord ++ tailWord_951226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951243 : List Nat := [1, 1, 1, 1, 3, 6, 2, 1, 2, 5]
def baseStart_951243 : Nat := 118140960795 + 951243 * 2 ^ 59
def prefixEnd_951243 : Nat := 4983230072969 + 3 ^ 40 * 951243 * 2
def baseEnd_951243 : Nat := 162814959408308997029273

theorem tailTrace_951243 : CollatzResearch.WordTrace tailWord_951243 prefixEnd_951243 162814959408308997029273 := by
  unfold tailWord_951243
  simp only [CollatzResearch.WordTrace]
  refine ⟨34694682492816545215458383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23129788328544363476972255 34694682492816545215458383)
  ·
    refine ⟨52042023739224817823187575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34694682492816545215458383 52042023739224817823187575)
    ·
      refine ⟨78063035608837226734781363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52042023739224817823187575 78063035608837226734781363)
      ·
        refine ⟨117094553413255840102172045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78063035608837226734781363 117094553413255840102172045)
        ·
          refine ⟨43910457529970940038314517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117094553413255840102172045 43910457529970940038314517)
          ·
            refine ⟨2058302696717387814295993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43910457529970940038314517 2058302696717387814295993)
            ·
              refine ⟨1543727022538040860721995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2058302696717387814295993 1543727022538040860721995)
              ·
                refine ⟨2315590533807061291082993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1543727022538040860721995 2315590533807061291082993)
                ·
                  refine ⟨1736692900355295968312245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2315590533807061291082993 1736692900355295968312245)
                  ·
                    refine ⟨162814959408308997029273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1736692900355295968312245 162814959408308997029273)
                    ·
                      rfl

theorem cell23_951243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 5].length) (baseStart_951243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951243 prefixEnd_951243 := by exact prefixLift 951243
  have htrace : WordTrace (prefixWord ++ tailWord_951243) baseStart_951243 baseEnd_951243 := by
    simpa [prefixWord, tailWord_951243, baseEnd_951243] using wordTrace_append hprefix tailTrace_951243
  have hstable : (prefixWord ++ tailWord_951243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951243).length < 2 ^ (prefixWord ++ tailWord_951243).sum := by decide
  have hdescent : baseEnd_951243 < baseStart_951243 := by decide
  rcases family_descends (prefixWord ++ tailWord_951243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951276 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 4]
def baseStart_951276 : Nat := 118140960795 + 951276 * 2 ^ 59
def prefixEnd_951276 : Nat := 4983230072969 + 3 ^ 40 * 951276 * 2
def baseEnd_951276 : Nat := 488461823086525361975167

theorem tailTrace_951276 : CollatzResearch.WordTrace tailWord_951276 prefixEnd_951276 488461823086525361975167 := by
  unfold tailWord_951276
  simp only [CollatzResearch.WordTrace]
  refine ⟨17347943050848495925704841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23130590734464661234273121 17347943050848495925704841)
  ·
    refine ⟨13010957288136371944278631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17347943050848495925704841 13010957288136371944278631)
    ·
      refine ⟨19516435932204557916417947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13010957288136371944278631 19516435932204557916417947)
      ·
        refine ⟨29274653898306836874626921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19516435932204557916417947 29274653898306836874626921)
        ·
          refine ⟨21955990423730127655970191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29274653898306836874626921 21955990423730127655970191)
          ·
            refine ⟨32933985635595191483955287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21955990423730127655970191 32933985635595191483955287)
            ·
              refine ⟨49400978453392787225932931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32933985635595191483955287 49400978453392787225932931)
              ·
                refine ⟨74101467680089180838899397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49400978453392787225932931 74101467680089180838899397)
                ·
                  refine ⟨13894025190016721407293637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74101467680089180838899397 13894025190016721407293637)
                  ·
                    refine ⟨2605129723128135263867557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13894025190016721407293637 2605129723128135263867557)
                    ·
                      refine ⟨488461823086525361975167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2605129723128135263867557 488461823086525361975167)
                      ·
                        rfl

theorem cell23_951276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_951276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951276 prefixEnd_951276 := by exact prefixLift 951276
  have htrace : WordTrace (prefixWord ++ tailWord_951276) baseStart_951276 baseEnd_951276 := by
    simpa [prefixWord, tailWord_951276, baseEnd_951276] using wordTrace_append hprefix tailTrace_951276
  have hstable : (prefixWord ++ tailWord_951276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951276).length < 2 ^ (prefixWord ++ tailWord_951276).sum := by decide
  have hdescent : baseEnd_951276 < baseStart_951276 := by decide
  rcases family_descends (prefixWord ++ tailWord_951276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951294 : List Nat := [4, 2, 2, 2, 3, 1, 1, 1, 2, 5]
def baseStart_951294 : Nat := 118140960795 + 951294 * 2 ^ 59
def prefixEnd_951294 : Nat := 4983230072969 + 3 ^ 40 * 951294 * 2
def baseEnd_951294 : Nat := 162823688579435430516695

theorem tailTrace_951294 : CollatzResearch.WordTrace tailWord_951294 prefixEnd_951294 162823688579435430516695 := by
  unfold tailWord_951294
  simp only [CollatzResearch.WordTrace]
  refine ⟨4337067826953972615695617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23131028410421187283709957 4337067826953972615695617)
  ·
    refine ⟨3252800870215479461771713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4337067826953972615695617 3252800870215479461771713)
    ·
      refine ⟨2439600652661609596328785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3252800870215479461771713 2439600652661609596328785)
      ·
        refine ⟨1829700489496207197246589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2439600652661609596328785 1829700489496207197246589)
        ·
          refine ⟨686137683561077698967471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1829700489496207197246589 686137683561077698967471)
          ·
            refine ⟨1029206525341616548451207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686137683561077698967471 1029206525341616548451207)
            ·
              refine ⟨1543809788012424822676811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1029206525341616548451207 1543809788012424822676811)
              ·
                refine ⟨2315714682018637234015217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1543809788012424822676811 2315714682018637234015217)
                ·
                  refine ⟨1736786011513977925511413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2315714682018637234015217 1736786011513977925511413)
                  ·
                    refine ⟨162823688579435430516695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1736786011513977925511413 162823688579435430516695)
                    ·
                      rfl

theorem cell23_951294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_951294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951294 prefixEnd_951294 := by exact prefixLift 951294
  have htrace : WordTrace (prefixWord ++ tailWord_951294) baseStart_951294 baseEnd_951294 := by
    simpa [prefixWord, tailWord_951294, baseEnd_951294] using wordTrace_append hprefix tailTrace_951294
  have hstable : (prefixWord ++ tailWord_951294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951294).length < 2 ^ (prefixWord ++ tailWord_951294).sum := by decide
  have hdescent : baseEnd_951294 < baseStart_951294 := by decide
  rcases family_descends (prefixWord ++ tailWord_951294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951307 : List Nat := [1, 1, 1, 1, 6, 3, 2, 3, 1, 4]
def baseStart_951307 : Nat := 118140960795 + 951307 * 2 ^ 59
def prefixEnd_951307 : Nat := 4983230072969 + 3 ^ 40 * 951307 * 2
def baseEnd_951307 : Nat := 162825913662271580229175

theorem tailTrace_951307 : CollatzResearch.WordTrace tailWord_951307 prefixEnd_951307 162825913662271580229175 := by
  unfold tailWord_951307
  simp only [CollatzResearch.WordTrace]
  refine ⟨34697016764584684145788175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23131344509723122763858783 34697016764584684145788175)
  ·
    refine ⟨52045525146877026218682263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34697016764584684145788175 52045525146877026218682263)
    ·
      refine ⟨78068287720315539328023395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52045525146877026218682263 78068287720315539328023395)
      ·
        refine ⟨117102431580473308992035093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78068287720315539328023395 117102431580473308992035093)
        ·
          refine ⟨5489176480334686359001645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 117102431580473308992035093 5489176480334686359001645)
          ·
            refine ⟨2058441180125507384625617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5489176480334686359001645 2058441180125507384625617)
            ·
              refine ⟨1543830885094130538469213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2058441180125507384625617 1543830885094130538469213)
              ·
                refine ⟨578936581910298951925955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1543830885094130538469213 578936581910298951925955)
                ·
                  refine ⟨868404872865448427888933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 578936581910298951925955 868404872865448427888933)
                  ·
                    refine ⟨162825913662271580229175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 868404872865448427888933 162825913662271580229175)
                    ·
                      rfl

theorem cell23_951307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 3, 1, 4].length) (baseStart_951307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951307 prefixEnd_951307 := by exact prefixLift 951307
  have htrace : WordTrace (prefixWord ++ tailWord_951307) baseStart_951307 baseEnd_951307 := by
    simpa [prefixWord, tailWord_951307, baseEnd_951307] using wordTrace_append hprefix tailTrace_951307
  have hstable : (prefixWord ++ tailWord_951307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951307).length < 2 ^ (prefixWord ++ tailWord_951307).sum := by decide
  have hdescent : baseEnd_951307 < baseStart_951307 := by decide
  rcases family_descends (prefixWord ++ tailWord_951307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951320 : List Nat := [2, 1, 2, 3, 2, 4, 1, 2, 6]
def baseStart_951320 : Nat := 118140960795 + 951320 * 2 ^ 59
def prefixEnd_951320 : Nat := 4983230072969 + 3 ^ 40 * 951320 * 2
def baseEnd_951320 : Nat := 54276046248369243313885

theorem tailTrace_951320 : CollatzResearch.WordTrace tailWord_951320 prefixEnd_951320 54276046248369243313885 := by
  unfold tailWord_951320
  simp only [CollatzResearch.WordTrace]
  refine ⟨17348745456768793683005707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23131660609025058244007609 17348745456768793683005707)
  ·
    refine ⟨26023118185153190524508561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17348745456768793683005707 26023118185153190524508561)
    ·
      refine ⟨19517338638864892893381421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26023118185153190524508561 19517338638864892893381421)
      ·
        refine ⟨7319001989574334835018033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19517338638864892893381421 7319001989574334835018033)
        ·
          refine ⟨5489251492180751126263525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7319001989574334835018033 5489251492180751126263525)
          ·
            refine ⟨1029234654783890836174411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5489251492180751126263525 1029234654783890836174411)
            ·
              refine ⟨1543851982175836254261617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1029234654783890836174411 1543851982175836254261617)
              ·
                refine ⟨1157888986631877190696213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1543851982175836254261617 1157888986631877190696213)
                ·
                  refine ⟨54276046248369243313885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1157888986631877190696213 54276046248369243313885)
                  ·
                    rfl

theorem cell23_951320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 6].length) (baseStart_951320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951320 prefixEnd_951320 := by exact prefixLift 951320
  have htrace : WordTrace (prefixWord ++ tailWord_951320) baseStart_951320 baseEnd_951320 := by
    simpa [prefixWord, tailWord_951320, baseEnd_951320] using wordTrace_append hprefix tailTrace_951320
  have hstable : (prefixWord ++ tailWord_951320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951320).length < 2 ^ (prefixWord ++ tailWord_951320).sum := by decide
  have hdescent : baseEnd_951320 < baseStart_951320 := by decide
  rcases family_descends (prefixWord ++ tailWord_951320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951363 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 6, 4]
def baseStart_951363 : Nat := 118140960795 + 951363 * 2 ^ 59
def prefixEnd_951363 : Nat := 4983230072969 + 3 ^ 40 * 951363 * 2
def baseEnd_951363 : Nat := 162835498634488840529089

theorem tailTrace_951363 : CollatzResearch.WordTrace tailWord_951363 prefixEnd_951363 162835498634488840529089 := by
  unfold tailWord_951363
  simp only [CollatzResearch.WordTrace]
  refine ⟨34699059252381805709826743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23132706168254537139884495 34699059252381805709826743)
  ·
    refine ⟨52048588878572708564740115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34699059252381805709826743 52048588878572708564740115)
    ·
      refine ⟨78072883317859062847110173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52048588878572708564740115 78072883317859062847110173)
      ·
        refine ⟨29277331244197148567666315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78072883317859062847110173 29277331244197148567666315)
        ·
          refine ⟨43915996866295722851499473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29277331244197148567666315 43915996866295722851499473)
          ·
            refine ⟨32936997649721792138624605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43915996866295722851499473 32936997649721792138624605)
            ·
              refine ⟨12351374118645672051984227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32936997649721792138624605 12351374118645672051984227)
              ·
                refine ⟨18527061177968508077976341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12351374118645672051984227 18527061177968508077976341)
                ·
                  refine ⟨868455992717273816155141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 18527061177968508077976341 868455992717273816155141)
                  ·
                    refine ⟨162835498634488840529089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 868455992717273816155141 162835498634488840529089)
                    ·
                      rfl

theorem cell23_951363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 6, 4].length) (baseStart_951363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951363 prefixEnd_951363 := by exact prefixLift 951363
  have htrace : WordTrace (prefixWord ++ tailWord_951363) baseStart_951363 baseEnd_951363 := by
    simpa [prefixWord, tailWord_951363, baseEnd_951363] using wordTrace_append hprefix tailTrace_951363
  have hstable : (prefixWord ++ tailWord_951363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951363).length < 2 ^ (prefixWord ++ tailWord_951363).sum := by decide
  have hdescent : baseEnd_951363 < baseStart_951363 := by decide
  rcases family_descends (prefixWord ++ tailWord_951363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951370 : List Nat := [3, 1, 2, 1, 1, 2, 4, 3, 1, 1, 4]
def baseStart_951370 : Nat := 118140960795 + 951370 * 2 ^ 59
def prefixEnd_951370 : Nat := 4983230072969 + 3 ^ 40 * 951370 * 2
def baseEnd_951370 : Nat := 488510090268047994199735

theorem tailTrace_951370 : CollatzResearch.WordTrace tailWord_951370 prefixEnd_951370 488510090268047994199735 := by
  unfold tailWord_951370
  simp only [CollatzResearch.WordTrace]
  refine ⟨8674828640839111476332891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23132876375570963936887709 8674828640839111476332891)
  ·
    refine ⟨13012242961258667214499337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8674828640839111476332891 13012242961258667214499337)
    ·
      refine ⟨9759182220944000410874503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13012242961258667214499337 9759182220944000410874503)
      ·
        refine ⟨14638773331416000616311755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9759182220944000410874503 14638773331416000616311755)
        ·
          refine ⟨21958159997124000924467633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14638773331416000616311755 21958159997124000924467633)
          ·
            refine ⟨16468619997843000693350725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21958159997124000924467633 16468619997843000693350725)
            ·
              refine ⟨3087866249595562630003261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16468619997843000693350725 3087866249595562630003261)
              ·
                refine ⟨1157949843598335986251223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3087866249595562630003261 1157949843598335986251223)
                ·
                  refine ⟨1736924765397503979376835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1157949843598335986251223 1736924765397503979376835)
                  ·
                    refine ⟨2605387148096255969065253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1736924765397503979376835 2605387148096255969065253)
                    ·
                      refine ⟨488510090268047994199735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2605387148096255969065253 488510090268047994199735)
                      ·
                        rfl

theorem cell23_951370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 1, 1, 4].length) (baseStart_951370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951370 prefixEnd_951370 := by exact prefixLift 951370
  have htrace : WordTrace (prefixWord ++ tailWord_951370) baseStart_951370 baseEnd_951370 := by
    simpa [prefixWord, tailWord_951370, baseEnd_951370] using wordTrace_append hprefix tailTrace_951370
  have hstable : (prefixWord ++ tailWord_951370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951370).length < 2 ^ (prefixWord ++ tailWord_951370).sum := by decide
  have hdescent : baseEnd_951370 < baseStart_951370 := by decide
  rcases family_descends (prefixWord ++ tailWord_951370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951380 : List Nat := [2, 4, 1, 1, 1, 1, 4, 1, 4, 4]
def baseStart_951380 : Nat := 118140960795 + 951380 * 2 ^ 59
def prefixEnd_951380 : Nat := 4983230072969 + 3 ^ 40 * 951380 * 2
def baseEnd_951380 : Nat := 162838408358197651691563

theorem tailTrace_951380 : CollatzResearch.WordTrace tailWord_951380 prefixEnd_951380 162838408358197651691563 := by
  unfold tailWord_951380
  simp only [CollatzResearch.WordTrace]
  refine ⟨17349839646660108806597797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23133119528880145075463729 17349839646660108806597797)
  ·
    refine ⟨3253094933748770401237087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17349839646660108806597797 3253094933748770401237087)
    ·
      refine ⟨4879642400623155601855631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3253094933748770401237087 4879642400623155601855631)
      ·
        refine ⟨7319463600934733402783447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4879642400623155601855631 7319463600934733402783447)
        ·
          refine ⟨10979195401402100104175171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7319463600934733402783447 10979195401402100104175171)
          ·
            refine ⟨16468793102103150156262757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10979195401402100104175171 16468793102103150156262757)
            ·
              refine ⟨3087898706644340654299267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16468793102103150156262757 3087898706644340654299267)
              ·
                refine ⟨4631848059966510981448901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3087898706644340654299267 4631848059966510981448901)
                ·
                  refine ⟨868471511243720809021669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4631848059966510981448901 868471511243720809021669)
                  ·
                    refine ⟨162838408358197651691563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 868471511243720809021669 162838408358197651691563)
                    ·
                      rfl

theorem cell23_951380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_951380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951380 prefixEnd_951380 := by exact prefixLift 951380
  have htrace : WordTrace (prefixWord ++ tailWord_951380) baseStart_951380 baseEnd_951380 := by
    simpa [prefixWord, tailWord_951380, baseEnd_951380] using wordTrace_append hprefix tailTrace_951380
  have hstable : (prefixWord ++ tailWord_951380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951380).length < 2 ^ (prefixWord ++ tailWord_951380).sum := by decide
  have hdescent : baseEnd_951380 < baseStart_951380 := by decide
  rcases family_descends (prefixWord ++ tailWord_951380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951403 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 7, 3, 3]
def baseStart_951403 : Nat := 118140960795 + 951403 * 2 ^ 59
def prefixEnd_951403 : Nat := 4983230072969 + 3 ^ 40 * 951403 * 2
def baseEnd_951403 : Nat := 488527035129646365087083

theorem tailTrace_951403 : CollatzResearch.WordTrace tailWord_951403 prefixEnd_951403 488527035129646365087083 := by
  unfold tailWord_951403
  simp only [CollatzResearch.WordTrace]
  refine ⟨34700518172236892541282863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23133678781491261694188575 34700518172236892541282863)
  ·
    refine ⟨52050777258355338811924295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34700518172236892541282863 52050777258355338811924295)
    ·
      refine ⟨78076165887533008217886443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52050777258355338811924295 78076165887533008217886443)
      ·
        refine ⟨117114248831299512326829665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78076165887533008217886443 117114248831299512326829665)
        ·
          refine ⟨87835686623474634245122249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117114248831299512326829665 87835686623474634245122249)
          ·
            refine ⟨65876764967605975683841687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87835686623474634245122249 65876764967605975683841687)
            ·
              refine ⟨98815147451408963525762531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65876764967605975683841687 98815147451408963525762531)
              ·
                refine ⟨148222721177113445288643797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98815147451408963525762531 148222721177113445288643797)
                ·
                  refine ⟨3473970027588596373952589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 148222721177113445288643797 3473970027588596373952589)
                  ·
                    refine ⟨1302738760345723640232221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3473970027588596373952589 1302738760345723640232221)
                    ·
                      refine ⟨488527035129646365087083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1302738760345723640232221 488527035129646365087083)
                      ·
                        rfl

theorem cell23_951403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 3, 3].length) (baseStart_951403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951403 prefixEnd_951403 := by exact prefixLift 951403
  have htrace : WordTrace (prefixWord ++ tailWord_951403) baseStart_951403 baseEnd_951403 := by
    simpa [prefixWord, tailWord_951403, baseEnd_951403] using wordTrace_append hprefix tailTrace_951403
  have hstable : (prefixWord ++ tailWord_951403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951403).length < 2 ^ (prefixWord ++ tailWord_951403).sum := by decide
  have hdescent : baseEnd_951403 < baseStart_951403 := by decide
  rcases family_descends (prefixWord ++ tailWord_951403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951420 : List Nat := [2, 2, 2, 1, 1, 3, 3, 2, 1, 3, 3]
def baseStart_951420 : Nat := 118140960795 + 951420 * 2 ^ 59
def prefixEnd_951420 : Nat := 4983230072969 + 3 ^ 40 * 951420 * 2
def baseEnd_951420 : Nat := 488535764300772798574505

theorem tailTrace_951420 : CollatzResearch.WordTrace tailWord_951420 prefixEnd_951420 488535764300772798574505 := by
  unfold tailWord_951420
  simp only [CollatzResearch.WordTrace]
  refine ⟨17350569106587652222325857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23134092142116869629767809 17350569106587652222325857)
  ·
    refine ⟨13012926829940739166744393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17350569106587652222325857 13012926829940739166744393)
    ·
      refine ⟨9759695122455554375058295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13012926829940739166744393 9759695122455554375058295)
      ·
        refine ⟨14639542683683331562587443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9759695122455554375058295 14639542683683331562587443)
        ·
          refine ⟨21959314025524997343881165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14639542683683331562587443 21959314025524997343881165)
          ·
            refine ⟨8234742759571874003955437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21959314025524997343881165 8234742759571874003955437)
            ·
              refine ⟨3088028534839452751483289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8234742759571874003955437 3088028534839452751483289)
              ·
                refine ⟨2316021401129589563612467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3088028534839452751483289 2316021401129589563612467)
                ·
                  refine ⟨3474032101694384345418701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2316021401129589563612467 3474032101694384345418701)
                  ·
                    refine ⟨1302762038135394129532013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3474032101694384345418701 1302762038135394129532013)
                    ·
                      refine ⟨488535764300772798574505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1302762038135394129532013 488535764300772798574505)
                      ·
                        rfl

theorem cell23_951420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_951420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951420 prefixEnd_951420 := by exact prefixLift 951420
  have htrace : WordTrace (prefixWord ++ tailWord_951420) baseStart_951420 baseEnd_951420 := by
    simpa [prefixWord, tailWord_951420, baseEnd_951420] using wordTrace_append hprefix tailTrace_951420
  have hstable : (prefixWord ++ tailWord_951420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951420).length < 2 ^ (prefixWord ++ tailWord_951420).sum := by decide
  have hdescent : baseEnd_951420 < baseStart_951420 := by decide
  rcases family_descends (prefixWord ++ tailWord_951420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951438 : List Nat := [4, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2]
def baseStart_951438 : Nat := 118140960795 + 951438 * 2 ^ 59
def prefixEnd_951438 : Nat := 4983230072969 + 3 ^ 40 * 951438 * 2
def baseEnd_951438 : Nat := 488545006952553728149423

theorem tailTrace_951438 : CollatzResearch.WordTrace tailWord_951438 prefixEnd_951438 488545006952553728149423 := by
  unfold tailWord_951438
  simp only [CollatzResearch.WordTrace]
  refine ⟨4337724340888761689850871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23134529818073395679204645 4337724340888761689850871)
  ·
    refine ⟨6506586511333142534776307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4337724340888761689850871 6506586511333142534776307)
    ·
      refine ⟨9759879766999713802164461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6506586511333142534776307 9759879766999713802164461)
      ·
        refine ⟨3659954912624892675811673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9759879766999713802164461 3659954912624892675811673)
        ·
          refine ⟨2744966184468669506858755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3659954912624892675811673 2744966184468669506858755)
          ·
            refine ⟨4117449276703004260288133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2744966184468669506858755 4117449276703004260288133)
            ·
              refine ⟨772021739381813298804025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4117449276703004260288133 772021739381813298804025)
              ·
                refine ⟨579016304536359974103019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 772021739381813298804025 579016304536359974103019)
                ·
                  refine ⟨868524456804539961154529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 579016304536359974103019 868524456804539961154529)
                  ·
                    refine ⟨651393342603404970865897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 868524456804539961154529 651393342603404970865897)
                    ·
                      refine ⟨488545006952553728149423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 651393342603404970865897 488545006952553728149423)
                      ·
                        rfl

theorem cell23_951438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_951438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951438 prefixEnd_951438 := by exact prefixLift 951438
  have htrace : WordTrace (prefixWord ++ tailWord_951438) baseStart_951438 baseEnd_951438 := by
    simpa [prefixWord, tailWord_951438, baseEnd_951438] using wordTrace_append hprefix tailTrace_951438
  have hstable : (prefixWord ++ tailWord_951438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951438).length < 2 ^ (prefixWord ++ tailWord_951438).sum := by decide
  have hdescent : baseEnd_951438 < baseStart_951438 := by decide
  rcases family_descends (prefixWord ++ tailWord_951438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951443 : List Nat := [1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 4]
def baseStart_951443 : Nat := 118140960795 + 951443 * 2 ^ 59
def prefixEnd_951443 : Nat := 4983230072969 + 3 ^ 40 * 951443 * 2
def baseEnd_951443 : Nat := 488547574355826208586899

theorem tailTrace_951443 : CollatzResearch.WordTrace tailWord_951443 prefixEnd_951443 488547574355826208586899 := by
  unfold tailWord_951443
  simp only [CollatzResearch.WordTrace]
  refine ⟨34701977092091979372738983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23134651394727986248492655 34701977092091979372738983)
  ·
    refine ⟨52052965638137969059108475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34701977092091979372738983 52052965638137969059108475)
    ·
      refine ⟨78079448457206953588662713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52052965638137969059108475 78079448457206953588662713)
      ·
        refine ⟨58559586342905215191497035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78079448457206953588662713 58559586342905215191497035)
        ·
          refine ⟨87839379514357822787245553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58559586342905215191497035 87839379514357822787245553)
          ·
            refine ⟨65879534635768367090434165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87839379514357822787245553 65879534635768367090434165)
            ·
              refine ⟨6176206372103284414728203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65879534635768367090434165 6176206372103284414728203)
              ·
                refine ⟨9264309558154926622092305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6176206372103284414728203 9264309558154926622092305)
                ·
                  refine ⟨6948232168616194966569229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9264309558154926622092305 6948232168616194966569229)
                  ·
                    refine ⟨2605587063231073112463461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6948232168616194966569229 2605587063231073112463461)
                    ·
                      refine ⟨488547574355826208586899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2605587063231073112463461 488547574355826208586899)
                      ·
                        rfl

theorem cell23_951443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 4].length) (baseStart_951443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951443 prefixEnd_951443 := by exact prefixLift 951443
  have htrace : WordTrace (prefixWord ++ tailWord_951443) baseStart_951443 baseEnd_951443 := by
    simpa [prefixWord, tailWord_951443, baseEnd_951443] using wordTrace_append hprefix tailTrace_951443
  have hstable : (prefixWord ++ tailWord_951443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951443).length < 2 ^ (prefixWord ++ tailWord_951443).sum := by decide
  have hdescent : baseEnd_951443 < baseStart_951443 := by decide
  rcases family_descends (prefixWord ++ tailWord_951443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951447 : List Nat := [1, 1, 3, 3, 3, 1, 1, 2, 3, 3, 2]
def baseStart_951447 : Nat := 118140960795 + 951447 * 2 ^ 59
def prefixEnd_951447 : Nat := 4983230072969 + 3 ^ 40 * 951447 * 2
def baseEnd_951447 : Nat := 488549628278444192936881

theorem tailTrace_951447 : CollatzResearch.WordTrace tailWord_951447 prefixEnd_951447 488549628278444192936881 := by
  unfold tailWord_951447
  simp only [CollatzResearch.WordTrace]
  refine ⟨34702122984077488055884595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23134748656051658703923063 34702122984077488055884595)
  ·
    refine ⟨52053184476116232083826893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34702122984077488055884595 52053184476116232083826893)
    ·
      refine ⟨19519944178543587031435085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52053184476116232083826893 19519944178543587031435085)
      ·
        refine ⟨7319979066953845136788157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19519944178543587031435085 7319979066953845136788157)
        ·
          refine ⟨2744992150107691926295559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7319979066953845136788157 2744992150107691926295559)
          ·
            refine ⟨4117488225161537889443339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2744992150107691926295559 4117488225161537889443339)
            ·
              refine ⟨6176232337742306834165009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4117488225161537889443339 6176232337742306834165009)
              ·
                refine ⟨4632174253306730125623757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6176232337742306834165009 4632174253306730125623757)
                ·
                  refine ⟨1737065344990023797108909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4632174253306730125623757 1737065344990023797108909)
                  ·
                    refine ⟨651399504371258923915841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1737065344990023797108909 651399504371258923915841)
                    ·
                      refine ⟨488549628278444192936881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 651399504371258923915841 488549628278444192936881)
                      ·
                        rfl

theorem cell23_951447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_951447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951447 prefixEnd_951447 := by exact prefixLift 951447
  have htrace : WordTrace (prefixWord ++ tailWord_951447) baseStart_951447 baseEnd_951447 := by
    simpa [prefixWord, tailWord_951447, baseEnd_951447] using wordTrace_append hprefix tailTrace_951447
  have hstable : (prefixWord ++ tailWord_951447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951447).length < 2 ^ (prefixWord ++ tailWord_951447).sum := by decide
  have hdescent : baseEnd_951447 < baseStart_951447 := by decide
  rcases family_descends (prefixWord ++ tailWord_951447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951454 : List Nat := [4, 3, 1, 1, 2, 2, 2, 1, 1, 3, 3]
def baseStart_951454 : Nat := 118140960795 + 951454 * 2 ^ 59
def prefixEnd_951454 : Nat := 4983230072969 + 3 ^ 40 * 951454 * 2
def baseEnd_951454 : Nat := 488553222643025665549349

theorem tailTrace_951454 : CollatzResearch.WordTrace tailWord_951454 prefixEnd_951454 488553222643025665549349 := by
  unfold tailWord_951454
  simp only [CollatzResearch.WordTrace]
  refine ⟨4337797286881516031423677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23134918863368085500926277 4337797286881516031423677)
  ·
    refine ⟨1626673982580568511783879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4337797286881516031423677 1626673982580568511783879)
    ·
      refine ⟨2440010973870852767675819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1626673982580568511783879 2440010973870852767675819)
      ·
        refine ⟨3660016460806279151513729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2440010973870852767675819 3660016460806279151513729)
        ·
          refine ⟨2745012345604709363635297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3660016460806279151513729 2745012345604709363635297)
          ·
            refine ⟨2058759259203532022726473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2745012345604709363635297 2058759259203532022726473)
            ·
              refine ⟨1544069444402649017044855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2058759259203532022726473 1544069444402649017044855)
              ·
                refine ⟨2316104166603973525567283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1544069444402649017044855 2316104166603973525567283)
                ·
                  refine ⟨3474156249905960288350925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2316104166603973525567283 3474156249905960288350925)
                  ·
                    refine ⟨1302808593714735108131597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3474156249905960288350925 1302808593714735108131597)
                    ·
                      refine ⟨488553222643025665549349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1302808593714735108131597 488553222643025665549349)
                      ·
                        rfl

theorem cell23_951454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_951454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951454 prefixEnd_951454 := by exact prefixLift 951454
  have htrace : WordTrace (prefixWord ++ tailWord_951454) baseStart_951454 baseEnd_951454 := by
    simpa [prefixWord, tailWord_951454, baseEnd_951454] using wordTrace_append hprefix tailTrace_951454
  have hstable : (prefixWord ++ tailWord_951454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951454).length < 2 ^ (prefixWord ++ tailWord_951454).sum := by decide
  have hdescent : baseEnd_951454 < baseStart_951454 := by decide
  rcases family_descends (prefixWord ++ tailWord_951454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951481 : List Nat := [1, 2, 1, 4, 1, 5, 2, 1, 1, 3, 2]
def baseStart_951481 : Nat := 118140960795 + 951481 * 2 ^ 59
def prefixEnd_951481 : Nat := 4983230072969 + 3 ^ 40 * 951481 * 2
def baseEnd_951481 : Nat := 488567086620697059911725

theorem tailTrace_951481 : CollatzResearch.WordTrace tailWord_951481 prefixEnd_951481 488567086620697059911725 := by
  unfold tailWord_951481
  simp only [CollatzResearch.WordTrace]
  refine ⟨34703363065954311862622297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23135575377302874575081531 34703363065954311862622297)
  ·
    refine ⟨26027522299465733896966723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34703363065954311862622297 26027522299465733896966723)
    ·
      refine ⟨39041283449198600845450085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26027522299465733896966723 39041283449198600845450085)
      ·
        refine ⟨7320240646724737658521891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39041283449198600845450085 7320240646724737658521891)
        ·
          refine ⟨10980360970087106487782837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7320240646724737658521891 10980360970087106487782837)
          ·
            refine ⟨1029408840945666233229641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10980360970087106487782837 1029408840945666233229641)
            ·
              refine ⟨772056630709249674922231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1029408840945666233229641 772056630709249674922231)
              ·
                refine ⟨1158084946063874512383347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 772056630709249674922231 1158084946063874512383347)
                ·
                  refine ⟨1737127419095811768575021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1158084946063874512383347 1737127419095811768575021)
                  ·
                    refine ⟨651422782160929413215633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1737127419095811768575021 651422782160929413215633)
                    ·
                      refine ⟨488567086620697059911725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 651422782160929413215633 488567086620697059911725)
                      ·
                        rfl

theorem cell23_951481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_951481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951481 prefixEnd_951481 := by exact prefixLift 951481
  have htrace : WordTrace (prefixWord ++ tailWord_951481) baseStart_951481 baseEnd_951481 := by
    simpa [prefixWord, tailWord_951481, baseEnd_951481] using wordTrace_append hprefix tailTrace_951481
  have hstable : (prefixWord ++ tailWord_951481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951481).length < 2 ^ (prefixWord ++ tailWord_951481).sum := by decide
  have hdescent : baseEnd_951481 < baseStart_951481 := by decide
  rcases family_descends (prefixWord ++ tailWord_951481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951530 : List Nat := [3, 1, 3, 1, 1, 3, 2, 1, 1, 7]
def baseStart_951530 : Nat := 118140960795 + 951530 * 2 ^ 59
def prefixEnd_951530 : Nat := 4983230072969 + 3 ^ 40 * 951530 * 2
def baseEnd_951530 : Nat := 162864082390922456066333

theorem tailTrace_951530 : CollatzResearch.WordTrace tailWord_951530 prefixEnd_951530 162864082390922456066333 := by
  unfold tailWord_951530
  simp only [CollatzResearch.WordTrace]
  refine ⟨8676287560694198307789011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23136766828517862154104029 8676287560694198307789011)
  ·
    refine ⟨13014431341041297461683517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8676287560694198307789011 13014431341041297461683517)
    ·
      refine ⟨4880411752890486548131319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13014431341041297461683517 4880411752890486548131319)
      ·
        refine ⟨7320617629335729822196979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4880411752890486548131319 7320617629335729822196979)
        ·
          refine ⟨10980926444003594733295469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7320617629335729822196979 10980926444003594733295469)
          ·
            refine ⟨4117847416501348024985801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10980926444003594733295469 4117847416501348024985801)
            ·
              refine ⟨3088385562376011018739351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4117847416501348024985801 3088385562376011018739351)
              ·
                refine ⟨4632578343564016528109027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3088385562376011018739351 4632578343564016528109027)
                ·
                  refine ⟨6948867515346024792163541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4632578343564016528109027 6948867515346024792163541)
                  ·
                    refine ⟨162864082390922456066333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6948867515346024792163541 162864082390922456066333)
                    ·
                      rfl

theorem cell23_951530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_951530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951530 prefixEnd_951530 := by exact prefixLift 951530
  have htrace : WordTrace (prefixWord ++ tailWord_951530) baseStart_951530 baseEnd_951530 := by
    simpa [prefixWord, tailWord_951530, baseEnd_951530] using wordTrace_append hprefix tailTrace_951530
  have hstable : (prefixWord ++ tailWord_951530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951530).length < 2 ^ (prefixWord ++ tailWord_951530).sum := by decide
  have hdescent : baseEnd_951530 < baseStart_951530 := by decide
  rcases family_descends (prefixWord ++ tailWord_951530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951543 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 1, 10]
def baseStart_951543 : Nat := 118140960795 + 951543 * 2 ^ 59
def prefixEnd_951543 : Nat := 4983230072969 + 3 ^ 40 * 951543 * 2
def baseEnd_951543 : Nat := 162866307473758605778813

theorem tailTrace_951543 : CollatzResearch.WordTrace tailWord_951543 prefixEnd_951543 162866307473758605778813 := by
  unfold tailWord_951543
  simp only [CollatzResearch.WordTrace]
  refine ⟨34705624391729696451379283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23137082927819797634252855 34705624391729696451379283)
  ·
    refine ⟨52058436587594544677068925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34705624391729696451379283 52058436587594544677068925)
    ·
      refine ⟨19521913720347954253900847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52058436587594544677068925 19521913720347954253900847)
      ·
        refine ⟨29282870580521931380851271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19521913720347954253900847 29282870580521931380851271)
        ·
          refine ⟨43924305870782897071276907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29282870580521931380851271 43924305870782897071276907)
          ·
            refine ⟨65886458806174345606915361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43924305870782897071276907 65886458806174345606915361)
            ·
              refine ⟨49414844104630759205186521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65886458806174345606915361 49414844104630759205186521)
              ·
                refine ⟨37061133078473069403889891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49414844104630759205186521 37061133078473069403889891)
                ·
                  refine ⟨55591699617709604105834837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37061133078473069403889891 55591699617709604105834837)
                  ·
                    refine ⟨162866307473758605778813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 55591699617709604105834837 162866307473758605778813)
                    ·
                      rfl

theorem cell23_951543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 10].length) (baseStart_951543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951543 prefixEnd_951543 := by exact prefixLift 951543
  have htrace : WordTrace (prefixWord ++ tailWord_951543) baseStart_951543 baseEnd_951543 := by
    simpa [prefixWord, tailWord_951543, baseEnd_951543] using wordTrace_append hprefix tailTrace_951543
  have hstable : (prefixWord ++ tailWord_951543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951543).length < 2 ^ (prefixWord ++ tailWord_951543).sum := by decide
  have hdescent : baseEnd_951543 < baseStart_951543 := by decide
  rcases family_descends (prefixWord ++ tailWord_951543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951580 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 2, 4, 4]
def baseStart_951580 : Nat := 118140960795 + 951580 * 2 ^ 59
def prefixEnd_951580 : Nat := 4983230072969 + 3 ^ 40 * 951580 * 2
def baseEnd_951580 : Nat := 488617921205492172573769

theorem tailTrace_951580 : CollatzResearch.WordTrace tailWord_951580 prefixEnd_951580 488617921205492172573769 := by
  unfold tailWord_951580
  simp only [CollatzResearch.WordTrace]
  refine ⟨17353486946297825885238097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23137982595063767846984129 17353486946297825885238097)
  ·
    refine ⟨13015115209723369413928573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17353486946297825885238097 13015115209723369413928573)
    ·
      refine ⟨4880668203646263530223215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13015115209723369413928573 4880668203646263530223215)
      ·
        refine ⟨7321002305469395295334823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4880668203646263530223215 7321002305469395295334823)
        ·
          refine ⟨10981503458204092943002235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7321002305469395295334823 10981503458204092943002235)
          ·
            refine ⟨16472255187306139414503353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10981503458204092943002235 16472255187306139414503353)
            ·
              refine ⟨12354191390479604560877515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16472255187306139414503353 12354191390479604560877515)
              ·
                refine ⟨18531287085719406841316273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12354191390479604560877515 18531287085719406841316273)
                ·
                  refine ⟨13898465314289555130987205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18531287085719406841316273 13898465314289555130987205)
                  ·
                    refine ⟨2605962246429291587060101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13898465314289555130987205 2605962246429291587060101)
                    ·
                      refine ⟨488617921205492172573769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2605962246429291587060101 488617921205492172573769)
                      ·
                        rfl

theorem cell23_951580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_951580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951580 prefixEnd_951580 := by exact prefixLift 951580
  have htrace : WordTrace (prefixWord ++ tailWord_951580) baseStart_951580 baseEnd_951580 := by
    simpa [prefixWord, tailWord_951580, baseEnd_951580] using wordTrace_append hprefix tailTrace_951580
  have hstable : (prefixWord ++ tailWord_951580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951580).length < 2 ^ (prefixWord ++ tailWord_951580).sum := by decide
  have hdescent : baseEnd_951580 < baseStart_951580 := by decide
  rcases family_descends (prefixWord ++ tailWord_951580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951584 : List Nat := [2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 4]
def baseStart_951584 : Nat := 118140960795 + 951584 * 2 ^ 59
def prefixEnd_951584 : Nat := 4983230072969 + 3 ^ 40 * 951584 * 2
def baseEnd_951584 : Nat := 488619975128110156923751

theorem tailTrace_951584 : CollatzResearch.WordTrace tailWord_951584 prefixEnd_951584 488619975128110156923751 := by
  unfold tailWord_951584
  simp only [CollatzResearch.WordTrace]
  refine ⟨17353559892290580226810903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23138079856387440302414537 17353559892290580226810903)
  ·
    refine ⟨26030339838435870340216355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17353559892290580226810903 26030339838435870340216355)
    ·
      refine ⟨39045509757653805510324533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26030339838435870340216355 39045509757653805510324533)
      ·
        refine ⟨3660516539780044266592925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39045509757653805510324533 3660516539780044266592925)
        ·
          refine ⟨1372693702417516599972347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3660516539780044266592925 1372693702417516599972347)
          ·
            refine ⟨2059040553626274899958521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1372693702417516599972347 2059040553626274899958521)
            ·
              refine ⟨1544280415219706174968891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2059040553626274899958521 1544280415219706174968891)
              ·
                refine ⟨2316420622829559262453337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1544280415219706174968891 2316420622829559262453337)
                ·
                  refine ⟨1737315467122169446840003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2316420622829559262453337 1737315467122169446840003)
                  ·
                    refine ⟨2605973200683254170260005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1737315467122169446840003 2605973200683254170260005)
                    ·
                      refine ⟨488619975128110156923751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2605973200683254170260005 488619975128110156923751)
                      ·
                        rfl

theorem cell23_951584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_951584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951584 prefixEnd_951584 := by exact prefixLift 951584
  have htrace : WordTrace (prefixWord ++ tailWord_951584) baseStart_951584 baseEnd_951584 := by
    simpa [prefixWord, tailWord_951584, baseEnd_951584] using wordTrace_append hprefix tailTrace_951584
  have hstable : (prefixWord ++ tailWord_951584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951584).length < 2 ^ (prefixWord ++ tailWord_951584).sum := by decide
  have hdescent : baseEnd_951584 < baseStart_951584 := by decide
  rcases family_descends (prefixWord ++ tailWord_951584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951587 : List Nat := [1, 1, 1, 4, 2, 3, 1, 3, 2, 2, 3]
def baseStart_951587 : Nat := 118140960795 + 951587 * 2 ^ 59
def prefixEnd_951587 : Nat := 4983230072969 + 3 ^ 40 * 951587 * 2
def baseEnd_951587 : Nat := 488621515570073645186237

theorem tailTrace_951587 : CollatzResearch.WordTrace tailWord_951587 prefixEnd_951587 488621515570073645186237 := by
  unfold tailWord_951587
  simp only [CollatzResearch.WordTrace]
  refine ⟨34707229203570291965981015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23138152802380194643987343 34707229203570291965981015)
  ·
    refine ⟨52060843805355437948971523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34707229203570291965981015 52060843805355437948971523)
    ·
      refine ⟨78091265708033156923457285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52060843805355437948971523 78091265708033156923457285)
      ·
        refine ⟨14642112320256216923148241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78091265708033156923457285 14642112320256216923148241)
        ·
          refine ⟨10981584240192162692361181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14642112320256216923148241 10981584240192162692361181)
          ·
            refine ⟨4118094090072061009635443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10981584240192162692361181 4118094090072061009635443)
            ·
              refine ⟨6177141135108091514453165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4118094090072061009635443 6177141135108091514453165)
              ·
                refine ⟨2316427925665534317919937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6177141135108091514453165 2316427925665534317919937)
                ·
                  refine ⟨1737320944249150738439953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2316427925665534317919937 1737320944249150738439953)
                  ·
                    refine ⟨1302990708186863053829965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1737320944249150738439953 1302990708186863053829965)
                    ·
                      refine ⟨488621515570073645186237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1302990708186863053829965 488621515570073645186237)
                      ·
                        rfl

theorem cell23_951587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_951587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951587 prefixEnd_951587 := by exact prefixLift 951587
  have htrace : WordTrace (prefixWord ++ tailWord_951587) baseStart_951587 baseEnd_951587 := by
    simpa [prefixWord, tailWord_951587, baseEnd_951587] using wordTrace_append hprefix tailTrace_951587
  have hstable : (prefixWord ++ tailWord_951587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951587).length < 2 ^ (prefixWord ++ tailWord_951587).sum := by decide
  have hdescent : baseEnd_951587 < baseStart_951587 := by decide
  rcases family_descends (prefixWord ++ tailWord_951587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951604 : List Nat := [2, 5, 1, 1, 1, 1, 1, 4, 2, 2, 3]
def baseStart_951604 : Nat := 118140960795 + 951604 * 2 ^ 59
def prefixEnd_951604 : Nat := 4983230072969 + 3 ^ 40 * 951604 * 2
def baseEnd_951604 : Nat := 488630244741200078673659

theorem tailTrace_951604 : CollatzResearch.WordTrace tailWord_951604 prefixEnd_951604 488630244741200078673659 := by
  unfold tailWord_951604
  simp only [CollatzResearch.WordTrace]
  refine ⟨17353924622254351934674933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23138566163005802579566577 17353924622254351934674933)
  ·
    refine ⟨1626930433336345493875775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17353924622254351934674933 1626930433336345493875775)
    ·
      refine ⟨2440395650004518240813663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1626930433336345493875775 2440395650004518240813663)
      ·
        refine ⟨3660593475006777361220495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2440395650004518240813663 3660593475006777361220495)
        ·
          refine ⟨5490890212510166041830743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3660593475006777361220495 5490890212510166041830743)
          ·
            refine ⟨8236335318765249062746115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5490890212510166041830743 8236335318765249062746115)
            ·
              refine ⟨12354502978147873594119173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8236335318765249062746115 12354502978147873594119173)
              ·
                refine ⟨2316469308402726298897345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12354502978147873594119173 2316469308402726298897345)
                ·
                  refine ⟨1737351981302044724173009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2316469308402726298897345 1737351981302044724173009)
                  ·
                    refine ⟨1303013985976533543129757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1737351981302044724173009 1303013985976533543129757)
                    ·
                      refine ⟨488630244741200078673659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1303013985976533543129757 488630244741200078673659)
                      ·
                        rfl

theorem cell23_951604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_951604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951604 prefixEnd_951604 := by exact prefixLift 951604
  have htrace : WordTrace (prefixWord ++ tailWord_951604) baseStart_951604 baseEnd_951604 := by
    simpa [prefixWord, tailWord_951604, baseEnd_951604] using wordTrace_append hprefix tailTrace_951604
  have hstable : (prefixWord ++ tailWord_951604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951604).length < 2 ^ (prefixWord ++ tailWord_951604).sum := by decide
  have hdescent : baseEnd_951604 < baseStart_951604 := by decide
  rcases family_descends (prefixWord ++ tailWord_951604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951610 : List Nat := [3, 1, 1, 1, 4, 1, 2, 1, 1, 2, 6]
def baseStart_951610 : Nat := 118140960795 + 951610 * 2 ^ 59
def prefixEnd_951610 : Nat := 4983230072969 + 3 ^ 40 * 951610 * 2
def baseEnd_951610 : Nat := 488633325625127055198631

theorem tailTrace_951610 : CollatzResearch.WordTrace tailWord_951610 prefixEnd_951610 488633325625127055198631 := by
  unfold tailWord_951610
  simp only [CollatzResearch.WordTrace]
  refine ⟨8677017020621741723517071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23138712054991311262712189 8677017020621741723517071)
  ·
    refine ⟨13015525530932612585275607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8677017020621741723517071 13015525530932612585275607)
    ·
      refine ⟨19523288296398918877913411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13015525530932612585275607 19523288296398918877913411)
      ·
        refine ⟨29284932444598378316870117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19523288296398918877913411 29284932444598378316870117)
        ·
          refine ⟨5490924833362195934413147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29284932444598378316870117 5490924833362195934413147)
          ·
            refine ⟨8236387250043293901619721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5490924833362195934413147 8236387250043293901619721)
            ·
              refine ⟨6177290437532470426214791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8236387250043293901619721 6177290437532470426214791)
              ·
                refine ⟨9265935656298705639322187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6177290437532470426214791 9265935656298705639322187)
                ·
                  refine ⟨13898903484448058458983281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9265935656298705639322187 13898903484448058458983281)
                  ·
                    refine ⟨10424177613336043844237461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13898903484448058458983281 10424177613336043844237461)
                    ·
                      refine ⟨488633325625127055198631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10424177613336043844237461 488633325625127055198631)
                      ·
                        rfl

theorem cell23_951610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_951610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951610 prefixEnd_951610 := by exact prefixLift 951610
  have htrace : WordTrace (prefixWord ++ tailWord_951610) baseStart_951610 baseEnd_951610 := by
    simpa [prefixWord, tailWord_951610, baseEnd_951610] using wordTrace_append hprefix tailTrace_951610
  have hstable : (prefixWord ++ tailWord_951610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951610).length < 2 ^ (prefixWord ++ tailWord_951610).sum := by decide
  have hdescent : baseEnd_951610 < baseStart_951610 := by decide
  rcases family_descends (prefixWord ++ tailWord_951610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951630 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7]
def baseStart_951630 : Nat := 118140960795 + 951630 * 2 ^ 59
def prefixEnd_951630 : Nat := 4983230072969 + 3 ^ 40 * 951630 * 2
def baseEnd_951630 : Nat := 488643595238216976948539

theorem tailTrace_951630 : CollatzResearch.WordTrace tailWord_951630 prefixEnd_951630 488643595238216976948539 := by
  unfold tailWord_951630
  simp only [CollatzResearch.WordTrace]
  refine ⟨4338599692801813788724543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23139198361609673539864229 4338599692801813788724543)
  ·
    refine ⟨6507899539202720683086815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4338599692801813788724543 6507899539202720683086815)
    ·
      refine ⟨9761849308804081024630223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6507899539202720683086815 9761849308804081024630223)
      ·
        refine ⟨14642773963206121536945335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9761849308804081024630223 14642773963206121536945335)
        ·
          refine ⟨21964160944809182305418003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14642773963206121536945335 21964160944809182305418003)
          ·
            refine ⟨32946241417213773458127005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21964160944809182305418003 32946241417213773458127005)
            ·
              refine ⟨12354840531455165046797627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32946241417213773458127005 12354840531455165046797627)
              ·
                refine ⟨18532260797182747570196441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12354840531455165046797627 18532260797182747570196441)
                ·
                  refine ⟨13899195597887060677647331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18532260797182747570196441 13899195597887060677647331)
                  ·
                    refine ⟨20848793396830591016470997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13899195597887060677647331 20848793396830591016470997)
                    ·
                      refine ⟨488643595238216976948539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 20848793396830591016470997 488643595238216976948539)
                      ·
                        rfl

theorem cell23_951630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_951630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951630 prefixEnd_951630 := by exact prefixLift 951630
  have htrace : WordTrace (prefixWord ++ tailWord_951630) baseStart_951630 baseEnd_951630 := by
    simpa [prefixWord, tailWord_951630, baseEnd_951630] using wordTrace_append hprefix tailTrace_951630
  have hstable : (prefixWord ++ tailWord_951630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951630).length < 2 ^ (prefixWord ++ tailWord_951630).sum := by decide
  have hdescent : baseEnd_951630 < baseStart_951630 := by decide
  rcases family_descends (prefixWord ++ tailWord_951630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951637 : List Nat := [1, 3, 2, 2, 3, 1, 2, 1, 3, 5]
def baseStart_951637 : Nat := 118140960795 + 951637 * 2 ^ 59
def prefixEnd_951637 : Nat := 4983230072969 + 3 ^ 40 * 951637 * 2
def baseEnd_951637 : Nat := 162882396534266149853669

theorem tailTrace_951637 : CollatzResearch.WordTrace tailWord_951637 prefixEnd_951637 162882396534266149853669 := by
  unfold tailWord_951637
  simp only [CollatzResearch.WordTrace]
  refine ⟨34709052853389150505301165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23139368568926100336867443 34709052853389150505301165)
  ·
    refine ⟨13015894820020931439487937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34709052853389150505301165 13015894820020931439487937)
    ·
      refine ⟨9761921115015698579615953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13015894820020931439487937 9761921115015698579615953)
      ·
        refine ⟨7321440836261773934711965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9761921115015698579615953 7321440836261773934711965)
        ·
          refine ⟨2745540313598165225516987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7321440836261773934711965 2745540313598165225516987)
          ·
            refine ⟨4118310470397247838275481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2745540313598165225516987 4118310470397247838275481)
            ·
              refine ⟨3088732852797935878706611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4118310470397247838275481 3088732852797935878706611)
              ·
                refine ⟨4633099279196903818059917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3088732852797935878706611 4633099279196903818059917)
                ·
                  refine ⟨1737412229698838931772469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4633099279196903818059917 1737412229698838931772469)
                  ·
                    refine ⟨162882396534266149853669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1737412229698838931772469 162882396534266149853669)
                    ·
                      rfl

theorem cell23_951637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_951637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951637 prefixEnd_951637 := by exact prefixLift 951637
  have htrace : WordTrace (prefixWord ++ tailWord_951637) baseStart_951637 baseEnd_951637 := by
    simpa [prefixWord, tailWord_951637, baseEnd_951637] using wordTrace_append hprefix tailTrace_951637
  have hstable : (prefixWord ++ tailWord_951637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951637).length < 2 ^ (prefixWord ++ tailWord_951637).sum := by decide
  have hdescent : baseEnd_951637 < baseStart_951637 := by decide
  rcases family_descends (prefixWord ++ tailWord_951637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951651 : List Nat := [1, 1, 1, 5, 2, 2, 1, 5, 1, 1, 3]
def baseStart_951651 : Nat := 118140960795 + 951651 * 2 ^ 59
def prefixEnd_951651 : Nat := 4983230072969 + 3 ^ 40 * 951651 * 2
def baseEnd_951651 : Nat := 488654378331961394785943

theorem tailTrace_951651 : CollatzResearch.WordTrace tailWord_951651 prefixEnd_951651 488654378331961394785943 := by
  unfold tailWord_951651
  simp only [CollatzResearch.WordTrace]
  refine ⟨34709563475338430896310807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23139708983558953930873871 34709563475338430896310807)
  ·
    refine ⟨52064345213007646344466211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34709563475338430896310807 52064345213007646344466211)
    ·
      refine ⟨78096517819511469516699317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52064345213007646344466211 78096517819511469516699317)
      ·
        refine ⟨7321548545579200267190561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78096517819511469516699317 7321548545579200267190561)
        ·
          refine ⟨5491161409184400200392921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7321548545579200267190561 5491161409184400200392921)
          ·
            refine ⟨4118371056888300150294691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5491161409184400200392921 4118371056888300150294691)
            ·
              refine ⟨6177556585332450225442037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4118371056888300150294691 6177556585332450225442037)
              ·
                refine ⟨579145929874917208635191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6177556585332450225442037 579145929874917208635191)
                ·
                  refine ⟨868718894812375812952787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 579145929874917208635191 868718894812375812952787)
                  ·
                    refine ⟨1303078342218563719429181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 868718894812375812952787 1303078342218563719429181)
                    ·
                      refine ⟨488654378331961394785943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1303078342218563719429181 488654378331961394785943)
                      ·
                        rfl

theorem cell23_951651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 5, 1, 1, 3].length) (baseStart_951651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951651 prefixEnd_951651 := by exact prefixLift 951651
  have htrace : WordTrace (prefixWord ++ tailWord_951651) baseStart_951651 baseEnd_951651 := by
    simpa [prefixWord, tailWord_951651, baseEnd_951651] using wordTrace_append hprefix tailTrace_951651
  have hstable : (prefixWord ++ tailWord_951651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951651).length < 2 ^ (prefixWord ++ tailWord_951651).sum := by decide
  have hdescent : baseEnd_951651 < baseStart_951651 := by decide
  rcases family_descends (prefixWord ++ tailWord_951651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951674 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 7, 2, 2]
def baseStart_951674 : Nat := 118140960795 + 951674 * 2 ^ 59
def prefixEnd_951674 : Nat := 4983230072969 + 3 ^ 40 * 951674 * 2
def baseEnd_951674 : Nat := 488666188387014804798337

theorem tailTrace_951674 : CollatzResearch.WordTrace tailWord_951674 prefixEnd_951674 488666188387014804798337 := by
  unfold tailWord_951674
  simp only [CollatzResearch.WordTrace]
  refine ⟨8677600588563776456099519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23140268236170070549598717 8677600588563776456099519)
  ·
    refine ⟨13016400882845664684149279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8677600588563776456099519 13016400882845664684149279)
    ·
      refine ⟨19524601324268497026223919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13016400882845664684149279 19524601324268497026223919)
      ·
        refine ⟨29286901986402745539335879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19524601324268497026223919 29286901986402745539335879)
        ·
          refine ⟨43930352979604118309003819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29286901986402745539335879 43930352979604118309003819)
          ·
            refine ⟨65895529469406177463505729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43930352979604118309003819 65895529469406177463505729)
            ·
              refine ⟨49421647102054633097629297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65895529469406177463505729 49421647102054633097629297)
              ·
                refine ⟨37066235326540974823221973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49421647102054633097629297 37066235326540974823221973)
                ·
                  refine ⟨868739890465804097419265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 37066235326540974823221973 868739890465804097419265)
                  ·
                    refine ⟨651554917849353073064449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 868739890465804097419265 651554917849353073064449)
                    ·
                      refine ⟨488666188387014804798337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 651554917849353073064449 488666188387014804798337)
                      ·
                        rfl

theorem cell23_951674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 7, 2, 2].length) (baseStart_951674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951674 prefixEnd_951674 := by exact prefixLift 951674
  have htrace : WordTrace (prefixWord ++ tailWord_951674) baseStart_951674 baseEnd_951674 := by
    simpa [prefixWord, tailWord_951674, baseEnd_951674] using wordTrace_append hprefix tailTrace_951674
  have hstable : (prefixWord ++ tailWord_951674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951674).length < 2 ^ (prefixWord ++ tailWord_951674).sum := by decide
  have hdescent : baseEnd_951674 < baseStart_951674 := by decide
  rcases family_descends (prefixWord ++ tailWord_951674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951677 : List Nat := [1, 4, 1, 1, 2, 2, 3, 2, 1, 1, 5]
def baseStart_951677 : Nat := 118140960795 + 951677 * 2 ^ 59
def prefixEnd_951677 : Nat := 4983230072969 + 3 ^ 40 * 951677 * 2
def baseEnd_951677 : Nat := 488667728828978293060823

theorem tailTrace_951677 : CollatzResearch.WordTrace tailWord_951677 prefixEnd_951677 488667728828978293060823 := by
  unfold tailWord_951677
  simp only [CollatzResearch.WordTrace]
  refine ⟨34710511773244237336757285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23140341182162824891171523 34710511773244237336757285)
  ·
    refine ⟨6508220957483294500641991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34710511773244237336757285 6508220957483294500641991)
    ·
      refine ⟨9762331436224941750962987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6508220957483294500641991 9762331436224941750962987)
      ·
        refine ⟨14643497154337412626444481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9762331436224941750962987 14643497154337412626444481)
        ·
          refine ⟨10982622865753059469833361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14643497154337412626444481 10982622865753059469833361)
          ·
            refine ⟨8236967149314794602375021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10982622865753059469833361 8236967149314794602375021)
            ·
              refine ⟨3088862680993047975890633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8236967149314794602375021 3088862680993047975890633)
              ·
                refine ⟨2316647010744785981917975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3088862680993047975890633 2316647010744785981917975)
                ·
                  refine ⟨3474970516117178972876963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2316647010744785981917975 3474970516117178972876963)
                  ·
                    refine ⟨5212455774175768459315445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3474970516117178972876963 5212455774175768459315445)
                    ·
                      refine ⟨488667728828978293060823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5212455774175768459315445 488667728828978293060823)
                      ·
                        rfl

theorem cell23_951677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_951677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951677 prefixEnd_951677 := by exact prefixLift 951677
  have htrace : WordTrace (prefixWord ++ tailWord_951677) baseStart_951677 baseEnd_951677 := by
    simpa [prefixWord, tailWord_951677, baseEnd_951677] using wordTrace_append hprefix tailTrace_951677
  have hstable : (prefixWord ++ tailWord_951677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951677).length < 2 ^ (prefixWord ++ tailWord_951677).sum := by decide
  have hdescent : baseEnd_951677 < baseStart_951677 := by decide
  rcases family_descends (prefixWord ++ tailWord_951677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951684 : List Nat := [2, 3, 2, 1, 1, 5, 1, 1, 1, 6]
def baseStart_951684 : Nat := 118140960795 + 951684 * 2 ^ 59
def prefixEnd_951684 : Nat := 4983230072969 + 3 ^ 40 * 951684 * 2
def baseEnd_951684 : Nat := 162890441064519921891097

theorem tailTrace_951684 : CollatzResearch.WordTrace tailWord_951684 prefixEnd_951684 162890441064519921891097 := by
  unfold tailWord_951684
  simp only [CollatzResearch.WordTrace]
  refine ⟨17355383542109438766131053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23140511389479251688174737 17355383542109438766131053)
  ·
    refine ⟨6508268828291039537299145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17355383542109438766131053 6508268828291039537299145)
    ·
      refine ⟨4881201621218279652974359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6508268828291039537299145 4881201621218279652974359)
      ·
        refine ⟨7321802431827419479461539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4881201621218279652974359 7321802431827419479461539)
        ·
          refine ⟨10982703647741129219192309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7321802431827419479461539 10982703647741129219192309)
          ·
            refine ⟨1029628466975730864299279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10982703647741129219192309 1029628466975730864299279)
            ·
              refine ⟨1544442700463596296448919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1029628466975730864299279 1544442700463596296448919)
              ·
                refine ⟨2316664050695394444673379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1544442700463596296448919 2316664050695394444673379)
                ·
                  refine ⟨3474996076043091667010069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2316664050695394444673379 3474996076043091667010069)
                  ·
                    refine ⟨162890441064519921891097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3474996076043091667010069 162890441064519921891097)
                    ·
                      rfl

theorem cell23_951684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_951684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951684 prefixEnd_951684 := by exact prefixLift 951684
  have htrace : WordTrace (prefixWord ++ tailWord_951684) baseStart_951684 baseEnd_951684 := by
    simpa [prefixWord, tailWord_951684, baseEnd_951684] using wordTrace_append hprefix tailTrace_951684
  have hstable : (prefixWord ++ tailWord_951684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951684).length < 2 ^ (prefixWord ++ tailWord_951684).sum := by decide
  have hdescent : baseEnd_951684 < baseStart_951684 := by decide
  rcases family_descends (prefixWord ++ tailWord_951684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951687 : List Nat := [1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 6]
def baseStart_951687 : Nat := 118140960795 + 951687 * 2 ^ 59
def prefixEnd_951687 : Nat := 4983230072969 + 3 ^ 40 * 951687 * 2
def baseEnd_951687 : Nat := 488672863635523253935777

theorem tailTrace_951687 : CollatzResearch.WordTrace tailWord_951687 prefixEnd_951687 488672863635523253935777 := by
  unfold tailWord_951687
  simp only [CollatzResearch.WordTrace]
  refine ⟨34710876503208009044621315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23140584335472006029747543 34710876503208009044621315)
  ·
    refine ⟨52066314754812013566931973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34710876503208009044621315 52066314754812013566931973)
    ·
      refine ⟨9762434016527252543799745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52066314754812013566931973 9762434016527252543799745)
      ·
        refine ⟨7321825512395439407849809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9762434016527252543799745 7321825512395439407849809)
        ·
          refine ⟨5491369134296579555887357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7321825512395439407849809 5491369134296579555887357)
          ·
            refine ⟨2059263425361217333457759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5491369134296579555887357 2059263425361217333457759)
            ·
              refine ⟨3088895138041826000186639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2059263425361217333457759 3088895138041826000186639)
              ·
                refine ⟨4633342707062739000279959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3088895138041826000186639 4633342707062739000279959)
                ·
                  refine ⟨6950014060594108500419939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4633342707062739000279959 6950014060594108500419939)
                  ·
                    refine ⟨10425021090891162750629909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6950014060594108500419939 10425021090891162750629909)
                    ·
                      refine ⟨488672863635523253935777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10425021090891162750629909 488672863635523253935777)
                      ·
                        rfl

theorem cell23_951687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_951687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951687 prefixEnd_951687 := by exact prefixLift 951687
  have htrace : WordTrace (prefixWord ++ tailWord_951687) baseStart_951687 baseEnd_951687 := by
    simpa [prefixWord, tailWord_951687, baseEnd_951687] using wordTrace_append hprefix tailTrace_951687
  have hstable : (prefixWord ++ tailWord_951687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951687).length < 2 ^ (prefixWord ++ tailWord_951687).sum := by decide
  have hdescent : baseEnd_951687 < baseStart_951687 := by decide
  rcases family_descends (prefixWord ++ tailWord_951687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951724 : List Nat := [2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 3]
def baseStart_951724 : Nat := 118140960795 + 951724 * 2 ^ 59
def prefixEnd_951724 : Nat := 4983230072969 + 3 ^ 40 * 951724 * 2
def baseEnd_951724 : Nat := 488691862419739609173107

theorem tailTrace_951724 : CollatzResearch.WordTrace tailWord_951724 prefixEnd_951724 488691862419739609173107 := by
  unfold tailWord_951724
  simp only [CollatzResearch.WordTrace]
  refine ⟨17356113002036982181859113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23141484002715976242478817 17356113002036982181859113)
  ·
    refine ⟨13017084751527736636394335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17356113002036982181859113 13017084751527736636394335)
    ·
      refine ⟨19525627127291604954591503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13017084751527736636394335 19525627127291604954591503)
      ·
        refine ⟨29288440690937407431887255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19525627127291604954591503 29288440690937407431887255)
        ·
          refine ⟨43932661036406111147830883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29288440690937407431887255 43932661036406111147830883)
          ·
            refine ⟨65898991554609166721746325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43932661036406111147830883 65898991554609166721746325)
            ·
              refine ⟨3089015229122304690081859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 65898991554609166721746325 3089015229122304690081859)
              ·
                refine ⟨4633522843683457035122789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3089015229122304690081859 4633522843683457035122789)
                ·
                  refine ⟨868785533190648194085523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4633522843683457035122789 868785533190648194085523)
                  ·
                    refine ⟨1303178299785972291128285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 868785533190648194085523 1303178299785972291128285)
                    ·
                      refine ⟨488691862419739609173107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1303178299785972291128285 488691862419739609173107)
                      ·
                        rfl

theorem cell23_951724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 3].length) (baseStart_951724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951724 prefixEnd_951724 := by exact prefixLift 951724
  have htrace : WordTrace (prefixWord ++ tailWord_951724) baseStart_951724 baseEnd_951724 := by
    simpa [prefixWord, tailWord_951724, baseEnd_951724] using wordTrace_append hprefix tailTrace_951724
  have hstable : (prefixWord ++ tailWord_951724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951724).length < 2 ^ (prefixWord ++ tailWord_951724).sum := by decide
  have hdescent : baseEnd_951724 < baseStart_951724 := by decide
  rcases family_descends (prefixWord ++ tailWord_951724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951725 : List Nat := [1, 5, 2, 2, 1, 3, 1, 1, 3, 2, 2]
def baseStart_951725 : Nat := 118140960795 + 951725 * 2 ^ 59
def prefixEnd_951725 : Nat := 4983230072969 + 3 ^ 40 * 951725 * 2
def baseEnd_951725 : Nat := 488692375900394105260603

theorem tailTrace_951725 : CollatzResearch.WordTrace tailWord_951725 prefixEnd_951725 488692375900394105260603 := by
  unfold tailWord_951725
  simp only [CollatzResearch.WordTrace]
  refine ⟨34712262477070341534504629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23141508318046894356336419 34712262477070341534504629)
  ·
    refine ⟨3254274607225344518859809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34712262477070341534504629 3254274607225344518859809)
    ·
      refine ⟨2440705955419008389144857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3254274607225344518859809 2440705955419008389144857)
      ·
        refine ⟨1830529466564256291858643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2440705955419008389144857 1830529466564256291858643)
        ·
          refine ⟨2745794199846384437787965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1830529466564256291858643 2745794199846384437787965)
          ·
            refine ⟨1029672824942394164170487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2745794199846384437787965 1029672824942394164170487)
            ·
              refine ⟨1544509237413591246255731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1029672824942394164170487 1544509237413591246255731)
              ·
                refine ⟨2316763856120386869383597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1544509237413591246255731 2316763856120386869383597)
                ·
                  refine ⟨868786446045145076018849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2316763856120386869383597 868786446045145076018849)
                  ·
                    refine ⟨651589834533858807014137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 868786446045145076018849 651589834533858807014137)
                    ·
                      refine ⟨488692375900394105260603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 651589834533858807014137 488692375900394105260603)
                      ·
                        rfl

theorem cell23_951725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_951725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951725 prefixEnd_951725 := by exact prefixLift 951725
  have htrace : WordTrace (prefixWord ++ tailWord_951725) baseStart_951725 baseEnd_951725 := by
    simpa [prefixWord, tailWord_951725, baseEnd_951725] using wordTrace_append hprefix tailTrace_951725
  have hstable : (prefixWord ++ tailWord_951725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951725).length < 2 ^ (prefixWord ++ tailWord_951725).sum := by decide
  have hdescent : baseEnd_951725 < baseStart_951725 := by decide
  rcases family_descends (prefixWord ++ tailWord_951725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951741 : List Nat := [1, 4, 1, 2, 2, 1, 3, 3, 2, 1, 3]
def baseStart_951741 : Nat := 118140960795 + 951741 * 2 ^ 59
def prefixEnd_951741 : Nat := 4983230072969 + 3 ^ 40 * 951741 * 2
def baseEnd_951741 : Nat := 488700591590866042660529

theorem tailTrace_951741 : CollatzResearch.WordTrace tailWord_951741 prefixEnd_951741 488700591590866042660529 := by
  unfold tailWord_951741
  simp only [CollatzResearch.WordTrace]
  refine ⟨34712846045012376267087077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23141897363341584178058051 34712846045012376267087077)
  ·
    refine ⟨6508658633439820550078827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34712846045012376267087077 6508658633439820550078827)
    ·
      refine ⟨9762987950159730825118241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6508658633439820550078827 9762987950159730825118241)
      ·
        refine ⟨7322240962619798118838681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9762987950159730825118241 7322240962619798118838681)
        ·
          refine ⟨5491680721964848589129011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7322240962619798118838681 5491680721964848589129011)
          ·
            refine ⟨8237521082947272883693517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5491680721964848589129011 8237521082947272883693517)
            ·
              refine ⟨3089070406105227331385069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8237521082947272883693517 3089070406105227331385069)
              ·
                refine ⟨1158401402289460249269401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3089070406105227331385069 1158401402289460249269401)
                ·
                  refine ⟨868801051717095186952051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1158401402289460249269401 868801051717095186952051)
                  ·
                    refine ⟨1303201577575642780428077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 868801051717095186952051 1303201577575642780428077)
                    ·
                      refine ⟨488700591590866042660529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1303201577575642780428077 488700591590866042660529)
                      ·
                        rfl

theorem cell23_951741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_951741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951741 prefixEnd_951741 := by exact prefixLift 951741
  have htrace : WordTrace (prefixWord ++ tailWord_951741) baseStart_951741 baseEnd_951741 := by
    simpa [prefixWord, tailWord_951741, baseEnd_951741] using wordTrace_append hprefix tailTrace_951741
  have hstable : (prefixWord ++ tailWord_951741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951741).length < 2 ^ (prefixWord ++ tailWord_951741).sum := by decide
  have hdescent : baseEnd_951741 < baseStart_951741 := by decide
  rcases family_descends (prefixWord ++ tailWord_951741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951767 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 4, 4, 3]
def baseStart_951767 : Nat := 118140960795 + 951767 * 2 ^ 59
def prefixEnd_951767 : Nat := 4983230072969 + 3 ^ 40 * 951767 * 2
def baseEnd_951767 : Nat := 488713942087882940935409

theorem tailTrace_951767 : CollatzResearch.WordTrace tailWord_951767 prefixEnd_951767 488713942087882940935409 := by
  unfold tailWord_951767
  simp only [CollatzResearch.WordTrace]
  refine ⟨34713794342918182707533555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23142529561945455138355703 34713794342918182707533555)
  ·
    refine ⟨52070691514377274061300333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34713794342918182707533555 52070691514377274061300333)
    ·
      refine ⟨19526509317891477772987625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52070691514377274061300333 19526509317891477772987625)
      ·
        refine ⟨14644881988418608329740719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19526509317891477772987625 14644881988418608329740719)
        ·
          refine ⟨21967322982627912494611079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14644881988418608329740719 21967322982627912494611079)
          ·
            refine ⟨32950984473941868741916619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21967322982627912494611079 32950984473941868741916619)
            ·
              refine ⟨49426476710912803112874929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32950984473941868741916619 49426476710912803112874929)
              ·
                refine ⟨37069857533184602334656197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49426476710912803112874929 37069857533184602334656197)
                ·
                  refine ⟨6950598287472112937748037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37069857533184602334656197 6950598287472112937748037)
                  ·
                    refine ⟨1303237178901021175827757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6950598287472112937748037 1303237178901021175827757)
                    ·
                      refine ⟨488713942087882940935409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1303237178901021175827757 488713942087882940935409)
                      ·
                        rfl

theorem cell23_951767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_951767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951767 prefixEnd_951767 := by exact prefixLift 951767
  have htrace : WordTrace (prefixWord ++ tailWord_951767) baseStart_951767 baseEnd_951767 := by
    simpa [prefixWord, tailWord_951767, baseEnd_951767] using wordTrace_append hprefix tailTrace_951767
  have hstable : (prefixWord ++ tailWord_951767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951767).length < 2 ^ (prefixWord ++ tailWord_951767).sum := by decide
  have hdescent : baseEnd_951767 < baseStart_951767 := by decide
  rcases family_descends (prefixWord ++ tailWord_951767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951794 : List Nat := [3, 2, 1, 4, 1, 1, 1, 1, 1, 4, 4]
def baseStart_951794 : Nat := 118140960795 + 951794 * 2 ^ 59
def prefixEnd_951794 : Nat := 4983230072969 + 3 ^ 40 * 951794 * 2
def baseEnd_951794 : Nat := 488727806065554335297785

theorem tailTrace_951794 : CollatzResearch.WordTrace tailWord_951794 prefixEnd_951794 488727806065554335297785 := by
  unfold tailWord_951794
  simp only [CollatzResearch.WordTrace]
  refine ⟨8678694778455091579691609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23143186075880244212510957 8678694778455091579691609)
  ·
    refine ⟨6509021083841318684768707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8678694778455091579691609 6509021083841318684768707)
    ·
      refine ⟨9763531625761978027153061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6509021083841318684768707 9763531625761978027153061)
      ·
        refine ⟨1830662179830370880091199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9763531625761978027153061 1830662179830370880091199)
        ·
          refine ⟨2745993269745556320136799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1830662179830370880091199 2745993269745556320136799)
          ·
            refine ⟨4118989904618334480205199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2745993269745556320136799 4118989904618334480205199)
            ·
              refine ⟨6178484856927501720307799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4118989904618334480205199 6178484856927501720307799)
              ·
                refine ⟨9267727285391252580461699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6178484856927501720307799 9267727285391252580461699)
                ·
                  refine ⟨13901590928086878870692549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9267727285391252580461699 13901590928086878870692549)
                  ·
                    refine ⟨2606548299016289788254853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13901590928086878870692549 2606548299016289788254853)
                    ·
                      refine ⟨488727806065554335297785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2606548299016289788254853 488727806065554335297785)
                      ·
                        rfl

theorem cell23_951794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_951794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951794 prefixEnd_951794 := by exact prefixLift 951794
  have htrace : WordTrace (prefixWord ++ tailWord_951794) baseStart_951794 baseEnd_951794 := by
    simpa [prefixWord, tailWord_951794, baseEnd_951794] using wordTrace_append hprefix tailTrace_951794
  have hstable : (prefixWord ++ tailWord_951794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951794).length < 2 ^ (prefixWord ++ tailWord_951794).sum := by decide
  have hdescent : baseEnd_951794 < baseStart_951794 := by decide
  rcases family_descends (prefixWord ++ tailWord_951794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951798 : List Nat := [5, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2]
def baseStart_951798 : Nat := 118140960795 + 951798 * 2 ^ 59
def prefixEnd_951798 : Nat := 4983230072969 + 3 ^ 40 * 951798 * 2
def baseEnd_951798 : Nat := 488729859988172319647767

theorem tailTrace_951798 : CollatzResearch.WordTrace tailWord_951798 prefixEnd_951798 488729859988172319647767 := by
  unfold tailWord_951798
  simp only [CollatzResearch.WordTrace]
  refine ⟨2169682812862867187619503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23143283337203916667941365 2169682812862867187619503)
  ·
    refine ⟨3254524219294300781429255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2169682812862867187619503 3254524219294300781429255)
    ·
      refine ⟨4881786328941451172143883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3254524219294300781429255 4881786328941451172143883)
      ·
        refine ⟨7322679493412176758215825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4881786328941451172143883 7322679493412176758215825)
        ·
          refine ⟨5492009620059132568661869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7322679493412176758215825 5492009620059132568661869)
          ·
            refine ⟨2059503607522174713248201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5492009620059132568661869 2059503607522174713248201)
            ·
              refine ⟨1544627705641631034936151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2059503607522174713248201 1544627705641631034936151)
              ·
                refine ⟨2316941558462446552404227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1544627705641631034936151 2316941558462446552404227)
                ·
                  refine ⟨3475412337693669828606341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2316941558462446552404227 3475412337693669828606341)
                  ·
                    refine ⟨651639813317563092863689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3475412337693669828606341 651639813317563092863689)
                    ·
                      refine ⟨488729859988172319647767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 651639813317563092863689 488729859988172319647767)
                      ·
                        rfl

theorem cell23_951798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_951798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951798 prefixEnd_951798 := by exact prefixLift 951798
  have htrace : WordTrace (prefixWord ++ tailWord_951798) baseStart_951798 baseEnd_951798 := by
    simpa [prefixWord, tailWord_951798, baseEnd_951798] using wordTrace_append hprefix tailTrace_951798
  have hstable : (prefixWord ++ tailWord_951798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951798).length < 2 ^ (prefixWord ++ tailWord_951798).sum := by decide
  have hdescent : baseEnd_951798 < baseStart_951798 := by decide
  rcases family_descends (prefixWord ++ tailWord_951798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951817 : List Nat := [1, 2, 1, 1, 3, 1, 5, 1, 1, 7]
def baseStart_951817 : Nat := 118140960795 + 951817 * 2 ^ 59
def prefixEnd_951817 : Nat := 4983230072969 + 3 ^ 40 * 951817 * 2
def baseEnd_951817 : Nat := 162913205373535915103393

theorem tailTrace_951817 : CollatzResearch.WordTrace tailWord_951817 prefixEnd_951817 162913205373535915103393 := by
  unfold tailWord_951817
  simp only [CollatzResearch.WordTrace]
  refine ⟨34715617992737041246853705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23143745328491360831235803 34715617992737041246853705)
  ·
    refine ⟨26036713494552780935140279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34715617992737041246853705 26036713494552780935140279)
    ·
      refine ⟨39055070241829171402710419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26036713494552780935140279 39055070241829171402710419)
      ·
        refine ⟨58582605362743757104065629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39055070241829171402710419 58582605362743757104065629)
        ·
          refine ⟨21968477011028908914024611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58582605362743757104065629 21968477011028908914024611)
          ·
            refine ⟨32952715516543363371036917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21968477011028908914024611 32952715516543363371036917)
            ·
              refine ⟨3089317079675940316034711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32952715516543363371036917 3089317079675940316034711)
              ·
                refine ⟨4633975619513910474052067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3089317079675940316034711 4633975619513910474052067)
                ·
                  refine ⟨6950963429270865711078101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4633975619513910474052067 6950963429270865711078101)
                  ·
                    refine ⟨162913205373535915103393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6950963429270865711078101 162913205373535915103393)
                    ·
                      rfl

theorem cell23_951817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 7].length) (baseStart_951817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951817 prefixEnd_951817 := by exact prefixLift 951817
  have htrace : WordTrace (prefixWord ++ tailWord_951817) baseStart_951817 baseEnd_951817 := by
    simpa [prefixWord, tailWord_951817, baseEnd_951817] using wordTrace_append hprefix tailTrace_951817
  have hstable : (prefixWord ++ tailWord_951817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951817).length < 2 ^ (prefixWord ++ tailWord_951817).sum := by decide
  have hdescent : baseEnd_951817 < baseStart_951817 := by decide
  rcases family_descends (prefixWord ++ tailWord_951817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951832 : List Nat := [2, 1, 2, 3, 5, 1, 1, 2, 2, 2, 2]
def baseStart_951832 : Nat := 118140960795 + 951832 * 2 ^ 59
def prefixEnd_951832 : Nat := 4983230072969 + 3 ^ 40 * 951832 * 2
def baseEnd_951832 : Nat := 488747318330425186622611

theorem tailTrace_951832 : CollatzResearch.WordTrace tailWord_951832 prefixEnd_951832 488747318330425186622611 := by
  unfold tailWord_951832
  simp only [CollatzResearch.WordTrace]
  refine ⟨17358082543841349404324875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23144110058455132539099833 17358082543841349404324875)
  ·
    refine ⟨26037123815762024106487313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17358082543841349404324875 26037123815762024106487313)
    ·
      refine ⟨19527842861821518079865485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26037123815762024106487313 19527842861821518079865485)
      ·
        refine ⟨7322941073183069279949557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19527842861821518079865485 7322941073183069279949557)
        ·
          refine ⟨686525725610912744995271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7322941073183069279949557 686525725610912744995271)
          ·
            refine ⟨1029788588416369117492907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686525725610912744995271 1029788588416369117492907)
            ·
              refine ⟨1544682882624553676239361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1029788588416369117492907 1544682882624553676239361)
              ·
                refine ⟨1158512161968415257179521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1544682882624553676239361 1158512161968415257179521)
                ·
                  refine ⟨868884121476311442884641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1158512161968415257179521 868884121476311442884641)
                  ·
                    refine ⟨651663091107233582163481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 868884121476311442884641 651663091107233582163481)
                    ·
                      refine ⟨488747318330425186622611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 651663091107233582163481 488747318330425186622611)
                      ·
                        rfl

theorem cell23_951832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_951832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951832 prefixEnd_951832 := by exact prefixLift 951832
  have htrace : WordTrace (prefixWord ++ tailWord_951832) baseStart_951832 baseEnd_951832 := by
    simpa [prefixWord, tailWord_951832, baseEnd_951832] using wordTrace_append hprefix tailTrace_951832
  have hstable : (prefixWord ++ tailWord_951832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951832).length < 2 ^ (prefixWord ++ tailWord_951832).sum := by decide
  have hdescent : baseEnd_951832 < baseStart_951832 := by decide
  rcases family_descends (prefixWord ++ tailWord_951832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951877 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 10]
def baseStart_951877 : Nat := 118140960795 + 951877 * 2 ^ 59
def prefixEnd_951877 : Nat := 4983230072969 + 3 ^ 40 * 951877 * 2
def baseEnd_951877 : Nat := 54307824995541945617767

theorem tailTrace_951877 : CollatzResearch.WordTrace tailWord_951877 prefixEnd_951877 54307824995541945617767 := by
  unfold tailWord_951877
  simp only [CollatzResearch.WordTrace]
  refine ⟨34717806372519671494037885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23145204248346447662691923 34717806372519671494037885)
  ·
    refine ⟨13019177389694876810264207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34717806372519671494037885 13019177389694876810264207)
    ·
      refine ⟨19528766084542315215396311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13019177389694876810264207 19528766084542315215396311)
      ·
        refine ⟨29293149126813472823094467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19528766084542315215396311 29293149126813472823094467)
        ·
          refine ⟨43939723690220209234641701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29293149126813472823094467 43939723690220209234641701)
          ·
            refine ⟨8238698191916289231495319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43939723690220209234641701 8238698191916289231495319)
            ·
              refine ⟨12358047287874433847242979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8238698191916289231495319 12358047287874433847242979)
              ·
                refine ⟨18537070931811650770864469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12358047287874433847242979 18537070931811650770864469)
                ·
                  refine ⟨54307824995541945617767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 18537070931811650770864469 54307824995541945617767)
                  ·
                    rfl

theorem cell23_951877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 10].length) (baseStart_951877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951877 prefixEnd_951877 := by exact prefixLift 951877
  have htrace : WordTrace (prefixWord ++ tailWord_951877) baseStart_951877 baseEnd_951877 := by
    simpa [prefixWord, tailWord_951877, baseEnd_951877] using wordTrace_append hprefix tailTrace_951877
  have hstable : (prefixWord ++ tailWord_951877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951877).length < 2 ^ (prefixWord ++ tailWord_951877).sum := by decide
  have hdescent : baseEnd_951877 < baseStart_951877 := by decide
  rcases family_descends (prefixWord ++ tailWord_951877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951897 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 1, 1, 8]
def baseStart_951897 : Nat := 118140960795 + 951897 * 2 ^ 59
def prefixEnd_951897 : Nat := 4983230072969 + 3 ^ 40 * 951897 * 2
def baseEnd_951897 : Nat := 488780694572967432309811

theorem tailTrace_951897 : CollatzResearch.WordTrace tailWord_951897 prefixEnd_951897 488780694572967432309811 := by
  unfold tailWord_951897
  simp only [CollatzResearch.WordTrace]
  refine ⟨34718535832447214909765945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23145690554964809939843963 34718535832447214909765945)
  ·
    refine ⟨26038901874335411182324459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34718535832447214909765945 26038901874335411182324459)
    ·
      refine ⟨39058352811503116773486689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26038901874335411182324459 39058352811503116773486689)
      ·
        refine ⟨29293764608627337580115017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39058352811503116773486689 29293764608627337580115017)
        ·
          refine ⟨21970323456470503185086263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29293764608627337580115017 21970323456470503185086263)
          ·
            refine ⟨32955485184705754777629395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21970323456470503185086263 32955485184705754777629395)
            ·
              refine ⟨49433227777058632166444093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32955485184705754777629395 49433227777058632166444093)
              ·
                refine ⟨18537460416396987062416535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49433227777058632166444093 18537460416396987062416535)
                ·
                  refine ⟨27806190624595480593624803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18537460416396987062416535 27806190624595480593624803)
                  ·
                    refine ⟨41709285936893220890437205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27806190624595480593624803 41709285936893220890437205)
                    ·
                      refine ⟨488780694572967432309811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 41709285936893220890437205 488780694572967432309811)
                      ·
                        rfl

theorem cell23_951897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_951897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951897 prefixEnd_951897 := by exact prefixLift 951897
  have htrace : WordTrace (prefixWord ++ tailWord_951897) baseStart_951897 baseEnd_951897 := by
    simpa [prefixWord, tailWord_951897, baseEnd_951897] using wordTrace_append hprefix tailTrace_951897
  have hstable : (prefixWord ++ tailWord_951897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951897).length < 2 ^ (prefixWord ++ tailWord_951897).sum := by decide
  have hdescent : baseEnd_951897 < baseStart_951897 := by decide
  rcases family_descends (prefixWord ++ tailWord_951897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951911 : List Nat := [1, 1, 5, 1, 1, 1, 6, 1, 6]
def baseStart_951911 : Nat := 118140960795 + 951911 * 2 ^ 59
def prefixEnd_951911 : Nat := 4983230072969 + 3 ^ 40 * 951911 * 2
def baseEnd_951911 : Nat := 54309764811347819726083

theorem tailTrace_951911 : CollatzResearch.WordTrace tailWord_951911 prefixEnd_951911 54309764811347819726083 := by
  unfold tailWord_951911
  simp only [CollatzResearch.WordTrace]
  refine ⟨34719046454396495300775587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23146030969597663533850391 34719046454396495300775587)
  ·
    refine ⟨52078569681594742951163381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34719046454396495300775587 52078569681594742951163381)
    ·
      refine ⟨4882365907649507151671567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52078569681594742951163381 4882365907649507151671567)
      ·
        refine ⟨7323548861474260727507351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4882365907649507151671567 7323548861474260727507351)
        ·
          refine ⟨10985323292211391091261027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7323548861474260727507351 10985323292211391091261027)
          ·
            refine ⟨16477984938317086636891541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10985323292211391091261027 16477984938317086636891541)
            ·
              refine ⟨772405543983613436104291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16477984938317086636891541 772405543983613436104291)
              ·
                refine ⟨1158608315975420154156437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 772405543983613436104291 1158608315975420154156437)
                ·
                  refine ⟨54309764811347819726083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1158608315975420154156437 54309764811347819726083)
                  ·
                    rfl

theorem cell23_951911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 6].length) (baseStart_951911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951911 prefixEnd_951911 := by exact prefixLift 951911
  have htrace : WordTrace (prefixWord ++ tailWord_951911) baseStart_951911 baseEnd_951911 := by
    simpa [prefixWord, tailWord_951911, baseEnd_951911] using wordTrace_append hprefix tailTrace_951911
  have hstable : (prefixWord ++ tailWord_951911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951911).length < 2 ^ (prefixWord ++ tailWord_951911).sum := by decide
  have hdescent : baseEnd_951911 < baseStart_951911 := by decide
  rcases family_descends (prefixWord ++ tailWord_951911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951921 : List Nat := [1, 2, 2, 2, 1, 1, 1, 6, 3, 1, 3]
def baseStart_951921 : Nat := 118140960795 + 951921 * 2 ^ 59
def prefixEnd_951921 : Nat := 4983230072969 + 3 ^ 40 * 951921 * 2
def baseEnd_951921 : Nat := 488793018108675338409701

theorem tailTrace_951921 : CollatzResearch.WordTrace tailWord_951921 prefixEnd_951921 488793018108675338409701 := by
  unfold tailWord_951921
  simp only [CollatzResearch.WordTrace]
  refine ⟨34719411184360267008639617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23146274122906844672426411 34719411184360267008639617)
  ·
    refine ⟨26039558388270200256479713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34719411184360267008639617 26039558388270200256479713)
    ·
      refine ⟨19529668791202650192359785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26039558388270200256479713 19529668791202650192359785)
      ·
        refine ⟨14647251593401987644269839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19529668791202650192359785 14647251593401987644269839)
        ·
          refine ⟨21970877390102981466404759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14647251593401987644269839 21970877390102981466404759)
          ·
            refine ⟨32956316085154472199607139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21970877390102981466404759 32956316085154472199607139)
            ·
              refine ⟨49434474127731708299410709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32956316085154472199607139 49434474127731708299410709)
              ·
                refine ⟨2317240974737423826534877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49434474127731708299410709 2317240974737423826534877)
                ·
                  refine ⟨868965365526533934950579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2317240974737423826534877 868965365526533934950579)
                  ·
                    refine ⟨1303448048289800902425869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 868965365526533934950579 1303448048289800902425869)
                    ·
                      refine ⟨488793018108675338409701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1303448048289800902425869 488793018108675338409701)
                      ·
                        rfl

theorem cell23_951921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 3, 1, 3].length) (baseStart_951921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951921 prefixEnd_951921 := by exact prefixLift 951921
  have htrace : WordTrace (prefixWord ++ tailWord_951921) baseStart_951921 baseEnd_951921 := by
    simpa [prefixWord, tailWord_951921, baseEnd_951921] using wordTrace_append hprefix tailTrace_951921
  have hstable : (prefixWord ++ tailWord_951921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951921).length < 2 ^ (prefixWord ++ tailWord_951921).sum := by decide
  have hdescent : baseEnd_951921 < baseStart_951921 := by decide
  rcases family_descends (prefixWord ++ tailWord_951921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951971 : List Nat := [1, 1, 1, 4, 1, 1, 3, 5, 2, 4]
def baseStart_951971 : Nat := 118140960795 + 951971 * 2 ^ 59
def prefixEnd_951971 : Nat := 4983230072969 + 3 ^ 40 * 951971 * 2
def baseEnd_951971 : Nat := 162939564047133380928157

theorem tailTrace_951971 : CollatzResearch.WordTrace tailWord_951971 prefixEnd_951971 162939564047133380928157 := by
  unfold tailWord_951971
  simp only [CollatzResearch.WordTrace]
  refine ⟨34721234834179125547959767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23147489889452750365306511 34721234834179125547959767)
  ·
    refine ⟨52081852251268688321939651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34721234834179125547959767 52081852251268688321939651)
    ·
      refine ⟨78122778376903032482909477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52081852251268688321939651 78122778376903032482909477)
      ·
        refine ⟨14648020945669318590545527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78122778376903032482909477 14648020945669318590545527)
        ·
          refine ⟨21972031418503977885818291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14648020945669318590545527 21972031418503977885818291)
          ·
            refine ⟨32958047127755966828727437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21972031418503977885818291 32958047127755966828727437)
            ·
              refine ⟨12359267672908487560772789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32958047127755966828727437 12359267672908487560772789)
              ·
                refine ⟨1158681344335170708822449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12359267672908487560772789 1158681344335170708822449)
                ·
                  refine ⟨869011008251378031616837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1158681344335170708822449 869011008251378031616837)
                  ·
                    refine ⟨162939564047133380928157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 869011008251378031616837 162939564047133380928157)
                    ·
                      rfl

theorem cell23_951971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 2, 4].length) (baseStart_951971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951971 prefixEnd_951971 := by exact prefixLift 951971
  have htrace : WordTrace (prefixWord ++ tailWord_951971) baseStart_951971 baseEnd_951971 := by
    simpa [prefixWord, tailWord_951971, baseEnd_951971] using wordTrace_append hprefix tailTrace_951971
  have hstable : (prefixWord ++ tailWord_951971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951971).length < 2 ^ (prefixWord ++ tailWord_951971).sum := by decide
  have hdescent : baseEnd_951971 < baseStart_951971 := by decide
  rcases family_descends (prefixWord ++ tailWord_951971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951991 : List Nat := [1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 4]
def baseStart_951991 : Nat := 118140960795 + 951991 * 2 ^ 59
def prefixEnd_951991 : Nat := 4983230072969 + 3 ^ 40 * 951991 * 2
def baseEnd_951991 : Nat := 488828961754490064534379

theorem tailTrace_951991 : CollatzResearch.WordTrace tailWord_951991 prefixEnd_951991 488828961754490064534379 := by
  unfold tailWord_951991
  simp only [CollatzResearch.WordTrace]
  refine ⟨34721964294106668963687827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23147976196071112642458551 34721964294106668963687827)
  ·
    refine ⟨52082946441160003445531741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34721964294106668963687827 52082946441160003445531741)
    ·
      refine ⟨19531104915435001292074403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52082946441160003445531741 19531104915435001292074403)
      ·
        refine ⟨29296657373152501938111605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19531104915435001292074403 29296657373152501938111605)
        ·
          refine ⟨2746561628733047056697963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29296657373152501938111605 2746561628733047056697963)
          ·
            refine ⟨4119842443099570585046945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2746561628733047056697963 4119842443099570585046945)
            ·
              refine ⟨3089881832324677938785209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4119842443099570585046945 3089881832324677938785209)
              ·
                refine ⟨2317411374243508454088907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3089881832324677938785209 2317411374243508454088907)
                ·
                  refine ⟨3476117061365262681133361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2317411374243508454088907 3476117061365262681133361)
                  ·
                    refine ⟨2607087796023947010850021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3476117061365262681133361 2607087796023947010850021)
                    ·
                      refine ⟨488828961754490064534379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2607087796023947010850021 488828961754490064534379)
                      ·
                        rfl

theorem cell23_951991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 4].length) (baseStart_951991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_951991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_951991 prefixEnd_951991 := by exact prefixLift 951991
  have htrace : WordTrace (prefixWord ++ tailWord_951991) baseStart_951991 baseEnd_951991 := by
    simpa [prefixWord, tailWord_951991, baseEnd_951991] using wordTrace_append hprefix tailTrace_951991
  have hstable : (prefixWord ++ tailWord_951991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951991).length < 2 ^ (prefixWord ++ tailWord_951991).sum := by decide
  have hdescent : baseEnd_951991 < baseStart_951991 := by decide
  rcases family_descends (prefixWord ++ tailWord_951991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952012 : List Nat := [2, 2, 1, 5, 2, 1, 2, 1, 3, 2, 2]
def baseStart_952012 : Nat := 118140960795 + 952012 * 2 ^ 59
def prefixEnd_952012 : Nat := 4983230072969 + 3 ^ 40 * 952012 * 2
def baseEnd_952012 : Nat := 488839744848234482371783

theorem tailTrace_952012 : CollatzResearch.WordTrace tailWord_952012 prefixEnd_952012 488839744848234482371783 := by
  unfold tailWord_952012
  simp only [CollatzResearch.WordTrace]
  refine ⟨17361365113515294775101145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23148486818020393033468193 17361365113515294775101145)
  ·
    refine ⟨13021023835136471081325859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17361365113515294775101145 13021023835136471081325859)
    ·
      refine ⟨19531535752704706621988789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13021023835136471081325859 19531535752704706621988789)
      ·
        refine ⟨1831081476816066245811449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19531535752704706621988789 1831081476816066245811449)
        ·
          refine ⟨1373311107612049684358587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1831081476816066245811449 1373311107612049684358587)
          ·
            refine ⟨2059966661418074526537881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1373311107612049684358587 2059966661418074526537881)
            ·
              refine ⟨1544974996063555894903411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2059966661418074526537881 1544974996063555894903411)
              ·
                refine ⟨2317462494095333842355117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1544974996063555894903411 2317462494095333842355117)
                ·
                  refine ⟨869048435285750190883169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2317462494095333842355117 869048435285750190883169)
                  ·
                    refine ⟨651786326464312643162377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 869048435285750190883169 651786326464312643162377)
                    ·
                      refine ⟨488839744848234482371783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 651786326464312643162377 488839744848234482371783)
                      ·
                        rfl

theorem cell23_952012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_952012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952012 prefixEnd_952012 := by exact prefixLift 952012
  have htrace : WordTrace (prefixWord ++ tailWord_952012) baseStart_952012 baseEnd_952012 := by
    simpa [prefixWord, tailWord_952012, baseEnd_952012] using wordTrace_append hprefix tailTrace_952012
  have hstable : (prefixWord ++ tailWord_952012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952012).length < 2 ^ (prefixWord ++ tailWord_952012).sum := by decide
  have hdescent : baseEnd_952012 < baseStart_952012 := by decide
  rcases family_descends (prefixWord ++ tailWord_952012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952022 : List Nat := [5, 2, 1, 3, 1, 2, 1, 1, 1, 6]
def baseStart_952022 : Nat := 118140960795 + 952022 * 2 ^ 59
def prefixEnd_952022 : Nat := 4983230072969 + 3 ^ 40 * 952022 * 2
def baseEnd_952022 : Nat := 162948293218259814415579

theorem tailTrace_952022 : CollatzResearch.WordTrace tailWord_952022 prefixEnd_952022 162948293218259814415579 := by
  unfold tailWord_952022
  simp only [CollatzResearch.WordTrace]
  refine ⟨2170193434812147578629145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23148729971329574172044213 2170193434812147578629145)
  ·
    refine ⟨1627645076109110683971859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2170193434812147578629145 1627645076109110683971859)
    ·
      refine ⟨2441467614163666025957789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1627645076109110683971859 2441467614163666025957789)
      ·
        refine ⟨915550355311374759734171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2441467614163666025957789 915550355311374759734171)
        ·
          refine ⟨1373325532967062139601257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 915550355311374759734171 1373325532967062139601257)
          ·
            refine ⟨1029994149725296604700943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1373325532967062139601257 1029994149725296604700943)
            ·
              refine ⟨1544991224587944907051415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1029994149725296604700943 1544991224587944907051415)
              ·
                refine ⟨2317486836881917360577123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1544991224587944907051415 2317486836881917360577123)
                ·
                  refine ⟨3476230255322876040865685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2317486836881917360577123 3476230255322876040865685)
                  ·
                    refine ⟨162948293218259814415579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3476230255322876040865685 162948293218259814415579)
                    ·
                      rfl

theorem cell23_952022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_952022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952022 prefixEnd_952022 := by exact prefixLift 952022
  have htrace : WordTrace (prefixWord ++ tailWord_952022) baseStart_952022 baseEnd_952022 := by
    simpa [prefixWord, tailWord_952022, baseEnd_952022] using wordTrace_append hprefix tailTrace_952022
  have hstable : (prefixWord ++ tailWord_952022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952022).length < 2 ^ (prefixWord ++ tailWord_952022).sum := by decide
  have hdescent : baseEnd_952022 < baseStart_952022 := by decide
  rcases family_descends (prefixWord ++ tailWord_952022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952035 : List Nat := [1, 1, 1, 7, 3, 1, 2, 7]
def baseStart_952035 : Nat := 118140960795 + 952035 * 2 ^ 59
def prefixEnd_952035 : Nat := 4983230072969 + 3 ^ 40 * 952035 * 2
def baseEnd_952035 : Nat := 18105613144566218236451

theorem tailTrace_952035 : CollatzResearch.WordTrace tailWord_952035 prefixEnd_952035 18105613144566218236451 := by
  unfold tailWord_952035
  simp only [CollatzResearch.WordTrace]
  refine ⟨34723569105947264478289559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23149046070631509652193039 34723569105947264478289559)
  ·
    refine ⟨52085353658920896717434339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34723569105947264478289559 52085353658920896717434339)
    ·
      refine ⟨78128030488381345076151509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52085353658920896717434339 78128030488381345076151509)
      ·
        refine ⟨1831125714571437775222301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 78128030488381345076151509 1831125714571437775222301)
        ·
          refine ⟨686672142964289165708363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1831125714571437775222301 686672142964289165708363)
          ·
            refine ⟨1030008214446433748562545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686672142964289165708363 1030008214446433748562545)
            ·
              refine ⟨772506160834825311421909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1030008214446433748562545 772506160834825311421909)
              ·
                refine ⟨18105613144566218236451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 772506160834825311421909 18105613144566218236451)
                ·
                  rfl

theorem cell23_952035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 7].length) (baseStart_952035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952035 prefixEnd_952035 := by exact prefixLift 952035
  have htrace : WordTrace (prefixWord ++ tailWord_952035) baseStart_952035 baseEnd_952035 := by
    simpa [prefixWord, tailWord_952035, baseEnd_952035] using wordTrace_append hprefix tailTrace_952035
  have hstable : (prefixWord ++ tailWord_952035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952035).length < 2 ^ (prefixWord ++ tailWord_952035).sum := by decide
  have hdescent : baseEnd_952035 < baseStart_952035 := by decide
  rcases family_descends (prefixWord ++ tailWord_952035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952044 : List Nat := [2, 2, 1, 1, 2, 2, 2, 2, 1, 8]
def baseStart_952044 : Nat := 118140960795 + 952044 * 2 ^ 59
def prefixEnd_952044 : Nat := 4983230072969 + 3 ^ 40 * 952044 * 2
def baseEnd_952044 : Nat := 162952058743059452390545

theorem tailTrace_952044 : CollatzResearch.WordTrace tailWord_952044 prefixEnd_952044 162952058743059452390545 := by
  unfold tailWord_952044
  simp only [CollatzResearch.WordTrace]
  refine ⟨17361948681457329507683593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23149264908609772676911457 17361948681457329507683593)
  ·
    refine ⟨13021461511092997130762695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17361948681457329507683593 13021461511092997130762695)
    ·
      refine ⟨19532192266639495696144043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13021461511092997130762695 19532192266639495696144043)
      ·
        refine ⟨29298288399959243544216065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19532192266639495696144043 29298288399959243544216065)
        ·
          refine ⟨21973716299969432658162049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29298288399959243544216065 21973716299969432658162049)
          ·
            refine ⟨16480287224977074493621537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21973716299969432658162049 16480287224977074493621537)
            ·
              refine ⟨12360215418732805870216153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16480287224977074493621537 12360215418732805870216153)
              ·
                refine ⟨9270161564049604402662115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12360215418732805870216153 9270161564049604402662115)
                ·
                  refine ⟨13905242346074406603993173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9270161564049604402662115 13905242346074406603993173)
                  ·
                    refine ⟨162952058743059452390545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13905242346074406603993173 162952058743059452390545)
                    ·
                      rfl

theorem cell23_952044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 8].length) (baseStart_952044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952044 prefixEnd_952044 := by exact prefixLift 952044
  have htrace : WordTrace (prefixWord ++ tailWord_952044) baseStart_952044 baseEnd_952044 := by
    simpa [prefixWord, tailWord_952044, baseEnd_952044] using wordTrace_append hprefix tailTrace_952044
  have hstable : (prefixWord ++ tailWord_952044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952044).length < 2 ^ (prefixWord ++ tailWord_952044).sum := by decide
  have hdescent : baseEnd_952044 < baseStart_952044 := by decide
  rcases family_descends (prefixWord ++ tailWord_952044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952125 : List Nat := [1, 4, 1, 4, 1, 2, 1, 4, 5]
def baseStart_952125 : Nat := 118140960795 + 952125 * 2 ^ 59
def prefixEnd_952125 : Nat := 4983230072969 + 3 ^ 40 * 952125 * 2
def baseEnd_952125 : Nat := 54321974240243615584307

theorem tailTrace_952125 : CollatzResearch.WordTrace tailWord_952125 prefixEnd_952125 54321974240243615584307 := by
  unfold tailWord_952125
  simp only [CollatzResearch.WordTrace]
  refine ⟨34726851675621209849065829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23151234450414139899377219 34726851675621209849065829)
  ·
    refine ⟨6511284689178976846699843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34726851675621209849065829 6511284689178976846699843)
    ·
      refine ⟨9766927033768465270049765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6511284689178976846699843 9766927033768465270049765)
      ·
        refine ⟨1831298818831587238134331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9766927033768465270049765 1831298818831587238134331)
        ·
          refine ⟨2746948228247380857201497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1831298818831587238134331 2746948228247380857201497)
          ·
            refine ⟨2060211171185535642901123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2746948228247380857201497 2060211171185535642901123)
            ·
              refine ⟨3090316756778303464351685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2060211171185535642901123 3090316756778303464351685)
              ·
                refine ⟨579434391895931899565941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3090316756778303464351685 579434391895931899565941)
                ·
                  refine ⟨54321974240243615584307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 579434391895931899565941 54321974240243615584307)
                  ·
                    rfl

theorem cell23_952125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 4, 5].length) (baseStart_952125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952125 prefixEnd_952125 := by exact prefixLift 952125
  have htrace : WordTrace (prefixWord ++ tailWord_952125) baseStart_952125 baseEnd_952125 := by
    simpa [prefixWord, tailWord_952125, baseEnd_952125] using wordTrace_append hprefix tailTrace_952125
  have hstable : (prefixWord ++ tailWord_952125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952125).length < 2 ^ (prefixWord ++ tailWord_952125).sum := by decide
  have hdescent : baseEnd_952125 < baseStart_952125 := by decide
  rcases family_descends (prefixWord ++ tailWord_952125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952131 : List Nat := [1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 5]
def baseStart_952131 : Nat := 118140960795 + 952131 * 2 ^ 59
def prefixEnd_952131 : Nat := 4983230072969 + 3 ^ 40 * 952131 * 2
def baseEnd_952131 : Nat := 488900849046119516783735

theorem tailTrace_952131 : CollatzResearch.WordTrace tailWord_952131 prefixEnd_952131 488900849046119516783735 := by
  unfold tailWord_952131
  simp only [CollatzResearch.WordTrace]
  refine ⟨34727070513599472873784247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23151380342399648582522831 34727070513599472873784247)
  ·
    refine ⟨52090605770399209310676371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34727070513599472873784247 52090605770399209310676371)
    ·
      refine ⟨78135908655598813966014557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52090605770399209310676371 78135908655598813966014557)
      ·
        refine ⟨29300965745849555237255459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78135908655598813966014557 29300965745849555237255459)
        ·
          refine ⟨43951448618774332855883189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29300965745849555237255459 43951448618774332855883189)
          ·
            refine ⟨4120448308010093705239049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43951448618774332855883189 4120448308010093705239049)
            ·
              refine ⟨3090336231007570278929287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4120448308010093705239049 3090336231007570278929287)
              ·
                refine ⟨4635504346511355418393931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3090336231007570278929287 4635504346511355418393931)
                ·
                  refine ⟨6953256519767033127590897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4635504346511355418393931 6953256519767033127590897)
                  ·
                    refine ⟨5214942389825274845693173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6953256519767033127590897 5214942389825274845693173)
                    ·
                      refine ⟨488900849046119516783735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5214942389825274845693173 488900849046119516783735)
                      ·
                        rfl

theorem cell23_952131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_952131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952131 prefixEnd_952131 := by exact prefixLift 952131
  have htrace : WordTrace (prefixWord ++ tailWord_952131) baseStart_952131 baseEnd_952131 := by
    simpa [prefixWord, tailWord_952131, baseEnd_952131] using wordTrace_append hprefix tailTrace_952131
  have hstable : (prefixWord ++ tailWord_952131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952131).length < 2 ^ (prefixWord ++ tailWord_952131).sum := by decide
  have hdescent : baseEnd_952131 < baseStart_952131 := by decide
  rcases family_descends (prefixWord ++ tailWord_952131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952168 : List Nat := [2, 1, 4, 2, 1, 1, 1, 2, 5, 4]
def baseStart_952168 : Nat := 118140960795 + 952168 * 2 ^ 59
def prefixEnd_952168 : Nat := 4983230072969 + 3 ^ 40 * 952168 * 2
def baseEnd_952168 : Nat := 162973282610111957340355

theorem tailTrace_952168 : CollatzResearch.WordTrace tailWord_952168 prefixEnd_952168 162973282610111957340355 := by
  unfold tailWord_952168
  simp only [CollatzResearch.WordTrace]
  refine ⟨17364210007232714096440579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23152280009643618795254105 17364210007232714096440579)
  ·
    refine ⟨26046315010849071144660869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17364210007232714096440579 26046315010849071144660869)
    ·
      refine ⟨4883684064534200839623913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26046315010849071144660869 4883684064534200839623913)
      ·
        refine ⟨3662763048400650629717935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4883684064534200839623913 3662763048400650629717935)
        ·
          refine ⟨5494144572600975944576903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3662763048400650629717935 5494144572600975944576903)
          ·
            refine ⟨8241216858901463916865355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5494144572600975944576903 8241216858901463916865355)
            ·
              refine ⟨12361825288352195875298033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8241216858901463916865355 12361825288352195875298033)
              ·
                refine ⟨9271368966264146906473525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12361825288352195875298033 9271368966264146906473525)
                ·
                  refine ⟨869190840587263772481893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9271368966264146906473525 869190840587263772481893)
                  ·
                    refine ⟨162973282610111957340355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 869190840587263772481893 162973282610111957340355)
                    ·
                      rfl

theorem cell23_952168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_952168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952168 prefixEnd_952168 := by exact prefixLift 952168
  have htrace : WordTrace (prefixWord ++ tailWord_952168) baseStart_952168 baseEnd_952168 := by
    simpa [prefixWord, tailWord_952168, baseEnd_952168] using wordTrace_append hprefix tailTrace_952168
  have hstable : (prefixWord ++ tailWord_952168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952168).length < 2 ^ (prefixWord ++ tailWord_952168).sum := by decide
  have hdescent : baseEnd_952168 < baseStart_952168 := by decide
  rcases family_descends (prefixWord ++ tailWord_952168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952178 : List Nat := [3, 2, 1, 2, 1, 1, 1, 3, 4, 2, 3]
def baseStart_952178 : Nat := 118140960795 + 952178 * 2 ^ 59
def prefixEnd_952178 : Nat := 4983230072969 + 3 ^ 40 * 952178 * 2
def baseEnd_952178 : Nat := 488924982636880832896019

theorem tailTrace_952178 : CollatzResearch.WordTrace tailWord_952178 prefixEnd_952178 488924982636880832896019 := by
  unfold tailWord_952178
  simp only [CollatzResearch.WordTrace]
  refine ⟨8682196186107299975186297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23152523162952799933830125 8682196186107299975186297)
  ·
    refine ⟨6511647139580474981389723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8682196186107299975186297 6511647139580474981389723)
    ·
      refine ⟨9767470709370712472084585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6511647139580474981389723 9767470709370712472084585)
      ·
        refine ⟨7325603032028034354063439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9767470709370712472084585 7325603032028034354063439)
        ·
          refine ⟨10988404548042051531095159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7325603032028034354063439 10988404548042051531095159)
          ·
            refine ⟨16482606822063077296642739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10988404548042051531095159 16482606822063077296642739)
            ·
              refine ⟨24723910233094615944964109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16482606822063077296642739 24723910233094615944964109)
              ·
                refine ⟨9271466337410480979361541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24723910233094615944964109 9271466337410480979361541)
                ·
                  refine ⟨1738399938264465183630289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9271466337410480979361541 1738399938264465183630289)
                  ·
                    refine ⟨1303799953698348887722717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1738399938264465183630289 1303799953698348887722717)
                    ·
                      refine ⟨488924982636880832896019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1303799953698348887722717 488924982636880832896019)
                      ·
                        rfl

theorem cell23_952178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_952178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952178 prefixEnd_952178 := by exact prefixLift 952178
  have htrace : WordTrace (prefixWord ++ tailWord_952178) baseStart_952178 baseEnd_952178 := by
    simpa [prefixWord, tailWord_952178, baseEnd_952178] using wordTrace_append hprefix tailTrace_952178
  have hstable : (prefixWord ++ tailWord_952178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952178).length < 2 ^ (prefixWord ++ tailWord_952178).sum := by decide
  have hdescent : baseEnd_952178 < baseStart_952178 := by decide
  rcases family_descends (prefixWord ++ tailWord_952178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952185 : List Nat := [1, 2, 1, 3, 2, 2, 1, 6, 1, 4]
def baseStart_952185 : Nat := 118140960795 + 952185 * 2 ^ 59
def prefixEnd_952185 : Nat := 4983230072969 + 3 ^ 40 * 952185 * 2
def baseEnd_952185 : Nat := 162976192333820768502829

theorem tailTrace_952185 : CollatzResearch.WordTrace tailWord_952185 prefixEnd_952185 162976192333820768502829 := by
  unfold tailWord_952185
  simp only [CollatzResearch.WordTrace]
  refine ⟨34729040055403840096250009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23152693370269226730833339 34729040055403840096250009)
  ·
    refine ⟨26046780041552880072187507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34729040055403840096250009 26046780041552880072187507)
    ·
      refine ⟨39070170062329320108281261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26046780041552880072187507 39070170062329320108281261)
      ·
        refine ⟨14651313773373495040605473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39070170062329320108281261 14651313773373495040605473)
        ·
          refine ⟨10988485330030121280454105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14651313773373495040605473 10988485330030121280454105)
          ·
            refine ⟨8241363997522590960340579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10988485330030121280454105 8241363997522590960340579)
            ·
              refine ⟨12362045996283886440510869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8241363997522590960340579 12362045996283886440510869)
              ·
                refine ⟨579470906075807176898947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12362045996283886440510869 579470906075807176898947)
                ·
                  refine ⟨869206359113710765348421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 579470906075807176898947 869206359113710765348421)
                  ·
                    refine ⟨162976192333820768502829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 869206359113710765348421 162976192333820768502829)
                    ·
                      rfl

theorem cell23_952185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 6, 1, 4].length) (baseStart_952185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952185 prefixEnd_952185 := by exact prefixLift 952185
  have htrace : WordTrace (prefixWord ++ tailWord_952185) baseStart_952185 baseEnd_952185 := by
    simpa [prefixWord, tailWord_952185, baseEnd_952185] using wordTrace_append hprefix tailTrace_952185
  have hstable : (prefixWord ++ tailWord_952185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952185).length < 2 ^ (prefixWord ++ tailWord_952185).sum := by decide
  have hdescent : baseEnd_952185 < baseStart_952185 := by decide
  rcases family_descends (prefixWord ++ tailWord_952185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952201 : List Nat := [1, 2, 1, 1, 5, 1, 1, 2, 1, 2, 6]
def baseStart_952201 : Nat := 118140960795 + 952201 * 2 ^ 59
def prefixEnd_952201 : Nat := 4983230072969 + 3 ^ 40 * 952201 * 2
def baseEnd_952201 : Nat := 488936792691934242908413

theorem tailTrace_952201 : CollatzResearch.WordTrace tailWord_952201 prefixEnd_952201 488936792691934242908413 := by
  unfold tailWord_952201
  simp only [CollatzResearch.WordTrace]
  refine ⟨34729623623345874828832457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23153082415563916552554971 34729623623345874828832457)
  ·
    refine ⟨26047217717509406121624343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34729623623345874828832457 26047217717509406121624343)
    ·
      refine ⟨39070826576264109182436515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26047217717509406121624343 39070826576264109182436515)
      ·
        refine ⟨58606239864396163773654773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39070826576264109182436515 58606239864396163773654773)
        ·
          refine ⟨5494334987287140353780135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58606239864396163773654773 5494334987287140353780135)
          ·
            refine ⟨8241502480930710530670203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5494334987287140353780135 8241502480930710530670203)
            ·
              refine ⟨12362253721396065796005305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8241502480930710530670203 12362253721396065796005305)
              ·
                refine ⟨9271690291047049347003979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12362253721396065796005305 9271690291047049347003979)
                ·
                  refine ⟨13907535436570574020505969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9271690291047049347003979 13907535436570574020505969)
                  ·
                    refine ⟨10430651577427930515379477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13907535436570574020505969 10430651577427930515379477)
                    ·
                      refine ⟨488936792691934242908413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10430651577427930515379477 488936792691934242908413)
                      ·
                        rfl

theorem cell23_952201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 2, 6].length) (baseStart_952201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952201 prefixEnd_952201 := by exact prefixLift 952201
  have htrace : WordTrace (prefixWord ++ tailWord_952201) baseStart_952201 baseEnd_952201 := by
    simpa [prefixWord, tailWord_952201, baseEnd_952201] using wordTrace_append hprefix tailTrace_952201
  have hstable : (prefixWord ++ tailWord_952201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952201).length < 2 ^ (prefixWord ++ tailWord_952201).sum := by decide
  have hdescent : baseEnd_952201 < baseStart_952201 := by decide
  rcases family_descends (prefixWord ++ tailWord_952201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
