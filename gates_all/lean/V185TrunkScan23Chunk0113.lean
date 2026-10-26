import V185TrunkScan23Chunk0112

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_668272 : List Nat := [2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 5]
def baseStart_668272 : Nat := 118140960795 + 668272 * 2 ^ 59
def prefixEnd_668272 : Nat := 4983230072969 + 3 ^ 40 * 668272 * 2
def baseEnd_668272 : Nat := 343144743941514616426679

theorem tailTrace_668272 : CollatzResearch.WordTrace tailWord_668272 prefixEnd_668272 343144743941514616426679 := by
  unfold tailWord_668272
  simp only [CollatzResearch.WordTrace]
  refine ⟨12186941117486075308107535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16249254823314767077476713 12186941117486075308107535)
  ·
    refine ⟨18280411676229112962161303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12186941117486075308107535 18280411676229112962161303)
    ·
      refine ⟨27420617514343669443241955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18280411676229112962161303 27420617514343669443241955)
      ·
        refine ⟨41130926271515504164862933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27420617514343669443241955 41130926271515504164862933)
        ·
          refine ⟨964006084488644628863975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 41130926271515504164862933 964006084488644628863975)
          ·
            refine ⟨1446009126732966943295963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 964006084488644628863975 1446009126732966943295963)
            ·
              refine ⟨2169013690099450414943945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1446009126732966943295963 2169013690099450414943945)
              ·
                refine ⟨1626760267574587811207959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2169013690099450414943945 1626760267574587811207959)
                ·
                  refine ⟨2440140401361881716811939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1626760267574587811207959 2440140401361881716811939)
                  ·
                    refine ⟨3660210602042822575217909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2440140401361881716811939 3660210602042822575217909)
                    ·
                      refine ⟨343144743941514616426679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3660210602042822575217909 343144743941514616426679)
                      ·
                        rfl

theorem cell23_668272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 5].length) (baseStart_668272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668272 prefixEnd_668272 := by exact prefixLift 668272
  have htrace : WordTrace (prefixWord ++ tailWord_668272) baseStart_668272 baseEnd_668272 := by
    simpa [prefixWord, tailWord_668272, baseEnd_668272] using wordTrace_append hprefix tailTrace_668272
  have hstable : (prefixWord ++ tailWord_668272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668272).length < 2 ^ (prefixWord ++ tailWord_668272).sum := by decide
  have hdescent : baseEnd_668272 < baseStart_668272 := by decide
  rcases family_descends (prefixWord ++ tailWord_668272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668289 : List Nat := [1, 2, 4, 2, 1, 1, 4, 2, 1, 2, 3]
def baseStart_668289 : Nat := 118140960795 + 668289 * 2 ^ 59
def prefixEnd_668289 : Nat := 4983230072969 + 3 ^ 40 * 668289 * 2
def baseEnd_668289 : Nat := 343153473112641049914101

theorem tailTrace_668289 : CollatzResearch.WordTrace tailWord_668289 prefixEnd_668289 343153473112641049914101 := by
  unfold tailWord_668289
  simp only [CollatzResearch.WordTrace]
  refine ⟨24374502275910562519583921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16249668183940375013055947 24374502275910562519583921)
  ·
    refine ⟨18280876706932921889687941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24374502275910562519583921 18280876706932921889687941)
    ·
      refine ⟨3427664382549922854316489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18280876706932921889687941 3427664382549922854316489)
      ·
        refine ⟨2570748286912442140737367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3427664382549922854316489 2570748286912442140737367)
        ·
          refine ⟨3856122430368663211106051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2570748286912442140737367 3856122430368663211106051)
          ·
            refine ⟨5784183645552994816659077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3856122430368663211106051 5784183645552994816659077)
            ·
              refine ⟨1084534433541186528123577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5784183645552994816659077 1084534433541186528123577)
              ·
                refine ⟨813400825155889896092683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1084534433541186528123577 813400825155889896092683)
                ·
                  refine ⟨1220101237733834844139025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 813400825155889896092683 1220101237733834844139025)
                  ·
                    refine ⟨915075928300376133104269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1220101237733834844139025 915075928300376133104269)
                    ·
                      refine ⟨343153473112641049914101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 915075928300376133104269 343153473112641049914101)
                      ·
                        rfl

theorem cell23_668289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_668289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668289 prefixEnd_668289 := by exact prefixLift 668289
  have htrace : WordTrace (prefixWord ++ tailWord_668289) baseStart_668289 baseEnd_668289 := by
    simpa [prefixWord, tailWord_668289, baseEnd_668289] using wordTrace_append hprefix tailTrace_668289
  have hstable : (prefixWord ++ tailWord_668289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668289).length < 2 ^ (prefixWord ++ tailWord_668289).sum := by decide
  have hdescent : baseEnd_668289 < baseStart_668289 := by decide
  rcases family_descends (prefixWord ++ tailWord_668289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668292 : List Nat := [2, 3, 2, 1, 3, 1, 4, 7]
def baseStart_668292 : Nat := 118140960795 + 668292 * 2 ^ 59
def prefixEnd_668292 : Nat := 4983230072969 + 3 ^ 40 * 668292 * 2
def baseEnd_668292 : Nat := 12709444946466834747281

theorem tailTrace_668292 : CollatzResearch.WordTrace tailWord_668292 prefixEnd_668292 12709444946466834747281 := by
  unfold tailWord_668292
  simp only [CollatzResearch.WordTrace]
  refine ⟨12187305847449847015971565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16249741129933129354628753 12187305847449847015971565)
  ·
    refine ⟨4570239692793692630989337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12187305847449847015971565 4570239692793692630989337)
    ·
      refine ⟨3427679769595269473242003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4570239692793692630989337 3427679769595269473242003)
      ·
        refine ⟨5141519654392904209863005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3427679769595269473242003 5141519654392904209863005)
        ·
          refine ⟨1928069870397339078698627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5141519654392904209863005 1928069870397339078698627)
          ·
            refine ⟨2892104805596008618047941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1928069870397339078698627 2892104805596008618047941)
            ·
              refine ⟨542269651049251615883989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2892104805596008618047941 542269651049251615883989)
              ·
                refine ⟨12709444946466834747281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 542269651049251615883989 12709444946466834747281)
                ·
                  rfl

theorem cell23_668292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 7].length) (baseStart_668292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668292 prefixEnd_668292 := by exact prefixLift 668292
  have htrace : WordTrace (prefixWord ++ tailWord_668292) baseStart_668292 baseEnd_668292 := by
    simpa [prefixWord, tailWord_668292, baseEnd_668292] using wordTrace_append hprefix tailTrace_668292
  have hstable : (prefixWord ++ tailWord_668292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668292).length < 2 ^ (prefixWord ++ tailWord_668292).sum := by decide
  have hdescent : baseEnd_668292 < baseStart_668292 := by decide
  rcases family_descends (prefixWord ++ tailWord_668292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668302 : List Nat := [4, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3]
def baseStart_668302 : Nat := 118140960795 + 668302 * 2 ^ 59
def prefixEnd_668302 : Nat := 4983230072969 + 3 ^ 40 * 668302 * 2
def baseEnd_668302 : Nat := 343160148361149499051541

theorem tailTrace_668302 : CollatzResearch.WordTrace tailWord_668302 prefixEnd_668302 343160148361149499051541 := by
  unfold tailWord_668302
  simp only [CollatzResearch.WordTrace]
  refine ⟨3046872053107933217475895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16249984283242310493204773 3046872053107933217475895)
  ·
    refine ⟨4570308079661899826213843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3046872053107933217475895 4570308079661899826213843)
    ·
      refine ⟨6855462119492849739320765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4570308079661899826213843 6855462119492849739320765)
      ·
        refine ⟨2570798294809818652245287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6855462119492849739320765 2570798294809818652245287)
        ·
          refine ⟨3856197442214727978367931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2570798294809818652245287 3856197442214727978367931)
          ·
            refine ⟨5784296163322091967551897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3856197442214727978367931 5784296163322091967551897)
            ·
              refine ⟨4338222122491568975663923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5784296163322091967551897 4338222122491568975663923)
              ·
                refine ⟨6507333183737353463495885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4338222122491568975663923 6507333183737353463495885)
                ·
                  refine ⟨2440249943901507548810957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6507333183737353463495885 2440249943901507548810957)
                  ·
                    refine ⟨915093728963065330804109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2440249943901507548810957 915093728963065330804109)
                    ·
                      refine ⟨343160148361149499051541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 915093728963065330804109 343160148361149499051541)
                      ·
                        rfl

theorem cell23_668302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_668302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668302 prefixEnd_668302 := by exact prefixLift 668302
  have htrace : WordTrace (prefixWord ++ tailWord_668302) baseStart_668302 baseEnd_668302 := by
    simpa [prefixWord, tailWord_668302, baseEnd_668302] using wordTrace_append hprefix tailTrace_668302
  have hstable : (prefixWord ++ tailWord_668302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668302).length < 2 ^ (prefixWord ++ tailWord_668302).sum := by decide
  have hdescent : baseEnd_668302 < baseStart_668302 := by decide
  rcases family_descends (prefixWord ++ tailWord_668302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668320 : List Nat := [2, 1, 1, 4, 4, 1, 3, 2, 1, 2, 2]
def baseStart_668320 : Nat := 118140960795 + 668320 * 2 ^ 59
def prefixEnd_668320 : Nat := 4983230072969 + 3 ^ 40 * 668320 * 2
def baseEnd_668320 : Nat := 343169391012930428626459

theorem tailTrace_668320 : CollatzResearch.WordTrace tailWord_668320 prefixEnd_668320 343169391012930428626459 := by
  unfold tailWord_668320
  simp only [CollatzResearch.WordTrace]
  refine ⟨12187816469399127406981207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16250421959198836542641609 12187816469399127406981207)
  ·
    refine ⟨18281724704098691110471811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12187816469399127406981207 18281724704098691110471811)
    ·
      refine ⟨27422587056148036665707717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18281724704098691110471811 27422587056148036665707717)
      ·
        refine ⟨5141735073027756874820197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27422587056148036665707717 5141735073027756874820197)
        ·
          refine ⟨964075326192704414028787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5141735073027756874820197 964075326192704414028787)
          ·
            refine ⟨1446112989289056621043181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 964075326192704414028787 1446112989289056621043181)
            ·
              refine ⟨542292370983396232891193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1446112989289056621043181 542292370983396232891193)
              ·
                refine ⟨406719278237547174668395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 542292370983396232891193 406719278237547174668395)
                ·
                  refine ⟨610078917356320762002593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 406719278237547174668395 610078917356320762002593)
                  ·
                    refine ⟨457559188017240571501945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 610078917356320762002593 457559188017240571501945)
                    ·
                      refine ⟨343169391012930428626459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 457559188017240571501945 343169391012930428626459)
                      ·
                        rfl

theorem cell23_668320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 2, 1, 2, 2].length) (baseStart_668320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668320 prefixEnd_668320 := by exact prefixLift 668320
  have htrace : WordTrace (prefixWord ++ tailWord_668320) baseStart_668320 baseEnd_668320 := by
    simpa [prefixWord, tailWord_668320, baseEnd_668320] using wordTrace_append hprefix tailTrace_668320
  have hstable : (prefixWord ++ tailWord_668320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668320).length < 2 ^ (prefixWord ++ tailWord_668320).sum := by decide
  have hdescent : baseEnd_668320 < baseStart_668320 := by decide
  rcases family_descends (prefixWord ++ tailWord_668320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668325 : List Nat := [1, 3, 1, 2, 1, 2, 1, 3, 2, 3, 4]
def baseStart_668325 : Nat := 118140960795 + 668325 * 2 ^ 59
def prefixEnd_668325 : Nat := 4983230072969 + 3 ^ 40 * 668325 * 2
def baseEnd_668325 : Nat := 343171958416202909063935

theorem tailTrace_668325 : CollatzResearch.WordTrace tailWord_668325 prefixEnd_668325 343171958416202909063935 := by
  unfold tailWord_668325
  simp only [CollatzResearch.WordTrace]
  refine ⟨24375815303780140667894429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16250543535853427111929619 24375815303780140667894429)
  ·
    refine ⟨9140930738917552750460411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24375815303780140667894429 9140930738917552750460411)
    ·
      refine ⟨13711396108376329125690617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9140930738917552750460411 13711396108376329125690617)
      ·
        refine ⟨10283547081282246844267963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13711396108376329125690617 10283547081282246844267963)
        ·
          refine ⟨15425320621923370266401945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10283547081282246844267963 15425320621923370266401945)
          ·
            refine ⟨11568990466442527699801459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15425320621923370266401945 11568990466442527699801459)
            ·
              refine ⟨17353485699663791549702189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11568990466442527699801459 17353485699663791549702189)
              ·
                refine ⟨6507557137373921831138321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17353485699663791549702189 6507557137373921831138321)
                ·
                  refine ⟨4880667853030441373353741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6507557137373921831138321 4880667853030441373353741)
                  ·
                    refine ⟨1830250444886415515007653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4880667853030441373353741 1830250444886415515007653)
                    ·
                      refine ⟨343171958416202909063935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1830250444886415515007653 343171958416202909063935)
                      ·
                        rfl

theorem cell23_668325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_668325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668325 prefixEnd_668325 := by exact prefixLift 668325
  have htrace : WordTrace (prefixWord ++ tailWord_668325) baseStart_668325 baseEnd_668325 := by
    simpa [prefixWord, tailWord_668325, baseEnd_668325] using wordTrace_append hprefix tailTrace_668325
  have hstable : (prefixWord ++ tailWord_668325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668325).length < 2 ^ (prefixWord ++ tailWord_668325).sum := by decide
  have hdescent : baseEnd_668325 < baseStart_668325 := by decide
  rcases family_descends (prefixWord ++ tailWord_668325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668330 : List Nat := [3, 1, 5, 2, 1, 2, 2, 1, 2, 4]
def baseStart_668330 : Nat := 118140960795 + 668330 * 2 ^ 59
def prefixEnd_668330 : Nat := 4983230072969 + 3 ^ 40 * 668330 * 2
def baseEnd_668330 : Nat := 114391508606491796500471

theorem tailTrace_668330 : CollatzResearch.WordTrace tailWord_668330 prefixEnd_668330 114391508606491796500471 := by
  unfold tailWord_668330
  simp only [CollatzResearch.WordTrace]
  refine ⟨6093999417190506630456611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16250665112508017681217629 6093999417190506630456611)
  ·
    refine ⟨9140999125785759945684917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6093999417190506630456611 9140999125785759945684917)
    ·
      refine ⟨856968668042414994907961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9140999125785759945684917 856968668042414994907961)
      ·
        refine ⟨642726501031811246180971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 856968668042414994907961 642726501031811246180971)
        ·
          refine ⟨964089751547716869271457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 642726501031811246180971 964089751547716869271457)
          ·
            refine ⟨723067313660787651953593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 964089751547716869271457 723067313660787651953593)
            ·
              refine ⟨542300485245590738965195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 723067313660787651953593 542300485245590738965195)
              ·
                refine ⟨813450727868386108447793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 542300485245590738965195 813450727868386108447793)
                ·
                  refine ⟨610088045901289581335845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 813450727868386108447793 610088045901289581335845)
                  ·
                    refine ⟨114391508606491796500471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 610088045901289581335845 114391508606491796500471)
                    ·
                      rfl

theorem cell23_668330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_668330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668330 prefixEnd_668330 := by exact prefixLift 668330
  have htrace : WordTrace (prefixWord ++ tailWord_668330) baseStart_668330 baseEnd_668330 := by
    simpa [prefixWord, tailWord_668330, baseEnd_668330] using wordTrace_append hprefix tailTrace_668330
  have hstable : (prefixWord ++ tailWord_668330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668330).length < 2 ^ (prefixWord ++ tailWord_668330).sum := by decide
  have hdescent : baseEnd_668330 < baseStart_668330 := by decide
  rcases family_descends (prefixWord ++ tailWord_668330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668359 : List Nat := [1, 1, 4, 1, 1, 1, 2, 4, 4, 2, 2]
def baseStart_668359 : Nat := 118140960795 + 668359 * 2 ^ 59
def prefixEnd_668359 : Nat := 4983230072969 + 3 ^ 40 * 668359 * 2
def baseEnd_668359 : Nat := 343189416758455776038779

theorem tailTrace_668359 : CollatzResearch.WordTrace tailWord_668359 prefixEnd_668359 343189416758455776038779 := by
  unfold tailWord_668359
  simp only [CollatzResearch.WordTrace]
  refine ⟨24377055385656964474632131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16251370257104642983088087 24377055385656964474632131)
  ·
    refine ⟨36565583078485446711948197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24377055385656964474632131 36565583078485446711948197)
    ·
      refine ⟨6856046827216021258490287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36565583078485446711948197 6856046827216021258490287)
      ·
        refine ⟨10284070240824031887735431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6856046827216021258490287 10284070240824031887735431)
        ·
          refine ⟨15426105361236047831603147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10284070240824031887735431 15426105361236047831603147)
          ·
            refine ⟨23139158041854071747404721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15426105361236047831603147 23139158041854071747404721)
            ·
              refine ⟨17354368531390553810553541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23139158041854071747404721 17354368531390553810553541)
              ·
                refine ⟨3253944099635728839478789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17354368531390553810553541 3253944099635728839478789)
                ·
                  refine ⟨610114518681699157402273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3253944099635728839478789 610114518681699157402273)
                  ·
                    refine ⟨457585889011274368051705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 610114518681699157402273 457585889011274368051705)
                    ·
                      refine ⟨343189416758455776038779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 457585889011274368051705 343189416758455776038779)
                      ·
                        rfl

theorem cell23_668359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 4, 2, 2].length) (baseStart_668359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668359 prefixEnd_668359 := by exact prefixLift 668359
  have htrace : WordTrace (prefixWord ++ tailWord_668359) baseStart_668359 baseEnd_668359 := by
    simpa [prefixWord, tailWord_668359, baseEnd_668359] using wordTrace_append hprefix tailTrace_668359
  have hstable : (prefixWord ++ tailWord_668359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668359).length < 2 ^ (prefixWord ++ tailWord_668359).sum := by decide
  have hdescent : baseEnd_668359 < baseStart_668359 := by decide
  rcases family_descends (prefixWord ++ tailWord_668359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668362 : List Nat := [3, 1, 2, 1, 4, 1, 2, 1, 2, 1, 5]
def baseStart_668362 : Nat := 118140960795 + 668362 * 2 ^ 59
def prefixEnd_668362 : Nat := 4983230072969 + 3 ^ 40 * 668362 * 2
def baseEnd_668362 : Nat := 343190957200419264301265

theorem tailTrace_668362 : CollatzResearch.WordTrace tailWord_668362 prefixEnd_668362 343190957200419264301265 := by
  unfold tailWord_668362
  simp only [CollatzResearch.WordTrace]
  refine ⟨6094291201161523996747835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16251443203097397324660893 6094291201161523996747835)
  ·
    refine ⟨9141436801742285995121753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6094291201161523996747835 9141436801742285995121753)
    ·
      refine ⟨6856077601306714496341315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9141436801742285995121753 6856077601306714496341315)
      ·
        refine ⟨10284116401960071744511973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6856077601306714496341315 10284116401960071744511973)
        ·
          refine ⟨1928271825367513452095995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10284116401960071744511973 1928271825367513452095995)
          ·
            refine ⟨2892407738051270178143993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1928271825367513452095995 2892407738051270178143993)
            ·
              refine ⟨2169305803538452633607995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2892407738051270178143993 2169305803538452633607995)
              ·
                refine ⟨3253958705307678950411993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2169305803538452633607995 3253958705307678950411993)
                ·
                  refine ⟨2440469028980759212808995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3253958705307678950411993 2440469028980759212808995)
                  ·
                    refine ⟨3660703543471138819213493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2440469028980759212808995 3660703543471138819213493)
                    ·
                      refine ⟨343190957200419264301265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3660703543471138819213493 343190957200419264301265)
                      ·
                        rfl

theorem cell23_668362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_668362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668362 prefixEnd_668362 := by exact prefixLift 668362
  have htrace : WordTrace (prefixWord ++ tailWord_668362) baseStart_668362 baseEnd_668362 := by
    simpa [prefixWord, tailWord_668362, baseEnd_668362] using wordTrace_append hprefix tailTrace_668362
  have hstable : (prefixWord ++ tailWord_668362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668362).length < 2 ^ (prefixWord ++ tailWord_668362).sum := by decide
  have hdescent : baseEnd_668362 < baseStart_668362 := by decide
  rcases family_descends (prefixWord ++ tailWord_668362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668376 : List Nat := [2, 1, 2, 2, 3, 2, 1, 4, 2, 2, 2]
def baseStart_668376 : Nat := 118140960795 + 668376 * 2 ^ 59
def prefixEnd_668376 : Nat := 4983230072969 + 3 ^ 40 * 668376 * 2
def baseEnd_668376 : Nat := 343198145929582209526201

theorem tailTrace_668376 : CollatzResearch.WordTrace tailWord_668376 prefixEnd_668376 343198145929582209526201 := by
  unfold tailWord_668376
  simp only [CollatzResearch.WordTrace]
  refine ⟨12188837713297688189000491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16251783617730250918667321 12188837713297688189000491)
  ·
    refine ⟨18283256569946532283500737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12188837713297688189000491 18283256569946532283500737)
    ·
      refine ⟨13712442427459899212625553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18283256569946532283500737 13712442427459899212625553)
      ·
        refine ⟨10284331820594924409469165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13712442427459899212625553 10284331820594924409469165)
        ·
          refine ⟨3856624432723096653550937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10284331820594924409469165 3856624432723096653550937)
          ·
            refine ⟨2892468324542322490163203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3856624432723096653550937 2892468324542322490163203)
            ·
              refine ⟨4338702486813483735244805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2892468324542322490163203 4338702486813483735244805)
              ·
                refine ⟨813506716277528200358401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4338702486813483735244805 813506716277528200358401)
                ·
                  refine ⟨610130037208146150268801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 813506716277528200358401 610130037208146150268801)
                  ·
                    refine ⟨457597527906109612701601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 610130037208146150268801 457597527906109612701601)
                    ·
                      refine ⟨343198145929582209526201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 457597527906109612701601 343198145929582209526201)
                      ·
                        rfl

theorem cell23_668376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 2, 2, 2].length) (baseStart_668376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668376 prefixEnd_668376 := by exact prefixLift 668376
  have htrace : WordTrace (prefixWord ++ tailWord_668376) baseStart_668376 baseEnd_668376 := by
    simpa [prefixWord, tailWord_668376, baseEnd_668376] using wordTrace_append hprefix tailTrace_668376
  have hstable : (prefixWord ++ tailWord_668376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668376).length < 2 ^ (prefixWord ++ tailWord_668376).sum := by decide
  have hdescent : baseEnd_668376 < baseStart_668376 := by decide
  rcases family_descends (prefixWord ++ tailWord_668376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668395 : List Nat := [1, 1, 1, 1, 2, 4, 1, 4, 1, 7]
def baseStart_668395 : Nat := 118140960795 + 668395 * 2 ^ 59
def prefixEnd_668395 : Nat := 4983230072969 + 3 ^ 40 * 668395 * 2
def baseEnd_668395 : Nat := 114402634020672545062871

theorem tailTrace_668395 : CollatzResearch.WordTrace tailWord_668395 prefixEnd_668395 114402634020672545062871 := by
  unfold tailWord_668395
  simp only [CollatzResearch.WordTrace]
  refine ⟨24378368413526542622942639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16252245609017695081961759 24378368413526542622942639)
  ·
    refine ⟨36567552620289813934413959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24378368413526542622942639 36567552620289813934413959)
    ·
      refine ⟨54851328930434720901620939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36567552620289813934413959 54851328930434720901620939)
      ·
        refine ⟨82276993395652081352431409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54851328930434720901620939 82276993395652081352431409)
        ·
          refine ⟨61707745046739061014323557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82276993395652081352431409 61707745046739061014323557)
          ·
            refine ⟨11570202196263573940185667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61707745046739061014323557 11570202196263573940185667)
            ·
              refine ⟨17355303294395360910278501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11570202196263573940185667 17355303294395360910278501)
              ·
                refine ⟨3254119367699130170677219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17355303294395360910278501 3254119367699130170677219)
                ·
                  refine ⟨4881179051548695256015829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3254119367699130170677219 4881179051548695256015829)
                  ·
                    refine ⟨114402634020672545062871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4881179051548695256015829 114402634020672545062871)
                    ·
                      rfl

theorem cell23_668395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 7].length) (baseStart_668395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668395 prefixEnd_668395 := by exact prefixLift 668395
  have htrace : WordTrace (prefixWord ++ tailWord_668395) baseStart_668395 baseEnd_668395 := by
    simpa [prefixWord, tailWord_668395, baseEnd_668395] using wordTrace_append hprefix tailTrace_668395
  have hstable : (prefixWord ++ tailWord_668395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668395).length < 2 ^ (prefixWord ++ tailWord_668395).sum := by decide
  have hdescent : baseEnd_668395 < baseStart_668395 := by decide
  rcases family_descends (prefixWord ++ tailWord_668395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668412 : List Nat := [2, 2, 2, 1, 3, 3, 1, 1, 1, 7]
def baseStart_668412 : Nat := 118140960795 + 668412 * 2 ^ 59
def prefixEnd_668412 : Nat := 4983230072969 + 3 ^ 40 * 668412 * 2
def baseEnd_668412 : Nat := 114405543744381356225345

theorem tailTrace_668412 : CollatzResearch.WordTrace tailWord_668412 prefixEnd_668412 114405543744381356225345 := by
  unfold tailWord_668412
  simp only [CollatzResearch.WordTrace]
  refine ⟨12189494227232477263155745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16252658969643303017540993 12189494227232477263155745)
  ·
    refine ⟨9142120670424357947366809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12189494227232477263155745 9142120670424357947366809)
    ·
      refine ⟨6856590502818268460525107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9142120670424357947366809 6856590502818268460525107)
      ·
        refine ⟨10284885754227402690787661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6856590502818268460525107 10284885754227402690787661)
        ·
          refine ⟨3856832157835276009045373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10284885754227402690787661 3856832157835276009045373)
          ·
            refine ⟨1446312059188228503392015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3856832157835276009045373 1446312059188228503392015)
            ·
              refine ⟨2169468088782342755088023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1446312059188228503392015 2169468088782342755088023)
              ·
                refine ⟨3254202133173514132632035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2169468088782342755088023 3254202133173514132632035)
                ·
                  refine ⟨4881303199760271198948053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3254202133173514132632035 4881303199760271198948053)
                  ·
                    refine ⟨114405543744381356225345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4881303199760271198948053 114405543744381356225345)
                    ·
                      rfl

theorem cell23_668412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_668412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668412 prefixEnd_668412 := by exact prefixLift 668412
  have htrace : WordTrace (prefixWord ++ tailWord_668412) baseStart_668412 baseEnd_668412 := by
    simpa [prefixWord, tailWord_668412, baseEnd_668412] using wordTrace_append hprefix tailTrace_668412
  have hstable : (prefixWord ++ tailWord_668412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668412).length < 2 ^ (prefixWord ++ tailWord_668412).sum := by decide
  have hdescent : baseEnd_668412 < baseStart_668412 := by decide
  rcases family_descends (prefixWord ++ tailWord_668412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668449 : List Nat := [1, 2, 3, 2, 1, 2, 1, 3, 2, 4, 2]
def baseStart_668449 : Nat := 118140960795 + 668449 * 2 ^ 59
def prefixEnd_668449 : Nat := 4983230072969 + 3 ^ 40 * 668449 * 2
def baseEnd_668449 : Nat := 343235630017360423913365

theorem tailTrace_668449 : CollatzResearch.WordTrace tailWord_668449 prefixEnd_668449 343235630017360423913365 := by
  unfold tailWord_668449
  simp only [CollatzResearch.WordTrace]
  refine ⟨24380337955330909845408401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16253558636887273230272267 24380337955330909845408401)
  ·
    refine ⟨18285253466498182384056301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24380337955330909845408401 18285253466498182384056301)
    ·
      refine ⟨6856970049936818394021113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18285253466498182384056301 6856970049936818394021113)
      ·
        refine ⟨5142727537452613795515835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6856970049936818394021113 5142727537452613795515835)
        ·
          refine ⟨7714091306178920693273753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5142727537452613795515835 7714091306178920693273753)
          ·
            refine ⟨5785568479634190519955315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7714091306178920693273753 5785568479634190519955315)
            ·
              refine ⟨8678352719451285779932973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5785568479634190519955315 8678352719451285779932973)
              ·
                refine ⟨3254382269794232167474865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8678352719451285779932973 3254382269794232167474865)
                ·
                  refine ⟨2440786702345674125606149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3254382269794232167474865 2440786702345674125606149)
                  ·
                    refine ⟨457647506689813898551153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2440786702345674125606149 457647506689813898551153)
                    ·
                      refine ⟨343235630017360423913365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 457647506689813898551153 343235630017360423913365)
                      ·
                        rfl

theorem cell23_668449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_668449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668449 prefixEnd_668449 := by exact prefixLift 668449
  have htrace : WordTrace (prefixWord ++ tailWord_668449) baseStart_668449 baseEnd_668449 := by
    simpa [prefixWord, tailWord_668449, baseEnd_668449] using wordTrace_append hprefix tailTrace_668449
  have hstable : (prefixWord ++ tailWord_668449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668449).length < 2 ^ (prefixWord ++ tailWord_668449).sum := by decide
  have hdescent : baseEnd_668449 < baseStart_668449 := by decide
  rcases family_descends (prefixWord ++ tailWord_668449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668469 : List Nat := [1, 3, 3, 1, 3, 1, 2, 1, 1, 4, 3]
def baseStart_668469 : Nat := 118140960795 + 668469 * 2 ^ 59
def prefixEnd_668469 : Nat := 4983230072969 + 3 ^ 40 * 668469 * 2
def baseEnd_668469 : Nat := 343245899630450345663273

theorem tailTrace_668469 : CollatzResearch.WordTrace tailWord_668469 prefixEnd_668469 343245899630450345663273 := by
  unfold tailWord_668469
  simp only [CollatzResearch.WordTrace]
  refine ⟨24381067415258453261136461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16254044943505635507424307 24381067415258453261136461)
  ·
    refine ⟨9142900280721919972926173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24381067415258453261136461 9142900280721919972926173)
    ·
      refine ⟨3428587605270719989847315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9142900280721919972926173 3428587605270719989847315)
      ·
        refine ⟨5142881407906079984770973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3428587605270719989847315 5142881407906079984770973)
        ·
          refine ⟨1928580527964779994289115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5142881407906079984770973 1928580527964779994289115)
          ·
            refine ⟨2892870791947169991433673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1928580527964779994289115 2892870791947169991433673)
            ·
              refine ⟨2169653093960377493575255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2892870791947169991433673 2169653093960377493575255)
              ·
                refine ⟨3254479640940566240362883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2169653093960377493575255 3254479640940566240362883)
                ·
                  refine ⟨4881719461410849360544325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3254479640940566240362883 4881719461410849360544325)
                  ·
                    refine ⟨915322399014534255102061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4881719461410849360544325 915322399014534255102061)
                    ·
                      refine ⟨343245899630450345663273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 915322399014534255102061 343245899630450345663273)
                      ·
                        rfl

theorem cell23_668469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_668469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668469 prefixEnd_668469 := by exact prefixLift 668469
  have htrace : WordTrace (prefixWord ++ tailWord_668469) baseStart_668469 baseEnd_668469 := by
    simpa [prefixWord, tailWord_668469, baseEnd_668469] using wordTrace_append hprefix tailTrace_668469
  have hstable : (prefixWord ++ tailWord_668469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668469).length < 2 ^ (prefixWord ++ tailWord_668469).sum := by decide
  have hdescent : baseEnd_668469 < baseStart_668469 := by decide
  rcases family_descends (prefixWord ++ tailWord_668469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668506 : List Nat := [3, 1, 1, 2, 1, 6, 2, 1, 6]
def baseStart_668506 : Nat := 118140960795 + 668506 * 2 ^ 59
def prefixEnd_668506 : Nat := 4983230072969 + 3 ^ 40 * 668506 * 2
def baseEnd_668506 : Nat := 38140544268296300100067

theorem tailTrace_668506 : CollatzResearch.WordTrace tailWord_668506 prefixEnd_668506 38140544268296300100067 := by
  unfold tailWord_668506
  simp only [CollatzResearch.WordTrace]
  refine ⟨6095604229031102145058343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16254944610749605720155581 6095604229031102145058343)
  ·
    refine ⟨9143406343546653217587515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6095604229031102145058343 9143406343546653217587515)
    ·
      refine ⟨13715109515319979826381273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9143406343546653217587515 13715109515319979826381273)
      ·
        refine ⟨10286332136489984869785955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13715109515319979826381273 10286332136489984869785955)
        ·
          refine ⟨15429498204734977304678933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10286332136489984869785955 15429498204734977304678933)
          ·
            refine ⟨723257728346952061156825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15429498204734977304678933 723257728346952061156825)
            ·
              refine ⟨542443296260214045867619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 723257728346952061156825 542443296260214045867619)
              ·
                refine ⟨813664944390321068801429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 542443296260214045867619 813664944390321068801429)
                ·
                  refine ⟨38140544268296300100067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 813664944390321068801429 38140544268296300100067)
                  ·
                    rfl

theorem cell23_668506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 6].length) (baseStart_668506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668506 prefixEnd_668506 := by exact prefixLift 668506
  have htrace : WordTrace (prefixWord ++ tailWord_668506) baseStart_668506 baseEnd_668506 := by
    simpa [prefixWord, tailWord_668506, baseEnd_668506] using wordTrace_append hprefix tailTrace_668506
  have hstable : (prefixWord ++ tailWord_668506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668506).length < 2 ^ (prefixWord ++ tailWord_668506).sum := by decide
  have hdescent : baseEnd_668506 < baseStart_668506 := by decide
  rcases family_descends (prefixWord ++ tailWord_668506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668519 : List Nat := [1, 1, 5, 1, 2, 3, 1, 1, 3, 5]
def baseStart_668519 : Nat := 118140960795 + 668519 * 2 ^ 59
def prefixEnd_668519 : Nat := 4983230072969 + 3 ^ 40 * 668519 * 2
def baseEnd_668519 : Nat := 114423857887725050012681

theorem tailTrace_668519 : CollatzResearch.WordTrace tailWord_668519 prefixEnd_668519 114423857887725050012681 := by
  unfold tailWord_668519
  simp only [CollatzResearch.WordTrace]
  refine ⟨24382891065077311800456611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16255260710051541200304407 24382891065077311800456611)
  ·
    refine ⟨36574336597615967700684917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24382891065077311800456611 36574336597615967700684917)
    ·
      refine ⟨3428844056026496971939211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36574336597615967700684917 3428844056026496971939211)
      ·
        refine ⟨5143266084039745457908817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3428844056026496971939211 5143266084039745457908817)
        ·
          refine ⟨3857449563029809093431613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5143266084039745457908817 3857449563029809093431613)
          ·
            refine ⟨1446543586136178410036855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3857449563029809093431613 1446543586136178410036855)
            ·
              refine ⟨2169815379204267615055283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1446543586136178410036855 2169815379204267615055283)
              ·
                refine ⟨3254723068806401422582925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2169815379204267615055283 3254723068806401422582925)
                ·
                  refine ⟨1220521150802400533468597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3254723068806401422582925 1220521150802400533468597)
                  ·
                    refine ⟨114423857887725050012681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1220521150802400533468597 114423857887725050012681)
                    ·
                      rfl

theorem cell23_668519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_668519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668519 prefixEnd_668519 := by exact prefixLift 668519
  have htrace : WordTrace (prefixWord ++ tailWord_668519) baseStart_668519 baseEnd_668519 := by
    simpa [prefixWord, tailWord_668519, baseEnd_668519] using wordTrace_append hprefix tailTrace_668519
  have hstable : (prefixWord ++ tailWord_668519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668519).length < 2 ^ (prefixWord ++ tailWord_668519).sum := by decide
  have hdescent : baseEnd_668519 < baseStart_668519 := by decide
  rcases family_descends (prefixWord ++ tailWord_668519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668539 : List Nat := [1, 1, 1, 1, 1, 5, 2, 5, 1, 1, 4]
def baseStart_668539 : Nat := 118140960795 + 668539 * 2 ^ 59
def prefixEnd_668539 : Nat := 4983230072969 + 3 ^ 40 * 668539 * 2
def baseEnd_668539 : Nat := 343281843276265071787951

theorem tailTrace_668539 : CollatzResearch.WordTrace tailWord_668539 prefixEnd_668539 343281843276265071787951 := by
  unfold tailWord_668539
  simp only [CollatzResearch.WordTrace]
  refine ⟨24383620525004855216184671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16255747016669903477456447 24383620525004855216184671)
  ·
    refine ⟨36575430787507282824277007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24383620525004855216184671 36575430787507282824277007)
    ·
      refine ⟨54863146181260924236415511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36575430787507282824277007 54863146181260924236415511)
      ·
        refine ⟨82294719271891386354623267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54863146181260924236415511 82294719271891386354623267)
        ·
          refine ⟨123442078907837079531934901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82294719271891386354623267 123442078907837079531934901)
          ·
            refine ⟨11572694897609726206118897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 123442078907837079531934901 11572694897609726206118897)
            ·
              refine ⟨8679521173207294654589173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11572694897609726206118897 8679521173207294654589173)
              ·
                refine ⟨813705109988183873867735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8679521173207294654589173 813705109988183873867735)
                ·
                  refine ⟨1220557664982275810801603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 813705109988183873867735 1220557664982275810801603)
                  ·
                    refine ⟨1830836497473413716202405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1220557664982275810801603 1830836497473413716202405)
                    ·
                      refine ⟨343281843276265071787951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1830836497473413716202405 343281843276265071787951)
                      ·
                        rfl

theorem cell23_668539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 1, 4].length) (baseStart_668539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668539 prefixEnd_668539 := by exact prefixLift 668539
  have htrace : WordTrace (prefixWord ++ tailWord_668539) baseStart_668539 baseEnd_668539 := by
    simpa [prefixWord, tailWord_668539, baseEnd_668539] using wordTrace_append hprefix tailTrace_668539
  have hstable : (prefixWord ++ tailWord_668539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668539).length < 2 ^ (prefixWord ++ tailWord_668539).sum := by decide
  have hdescent : baseEnd_668539 < baseStart_668539 := by decide
  rcases family_descends (prefixWord ++ tailWord_668539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668573 : List Nat := [1, 4, 2, 1, 2, 1, 3, 2, 3, 2, 2]
def baseStart_668573 : Nat := 118140960795 + 668573 * 2 ^ 59
def prefixEnd_668573 : Nat := 4983230072969 + 3 ^ 40 * 668573 * 2
def baseEnd_668573 : Nat := 343299301618517938762795

theorem tailTrace_668573 : CollatzResearch.WordTrace tailWord_668573 prefixEnd_668573 343299301618517938762795 := by
  unfold tailWord_668573
  simp only [CollatzResearch.WordTrace]
  refine ⟨24384860606881679022922373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16256573737921119348614915 24384860606881679022922373)
  ·
    refine ⟨4572161363790314816797945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24384860606881679022922373 4572161363790314816797945)
    ·
      refine ⟨3429121022842736112598459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4572161363790314816797945 3429121022842736112598459)
      ·
        refine ⟨5143681534264104168897689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3429121022842736112598459 5143681534264104168897689)
        ·
          refine ⟨3857761150698078126673267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5143681534264104168897689 3857761150698078126673267)
          ·
            refine ⟨5786641726047117190009901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3857761150698078126673267 5786641726047117190009901)
            ·
              refine ⟨2169990647267668946253713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5786641726047117190009901 2169990647267668946253713)
              ·
                refine ⟨1627492985450751709690285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2169990647267668946253713 1627492985450751709690285)
                ·
                  refine ⟨610309869544031891133857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1627492985450751709690285 610309869544031891133857)
                  ·
                    refine ⟨457732402158023918350393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 610309869544031891133857 457732402158023918350393)
                    ·
                      refine ⟨343299301618517938762795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 457732402158023918350393 343299301618517938762795)
                      ·
                        rfl

theorem cell23_668573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_668573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668573 prefixEnd_668573 := by exact prefixLift 668573
  have htrace : WordTrace (prefixWord ++ tailWord_668573) baseStart_668573 baseEnd_668573 := by
    simpa [prefixWord, tailWord_668573, baseEnd_668573] using wordTrace_append hprefix tailTrace_668573
  have hstable : (prefixWord ++ tailWord_668573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668573).length < 2 ^ (prefixWord ++ tailWord_668573).sum := by decide
  have hdescent : baseEnd_668573 < baseStart_668573 := by decide
  rcases family_descends (prefixWord ++ tailWord_668573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668593 : List Nat := [1, 2, 2, 4, 3, 1, 1, 3, 1, 2, 3]
def baseStart_668593 : Nat := 118140960795 + 668593 * 2 ^ 59
def prefixEnd_668593 : Nat := 4983230072969 + 3 ^ 40 * 668593 * 2
def baseEnd_668593 : Nat := 343309571231607860512703

theorem tailTrace_668593 : CollatzResearch.WordTrace tailWord_668593 prefixEnd_668593 343309571231607860512703 := by
  unfold tailWord_668593
  simp only [CollatzResearch.WordTrace]
  refine ⟨24385590066809222438650433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16257060044539481625766955 24385590066809222438650433)
  ·
    refine ⟨18289192550106916828987825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24385590066809222438650433 18289192550106916828987825)
    ·
      refine ⟨13716894412580187621740869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18289192550106916828987825 13716894412580187621740869)
      ·
        refine ⟨2571917702358785179076413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13716894412580187621740869 2571917702358785179076413)
        ·
          refine ⟨964469138384544442153655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2571917702358785179076413 964469138384544442153655)
          ·
            refine ⟨1446703707576816663230483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 964469138384544442153655 1446703707576816663230483)
            ·
              refine ⟨2170055561365224994845725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1446703707576816663230483 2170055561365224994845725)
              ·
                refine ⟨813770835511959373067147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2170055561365224994845725 813770835511959373067147)
                ·
                  refine ⟨1220656253267939059600721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 813770835511959373067147 1220656253267939059600721)
                  ·
                    refine ⟨915492189950954294700541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1220656253267939059600721 915492189950954294700541)
                    ·
                      refine ⟨343309571231607860512703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 915492189950954294700541 343309571231607860512703)
                      ·
                        rfl

theorem cell23_668593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_668593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668593 prefixEnd_668593 := by exact prefixLift 668593
  have htrace : WordTrace (prefixWord ++ tailWord_668593) baseStart_668593 baseEnd_668593 := by
    simpa [prefixWord, tailWord_668593, baseEnd_668593] using wordTrace_append hprefix tailTrace_668593
  have hstable : (prefixWord ++ tailWord_668593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668593).length < 2 ^ (prefixWord ++ tailWord_668593).sum := by decide
  have hdescent : baseEnd_668593 < baseStart_668593 := by decide
  rcases family_descends (prefixWord ++ tailWord_668593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668596 : List Nat := [2, 5, 2, 1, 1, 2, 10]
def baseStart_668596 : Nat := 118140960795 + 668596 * 2 ^ 59
def prefixEnd_668596 : Nat := 4983230072969 + 3 ^ 40 * 668596 * 2
def baseEnd_668596 : Nat := 4238408786093473441669

theorem tailTrace_668596 : CollatzResearch.WordTrace tailWord_668596 prefixEnd_668596 4238408786093473441669 := by
  unfold tailWord_668596
  simp only [CollatzResearch.WordTrace]
  refine ⟨12192849742899176975504821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16257132990532235967339761 12192849742899176975504821)
  ·
    refine ⟨1143079663396797841453577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12192849742899176975504821 1143079663396797841453577)
    ·
      refine ⟨857309747547598381090183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1143079663396797841453577 857309747547598381090183)
      ·
        refine ⟨1285964621321397571635275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 857309747547598381090183 1285964621321397571635275)
        ·
          refine ⟨1928946931982096357452913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1285964621321397571635275 1928946931982096357452913)
          ·
            refine ⟨1446710198986572268089685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1928946931982096357452913 1446710198986572268089685)
            ·
              refine ⟨4238408786093473441669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1446710198986572268089685 4238408786093473441669)
              ·
                rfl

theorem cell23_668596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 10].length) (baseStart_668596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668596 prefixEnd_668596 := by exact prefixLift 668596
  have htrace : WordTrace (prefixWord ++ tailWord_668596) baseStart_668596 baseEnd_668596 := by
    simpa [prefixWord, tailWord_668596, baseEnd_668596] using wordTrace_append hprefix tailTrace_668596
  have hstable : (prefixWord ++ tailWord_668596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668596).length < 2 ^ (prefixWord ++ tailWord_668596).sum := by decide
  have hdescent : baseEnd_668596 < baseStart_668596 := by decide
  rcases family_descends (prefixWord ++ tailWord_668596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668633 : List Nat := [1, 2, 1, 2, 5, 1, 1, 4, 1, 3, 2]
def baseStart_668633 : Nat := 118140960795 + 668633 * 2 ^ 59
def prefixEnd_668633 : Nat := 4983230072969 + 3 ^ 40 * 668633 * 2
def baseEnd_668633 : Nat := 343330110457787704012519

theorem tailTrace_668633 : CollatzResearch.WordTrace tailWord_668633 prefixEnd_668633 343330110457787704012519 := by
  unfold tailWord_668633
  simp only [CollatzResearch.WordTrace]
  refine ⟨24387048986664309270106553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16258032657776206180071035 24387048986664309270106553)
  ·
    refine ⟨18290286739998231952579915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24387048986664309270106553 18290286739998231952579915)
    ·
      refine ⟨27435430109997347928869873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18290286739998231952579915 27435430109997347928869873)
      ·
        refine ⟨20576572582498010946652405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27435430109997347928869873 20576572582498010946652405)
        ·
          refine ⟨1929053679609188526248663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20576572582498010946652405 1929053679609188526248663)
          ·
            refine ⟨2893580519413782789372995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1929053679609188526248663 2893580519413782789372995)
            ·
              refine ⟨4340370779120674184059493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2893580519413782789372995 4340370779120674184059493)
              ·
                refine ⟨813819521085126409511155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4340370779120674184059493 813819521085126409511155)
                ·
                  refine ⟨1220729281627689614266733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 813819521085126409511155 1220729281627689614266733)
                  ·
                    refine ⟨457773480610383605350025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1220729281627689614266733 457773480610383605350025)
                    ·
                      refine ⟨343330110457787704012519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 457773480610383605350025 343330110457787704012519)
                      ·
                        rfl

theorem cell23_668633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 3, 2].length) (baseStart_668633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668633 prefixEnd_668633 := by exact prefixLift 668633
  have htrace : WordTrace (prefixWord ++ tailWord_668633) baseStart_668633 baseEnd_668633 := by
    simpa [prefixWord, tailWord_668633, baseEnd_668633] using wordTrace_append hprefix tailTrace_668633
  have hstable : (prefixWord ++ tailWord_668633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668633).length < 2 ^ (prefixWord ++ tailWord_668633).sum := by decide
  have hdescent : baseEnd_668633 < baseStart_668633 := by decide
  rcases family_descends (prefixWord ++ tailWord_668633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668680 : List Nat := [2, 1, 3, 2, 1, 4, 1, 3, 2, 2, 2]
def baseStart_668680 : Nat := 118140960795 + 668680 * 2 ^ 59
def prefixEnd_668680 : Nat := 4983230072969 + 3 ^ 40 * 668680 * 2
def baseEnd_668680 : Nat := 343354244048549020124803

theorem tailTrace_668680 : CollatzResearch.WordTrace tailWord_668680 prefixEnd_668680 343354244048549020124803 := by
  unfold tailWord_668680
  simp only [CollatzResearch.WordTrace]
  refine ⟨12194381608747018148533747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16259175478329357531378329 12194381608747018148533747)
  ·
    refine ⟨18291572413120527222800621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12194381608747018148533747 18291572413120527222800621)
    ·
      refine ⟨6859339654920197708550233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18291572413120527222800621 6859339654920197708550233)
      ·
        refine ⟨5144504741190148281412675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6859339654920197708550233 5144504741190148281412675)
        ·
          refine ⟨7716757111785222422119013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5144504741190148281412675 7716757111785222422119013)
          ·
            refine ⟨1446891958459729204147315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7716757111785222422119013 1446891958459729204147315)
            ·
              refine ⟨2170337937689593806220973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1446891958459729204147315 2170337937689593806220973)
              ·
                refine ⟨813876726633597677332865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2170337937689593806220973 813876726633597677332865)
                ·
                  refine ⟨610407544975198257999649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 813876726633597677332865 610407544975198257999649)
                  ·
                    refine ⟨457805658731398693499737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 610407544975198257999649 457805658731398693499737)
                    ·
                      refine ⟨343354244048549020124803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 457805658731398693499737 343354244048549020124803)
                      ·
                        rfl

theorem cell23_668680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_668680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668680 prefixEnd_668680 := by exact prefixLift 668680
  have htrace : WordTrace (prefixWord ++ tailWord_668680) baseStart_668680 baseEnd_668680 := by
    simpa [prefixWord, tailWord_668680, baseEnd_668680] using wordTrace_append hprefix tailTrace_668680
  have hstable : (prefixWord ++ tailWord_668680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668680).length < 2 ^ (prefixWord ++ tailWord_668680).sum := by decide
  have hdescent : baseEnd_668680 < baseStart_668680 := by decide
  rcases family_descends (prefixWord ++ tailWord_668680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668709 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 3, 2, 5]
def baseStart_668709 : Nat := 118140960795 + 668709 * 2 ^ 59
def prefixEnd_668709 : Nat := 4983230072969 + 3 ^ 40 * 668709 * 2
def baseEnd_668709 : Nat := 343369134987529406662169

theorem tailTrace_668709 : CollatzResearch.WordTrace tailWord_668709 prefixEnd_668709 343369134987529406662169 := by
  unfold tailWord_668709
  simp only [CollatzResearch.WordTrace]
  refine ⟨24389820934388974249873181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16259880622925982833248787 24389820934388974249873181)
  ·
    refine ⟨9146182850395865343702443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24389820934388974249873181 9146182850395865343702443)
    ·
      refine ⟨13719274275593798015553665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9146182850395865343702443 13719274275593798015553665)
      ·
        refine ⟨10289455706695348511665249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13719274275593798015553665 10289455706695348511665249)
        ·
          refine ⟨7717091780021511383748937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10289455706695348511665249 7717091780021511383748937)
          ·
            refine ⟨5787818835016133537811703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7717091780021511383748937 5787818835016133537811703)
            ·
              refine ⟨8681728252524200306717555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5787818835016133537811703 8681728252524200306717555)
              ·
                refine ⟨13022592378786300460076333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8681728252524200306717555 13022592378786300460076333)
                ·
                  refine ⟨4883472142044862672528625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13022592378786300460076333 4883472142044862672528625)
                  ·
                    refine ⟨3662604106533647004396469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4883472142044862672528625 3662604106533647004396469)
                    ·
                      refine ⟨343369134987529406662169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3662604106533647004396469 343369134987529406662169)
                      ·
                        rfl

theorem cell23_668709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_668709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668709 prefixEnd_668709 := by exact prefixLift 668709
  have htrace : WordTrace (prefixWord ++ tailWord_668709) baseStart_668709 baseEnd_668709 := by
    simpa [prefixWord, tailWord_668709, baseEnd_668709] using wordTrace_append hprefix tailTrace_668709
  have hstable : (prefixWord ++ tailWord_668709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668709).length < 2 ^ (prefixWord ++ tailWord_668709).sum := by decide
  have hdescent : baseEnd_668709 < baseStart_668709 := by decide
  rcases family_descends (prefixWord ++ tailWord_668709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668746 : List Nat := [3, 1, 2, 1, 1, 2, 3, 1, 5, 4]
def baseStart_668746 : Nat := 118140960795 + 668746 * 2 ^ 59
def prefixEnd_668746 : Nat := 4983230072969 + 3 ^ 40 * 668746 * 2
def baseEnd_668746 : Nat := 114462711257248587299833

theorem tailTrace_668746 : CollatzResearch.WordTrace tailWord_668746 prefixEnd_668746 114462711257248587299833 := by
  unfold tailWord_668746
  simp only [CollatzResearch.WordTrace]
  refine ⟨6097792608813732392242523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16260780290169953045980061 6097792608813732392242523)
  ·
    refine ⟨9146688913220598588363785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6097792608813732392242523 9146688913220598588363785)
    ·
      refine ⟨6860016684915448941272839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9146688913220598588363785 6860016684915448941272839)
      ·
        refine ⟨10290025027373173411909259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6860016684915448941272839 10290025027373173411909259)
        ·
          refine ⟨15435037541059760117863889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10290025027373173411909259 15435037541059760117863889)
          ·
            refine ⟨11576278155794820088397917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15435037541059760117863889 11576278155794820088397917)
            ·
              refine ⟨4341104308423057533149219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11576278155794820088397917 4341104308423057533149219)
              ·
                refine ⟨6511656462634586299723829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4341104308423057533149219 6511656462634586299723829)
                ·
                  refine ⟨610467793371992465599109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6511656462634586299723829 610467793371992465599109)
                  ·
                    refine ⟨114462711257248587299833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 610467793371992465599109 114462711257248587299833)
                    ·
                      rfl

theorem cell23_668746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_668746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668746 prefixEnd_668746 := by exact prefixLift 668746
  have htrace : WordTrace (prefixWord ++ tailWord_668746) baseStart_668746 baseEnd_668746 := by
    simpa [prefixWord, tailWord_668746, baseEnd_668746] using wordTrace_append hprefix tailTrace_668746
  have hstable : (prefixWord ++ tailWord_668746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668746).length < 2 ^ (prefixWord ++ tailWord_668746).sum := by decide
  have hdescent : baseEnd_668746 < baseStart_668746 := by decide
  rcases family_descends (prefixWord ++ tailWord_668746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668759 : List Nat := [1, 1, 3, 2, 2, 1, 1, 4, 8]
def baseStart_668759 : Nat := 118140960795 + 668759 * 2 ^ 59
def prefixEnd_668759 : Nat := 4983230072969 + 3 ^ 40 * 668759 * 2
def baseEnd_668759 : Nat := 38154978780028245670771

theorem tailTrace_668759 : CollatzResearch.WordTrace tailWord_668759 prefixEnd_668759 38154978780028245670771 := by
  unfold tailWord_668759
  simp only [CollatzResearch.WordTrace]
  refine ⟨24391644584207832789193331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16261096389471888526128887 24391644584207832789193331)
  ·
    refine ⟨36587466876311749183789997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24391644584207832789193331 36587466876311749183789997)
    ·
      refine ⟨13720300078616905943921249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36587466876311749183789997 13720300078616905943921249)
      ·
        refine ⟨10290225058962679457940937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13720300078616905943921249 10290225058962679457940937)
        ·
          refine ⟨7717668794222009593455703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10290225058962679457940937 7717668794222009593455703)
          ·
            refine ⟨11576503191333014390183555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7717668794222009593455703 11576503191333014390183555)
            ·
              refine ⟨17364754786999521585275333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11576503191333014390183555 17364754786999521585275333)
              ·
                refine ⟨3255891522562410297239125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17364754786999521585275333 3255891522562410297239125)
                ·
                  refine ⟨38154978780028245670771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3255891522562410297239125 38154978780028245670771)
                  ·
                    rfl

theorem cell23_668759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 8].length) (baseStart_668759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668759 prefixEnd_668759 := by exact prefixLift 668759
  have htrace : WordTrace (prefixWord ++ tailWord_668759) baseStart_668759 baseEnd_668759 := by
    simpa [prefixWord, tailWord_668759, baseEnd_668759] using wordTrace_append hprefix tailTrace_668759
  have hstable : (prefixWord ++ tailWord_668759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668759).length < 2 ^ (prefixWord ++ tailWord_668759).sum := by decide
  have hdescent : baseEnd_668759 < baseStart_668759 := by decide
  rcases family_descends (prefixWord ++ tailWord_668759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668770 : List Nat := [3, 3, 2, 2, 1, 1, 1, 2, 2, 4, 2]
def baseStart_668770 : Nat := 118140960795 + 668770 * 2 ^ 59
def prefixEnd_668770 : Nat := 4983230072969 + 3 ^ 40 * 668770 * 2
def baseEnd_668770 : Nat := 343400457307453667999389

theorem tailTrace_668770 : CollatzResearch.WordTrace tailWord_668770 prefixEnd_668770 343400457307453667999389 := by
  unfold tailWord_668770
  simp only [CollatzResearch.WordTrace]
  refine ⟨6098011446791995416960941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16261363858111987778562509 6098011446791995416960941)
  ·
    refine ⟨2286754292546998281360353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6098011446791995416960941 2286754292546998281360353)
    ·
      refine ⟨1715065719410248711020265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2286754292546998281360353 1715065719410248711020265)
      ·
        refine ⟨1286299289557686533265199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1715065719410248711020265 1286299289557686533265199)
        ·
          refine ⟨1929448934336529799897799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1286299289557686533265199 1929448934336529799897799)
          ·
            refine ⟨2894173401504794699846699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1929448934336529799897799 2894173401504794699846699)
            ·
              refine ⟨4341260102257192049770049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2894173401504794699846699 4341260102257192049770049)
              ·
                refine ⟨3255945076692894037327537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4341260102257192049770049 3255945076692894037327537)
                ·
                  refine ⟨2441958807519670527995653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3255945076692894037327537 2441958807519670527995653)
                  ·
                    refine ⟨457867276409938223999185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2441958807519670527995653 457867276409938223999185)
                    ·
                      refine ⟨343400457307453667999389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 457867276409938223999185 343400457307453667999389)
                      ·
                        rfl

theorem cell23_668770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_668770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668770 prefixEnd_668770 := by exact prefixLift 668770
  have htrace : WordTrace (prefixWord ++ tailWord_668770) baseStart_668770 baseEnd_668770 := by
    simpa [prefixWord, tailWord_668770, baseEnd_668770] using wordTrace_append hprefix tailTrace_668770
  have hstable : (prefixWord ++ tailWord_668770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668770).length < 2 ^ (prefixWord ++ tailWord_668770).sum := by decide
  have hdescent : baseEnd_668770 < baseStart_668770 := by decide
  rcases family_descends (prefixWord ++ tailWord_668770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668803 : List Nat := [1, 1, 1, 3, 3, 2, 1, 4, 3, 1, 3]
def baseStart_668803 : Nat := 118140960795 + 668803 * 2 ^ 59
def prefixEnd_668803 : Nat := 4983230072969 + 3 ^ 40 * 668803 * 2
def baseEnd_668803 : Nat := 343417402169052038886737

theorem tailTrace_668803 : CollatzResearch.WordTrace tailWord_668803 prefixEnd_668803 343417402169052038886737 := by
  unfold tailWord_668803
  simp only [CollatzResearch.WordTrace]
  refine ⟨24393249396048428303795063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16262166264032285535863375 24393249396048428303795063)
  ·
    refine ⟨36589874094072642455692595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24393249396048428303795063 36589874094072642455692595)
    ·
      refine ⟨54884811141108963683538893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36589874094072642455692595 54884811141108963683538893)
      ·
        refine ⟨20581804177915861381327085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54884811141108963683538893 20581804177915861381327085)
        ·
          refine ⟨7718176566718448017997657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20581804177915861381327085 7718176566718448017997657)
          ·
            refine ⟨5788632425038836013498243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7718176566718448017997657 5788632425038836013498243)
            ·
              refine ⟨8682948637558254020247365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5788632425038836013498243 8682948637558254020247365)
              ·
                refine ⟨1628052869542172628796381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8682948637558254020247365 1628052869542172628796381)
                ·
                  refine ⟨610519826078314735798643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1628052869542172628796381 610519826078314735798643)
                  ·
                    refine ⟨915779739117472103697965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 610519826078314735798643 915779739117472103697965)
                    ·
                      refine ⟨343417402169052038886737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 915779739117472103697965 343417402169052038886737)
                      ·
                        rfl

theorem cell23_668803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 3, 1, 3].length) (baseStart_668803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668803 prefixEnd_668803 := by exact prefixLift 668803
  have htrace : WordTrace (prefixWord ++ tailWord_668803) baseStart_668803 baseEnd_668803 := by
    simpa [prefixWord, tailWord_668803, baseEnd_668803] using wordTrace_append hprefix tailTrace_668803
  have hstable : (prefixWord ++ tailWord_668803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668803).length < 2 ^ (prefixWord ++ tailWord_668803).sum := by decide
  have hdescent : baseEnd_668803 < baseStart_668803 := by decide
  rcases family_descends (prefixWord ++ tailWord_668803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668823 : List Nat := [1, 1, 3, 3, 3, 1, 2, 3, 1, 5]
def baseStart_668823 : Nat := 118140960795 + 668823 * 2 ^ 59
def prefixEnd_668823 : Nat := 4983230072969 + 3 ^ 40 * 668823 * 2
def baseEnd_668823 : Nat := 114475890594047320212215

theorem tailTrace_668823 : CollatzResearch.WordTrace tailWord_668823 prefixEnd_668823 114475890594047320212215 := by
  unfold tailWord_668823
  simp only [CollatzResearch.WordTrace]
  refine ⟨24393978855975971719523123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16262652570650647813015415 24393978855975971719523123)
  ·
    refine ⟨36590968283963957579284685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24393978855975971719523123 36590968283963957579284685)
    ·
      refine ⟨13721613106486484092231757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36590968283963957579284685 13721613106486484092231757)
      ·
        refine ⟨5145604914932431534586909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13721613106486484092231757 5145604914932431534586909)
        ·
          refine ⟨1929601843099661825470091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5145604914932431534586909 1929601843099661825470091)
          ·
            refine ⟨2894402764649492738205137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1929601843099661825470091 2894402764649492738205137)
            ·
              refine ⟨2170802073487119553653853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2894402764649492738205137 2170802073487119553653853)
              ·
                refine ⟨814050777557669832620195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2170802073487119553653853 814050777557669832620195)
                ·
                  refine ⟨1221076166336504748930293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 814050777557669832620195 1221076166336504748930293)
                  ·
                    refine ⟨114475890594047320212215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1221076166336504748930293 114475890594047320212215)
                    ·
                      rfl

theorem cell23_668823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 5].length) (baseStart_668823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668823 prefixEnd_668823 := by exact prefixLift 668823
  have htrace : WordTrace (prefixWord ++ tailWord_668823) baseStart_668823 baseEnd_668823 := by
    simpa [prefixWord, tailWord_668823, baseEnd_668823] using wordTrace_append hprefix tailTrace_668823
  have hstable : (prefixWord ++ tailWord_668823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668823).length < 2 ^ (prefixWord ++ tailWord_668823).sum := by decide
  have hdescent : baseEnd_668823 < baseStart_668823 := by decide
  rcases family_descends (prefixWord ++ tailWord_668823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668860 : List Nat := [2, 2, 2, 3, 2, 1, 3, 2, 1, 1, 4]
def baseStart_668860 : Nat := 118140960795 + 668860 * 2 ^ 59
def prefixEnd_668860 : Nat := 4983230072969 + 3 ^ 40 * 668860 * 2
def baseEnd_668860 : Nat := 343446670566358315873975

theorem tailTrace_668860 : CollatzResearch.WordTrace tailWord_668860 prefixEnd_668860 343446670566358315873975 := by
  unfold tailWord_668860
  simp only [CollatzResearch.WordTrace]
  refine ⟨12197664178420963519310017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16263552237894618025746689 12197664178420963519310017)
  ·
    refine ⟨9148248133815722639482513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12197664178420963519310017 9148248133815722639482513)
    ·
      refine ⟨6861186100361791979611885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9148248133815722639482513 6861186100361791979611885)
      ·
        refine ⟨2572944787635671992354457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6861186100361791979611885 2572944787635671992354457)
        ·
          refine ⟨1929708590726753994265843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2572944787635671992354457 1929708590726753994265843)
          ·
            refine ⟨2894562886090130991398765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1929708590726753994265843 2894562886090130991398765)
            ·
              refine ⟨1085461082283799121774537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2894562886090130991398765 1085461082283799121774537)
              ·
                refine ⟨814095811712849341330903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1085461082283799121774537 814095811712849341330903)
                ·
                  refine ⟨1221143717569274011996355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 814095811712849341330903 1221143717569274011996355)
                  ·
                    refine ⟨1831715576353911017994533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1221143717569274011996355 1831715576353911017994533)
                    ·
                      refine ⟨343446670566358315873975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1831715576353911017994533 343446670566358315873975)
                      ·
                        rfl

theorem cell23_668860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_668860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668860 prefixEnd_668860 := by exact prefixLift 668860
  have htrace : WordTrace (prefixWord ++ tailWord_668860) baseStart_668860 baseEnd_668860 := by
    simpa [prefixWord, tailWord_668860, baseEnd_668860] using wordTrace_append hprefix tailTrace_668860
  have hstable : (prefixWord ++ tailWord_668860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668860).length < 2 ^ (prefixWord ++ tailWord_668860).sum := by decide
  have hdescent : baseEnd_668860 < baseStart_668860 := by decide
  rcases family_descends (prefixWord ++ tailWord_668860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668896 : List Nat := [2, 1, 1, 3, 1, 4, 1, 1, 2, 7]
def baseStart_668896 : Nat := 118140960795 + 668896 * 2 ^ 59
def prefixEnd_668896 : Nat := 4983230072969 + 3 ^ 40 * 668896 * 2
def baseEnd_668896 : Nat := 114488385289973391674603

theorem tailTrace_668896 : CollatzResearch.WordTrace tailWord_668896 prefixEnd_668896 114488385289973391674603 := by
  unfold tailWord_668896
  simp only [CollatzResearch.WordTrace]
  refine ⟨12198320692355752593465271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16264427589807670124620361 12198320692355752593465271)
  ·
    refine ⟨18297481038533628890197907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12198320692355752593465271 18297481038533628890197907)
    ·
      refine ⟨27446221557800443335296861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18297481038533628890197907 27446221557800443335296861)
      ·
        refine ⟨10292333084175166250736323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27446221557800443335296861 10292333084175166250736323)
        ·
          refine ⟨15438499626262749376104485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10292333084175166250736323 15438499626262749376104485)
          ·
            refine ⟨2894718679924265508019591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15438499626262749376104485 2894718679924265508019591)
            ·
              refine ⟨4342078019886398262029387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2894718679924265508019591 4342078019886398262029387)
              ·
                refine ⟨6513117029829597393044081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4342078019886398262029387 6513117029829597393044081)
                ·
                  refine ⟨4884837772372198044783061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6513117029829597393044081 4884837772372198044783061)
                  ·
                    refine ⟨114488385289973391674603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4884837772372198044783061 114488385289973391674603)
                    ·
                      rfl

theorem cell23_668896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 2, 7].length) (baseStart_668896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668896 prefixEnd_668896 := by exact prefixLift 668896
  have htrace : WordTrace (prefixWord ++ tailWord_668896) baseStart_668896 baseEnd_668896 := by
    simpa [prefixWord, tailWord_668896, baseEnd_668896] using wordTrace_append hprefix tailTrace_668896
  have hstable : (prefixWord ++ tailWord_668896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668896).length < 2 ^ (prefixWord ++ tailWord_668896).sum := by decide
  have hdescent : baseEnd_668896 < baseStart_668896 := by decide
  rcases family_descends (prefixWord ++ tailWord_668896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668963 : List Nat := [1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 4]
def baseStart_668963 : Nat := 118140960795 + 668963 * 2 ^ 59
def prefixEnd_668963 : Nat := 4983230072969 + 3 ^ 40 * 668963 * 2
def baseEnd_668963 : Nat := 343499559073771412886001

theorem tailTrace_668963 : CollatzResearch.WordTrace tailWord_668963 prefixEnd_668963 343499559073771412886001 := by
  unfold tailWord_668963
  simp only [CollatzResearch.WordTrace]
  refine ⟨24399085075468775629619543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16266056716979183753079695 24399085075468775629619543)
  ·
    refine ⟨36598627613203163444429315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24399085075468775629619543 36598627613203163444429315)
    ·
      refine ⟨54897941419804745166643973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36598627613203163444429315 54897941419804745166643973)
      ·
        refine ⟨10293364016213389718745745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54897941419804745166643973 10293364016213389718745745)
        ·
          refine ⟨7720023012160042289059309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10293364016213389718745745 7720023012160042289059309)
          ·
            refine ⟨2895008629560015858397241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7720023012160042289059309 2895008629560015858397241)
            ·
              refine ⟨2171256472170011893797931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2895008629560015858397241 2171256472170011893797931)
              ·
                refine ⟨3256884708255017840696897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2171256472170011893797931 3256884708255017840696897)
                ·
                  refine ⟨2442663531191263380522673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3256884708255017840696897 2442663531191263380522673)
                  ·
                    refine ⟨1831997648393447535392005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2442663531191263380522673 1831997648393447535392005)
                    ·
                      refine ⟨343499559073771412886001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1831997648393447535392005 343499559073771412886001)
                      ·
                        rfl

theorem cell23_668963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_668963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668963 prefixEnd_668963 := by exact prefixLift 668963
  have htrace : WordTrace (prefixWord ++ tailWord_668963) baseStart_668963 baseEnd_668963 := by
    simpa [prefixWord, tailWord_668963, baseEnd_668963] using wordTrace_append hprefix tailTrace_668963
  have hstable : (prefixWord ++ tailWord_668963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668963).length < 2 ^ (prefixWord ++ tailWord_668963).sum := by decide
  have hdescent : baseEnd_668963 < baseStart_668963 := by decide
  rcases family_descends (prefixWord ++ tailWord_668963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669010 : List Nat := [3, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2]
def baseStart_669010 : Nat := 118140960795 + 669010 * 2 ^ 59
def prefixEnd_669010 : Nat := 4983230072969 + 3 ^ 40 * 669010 * 2
def baseEnd_669010 : Nat := 343523692664532728998285

theorem tailTrace_669010 : CollatzResearch.WordTrace tailWord_669010 prefixEnd_669010 343523692664532728998285 := by
  unfold tailWord_669010
  simp only [CollatzResearch.WordTrace]
  refine ⟨6100199826574625664145121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16267199537532335104386989 6100199826574625664145121)
  ·
    refine ⟨4575149869930969248108841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6100199826574625664145121 4575149869930969248108841)
    ·
      refine ⟨3431362402448226936081631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4575149869930969248108841 3431362402448226936081631)
      ·
        refine ⟨5147043603672340404122447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3431362402448226936081631 5147043603672340404122447)
        ·
          refine ⟨7720565405508510606183671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5147043603672340404122447 7720565405508510606183671)
          ·
            refine ⟨11580848108262765909275507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7720565405508510606183671 11580848108262765909275507)
            ·
              refine ⟨17371272162394148863913261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11580848108262765909275507 17371272162394148863913261)
              ·
                refine ⟨6514227060897805823967473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17371272162394148863913261 6514227060897805823967473)
                ·
                  refine ⟨4885670295673354367975605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6514227060897805823967473 4885670295673354367975605)
                  ·
                    refine ⟨458031590219376971997713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4885670295673354367975605 458031590219376971997713)
                    ·
                      refine ⟨343523692664532728998285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 458031590219376971997713 343523692664532728998285)
                      ·
                        rfl

theorem cell23_669010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_669010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669010 prefixEnd_669010 := by exact prefixLift 669010
  have htrace : WordTrace (prefixWord ++ tailWord_669010) baseStart_669010 baseEnd_669010 := by
    simpa [prefixWord, tailWord_669010, baseEnd_669010] using wordTrace_append hprefix tailTrace_669010
  have hstable : (prefixWord ++ tailWord_669010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669010).length < 2 ^ (prefixWord ++ tailWord_669010).sum := by decide
  have hdescent : baseEnd_669010 < baseStart_669010 := by decide
  rcases family_descends (prefixWord ++ tailWord_669010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669013 : List Nat := [1, 3, 2, 2, 3, 1, 1, 1, 1, 1, 7]
def baseStart_669013 : Nat := 118140960795 + 669013 * 2 ^ 59
def prefixEnd_669013 : Nat := 4983230072969 + 3 ^ 40 * 669013 * 2
def baseEnd_669013 : Nat := 343525233106496217260771

theorem tailTrace_669013 : CollatzResearch.WordTrace tailWord_669013 prefixEnd_669013 343525233106496217260771 := by
  unfold tailWord_669013
  simp only [CollatzResearch.WordTrace]
  refine ⟨24400908725287634168939693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16267272483525089445959795 24400908725287634168939693)
  ·
    refine ⟨9150340771982862813352385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24400908725287634168939693 9150340771982862813352385)
    ·
      refine ⟨6862755578987147110014289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9150340771982862813352385 6862755578987147110014289)
      ·
        refine ⟨5147066684240360332510717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6862755578987147110014289 5147066684240360332510717)
        ·
          refine ⟨1930150006590135124691519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5147066684240360332510717 1930150006590135124691519)
          ·
            refine ⟨2895225009885202687037279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1930150006590135124691519 2895225009885202687037279)
            ·
              refine ⟨4342837514827804030555919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2895225009885202687037279 4342837514827804030555919)
              ·
                refine ⟨6514256272241706045833879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4342837514827804030555919 6514256272241706045833879)
                ·
                  refine ⟨9771384408362559068750819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6514256272241706045833879 9771384408362559068750819)
                  ·
                    refine ⟨14657076612543838603126229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9771384408362559068750819 14657076612543838603126229)
                    ·
                      refine ⟨343525233106496217260771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 14657076612543838603126229 343525233106496217260771)
                      ·
                        rfl

theorem cell23_669013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_669013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669013 prefixEnd_669013 := by exact prefixLift 669013
  have htrace : WordTrace (prefixWord ++ tailWord_669013) baseStart_669013 baseEnd_669013 := by
    simpa [prefixWord, tailWord_669013, baseEnd_669013] using wordTrace_append hprefix tailTrace_669013
  have hstable : (prefixWord ++ tailWord_669013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669013).length < 2 ^ (prefixWord ++ tailWord_669013).sum := by decide
  have hdescent : baseEnd_669013 < baseStart_669013 := by decide
  rcases family_descends (prefixWord ++ tailWord_669013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669023 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 4]
def baseStart_669023 : Nat := 118140960795 + 669023 * 2 ^ 59
def prefixEnd_669023 : Nat := 4983230072969 + 3 ^ 40 * 669023 * 2
def baseEnd_669023 : Nat := 343530367913041178135725

theorem tailTrace_669023 : CollatzResearch.WordTrace tailWord_669023 prefixEnd_669023 343530367913041178135725 := by
  unfold tailWord_669023
  simp only [CollatzResearch.WordTrace]
  refine ⟨24401273455251405876803723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16267515636834270584535815 24401273455251405876803723)
  ·
    refine ⟨36601910182877108815205585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24401273455251405876803723 36601910182877108815205585)
    ·
      refine ⟨27451432637157831611404189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36601910182877108815205585 27451432637157831611404189)
      ·
        refine ⟨10294287238934186854276571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27451432637157831611404189 10294287238934186854276571)
        ·
          refine ⟨15441430858401280281414857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10294287238934186854276571 15441430858401280281414857)
          ·
            refine ⟨11581073143800960211061143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15441430858401280281414857 11581073143800960211061143)
            ·
              refine ⟨17371609715701440316591715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11581073143800960211061143 17371609715701440316591715)
              ·
                refine ⟨26057414573552160474887573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17371609715701440316591715 26057414573552160474887573)
                ·
                  refine ⟨1221441308135257522260355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26057414573552160474887573 1221441308135257522260355)
                  ·
                    refine ⟨1832161962202886283390533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1221441308135257522260355 1832161962202886283390533)
                    ·
                      refine ⟨343530367913041178135725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1832161962202886283390533 343530367913041178135725)
                      ·
                        rfl

theorem cell23_669023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_669023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669023 prefixEnd_669023 := by exact prefixLift 669023
  have htrace : WordTrace (prefixWord ++ tailWord_669023) baseStart_669023 baseEnd_669023 := by
    simpa [prefixWord, tailWord_669023, baseEnd_669023] using wordTrace_append hprefix tailTrace_669023
  have hstable : (prefixWord ++ tailWord_669023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669023).length < 2 ^ (prefixWord ++ tailWord_669023).sum := by decide
  have hdescent : baseEnd_669023 < baseStart_669023 := by decide
  rcases family_descends (prefixWord ++ tailWord_669023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669040 : List Nat := [2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 4]
def baseStart_669040 : Nat := 118140960795 + 669040 * 2 ^ 59
def prefixEnd_669040 : Nat := 4983230072969 + 3 ^ 40 * 669040 * 2
def baseEnd_669040 : Nat := 343539097084167611623147

theorem tailTrace_669040 : CollatzResearch.WordTrace tailWord_669040 prefixEnd_669040 343539097084167611623147 := by
  unfold tailWord_669040
  simp only [CollatzResearch.WordTrace]
  refine ⟨12200946748094908890086287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16267928997459878520115049 12200946748094908890086287)
  ·
    refine ⟨18301420122142363335129431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12200946748094908890086287 18301420122142363335129431)
    ·
      refine ⟨27452130183213545002694147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18301420122142363335129431 27452130183213545002694147)
      ·
        refine ⟨41178195274820317504041221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27452130183213545002694147 41178195274820317504041221)
        ·
          refine ⟨7720911614028809532007729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41178195274820317504041221 7720911614028809532007729)
          ·
            refine ⟨5790683710521607149005797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7720911614028809532007729 5790683710521607149005797)
            ·
              refine ⟨1085753195722801340438587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5790683710521607149005797 1085753195722801340438587)
              ·
                refine ⟨1628629793584202010657881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1085753195722801340438587 1628629793584202010657881)
                ·
                  refine ⟨1221472345188151507993411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1628629793584202010657881 1221472345188151507993411)
                  ·
                    refine ⟨1832208517782227261990117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1221472345188151507993411 1832208517782227261990117)
                    ·
                      refine ⟨343539097084167611623147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1832208517782227261990117 343539097084167611623147)
                      ·
                        rfl

theorem cell23_669040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 4].length) (baseStart_669040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669040 prefixEnd_669040 := by exact prefixLift 669040
  have htrace : WordTrace (prefixWord ++ tailWord_669040) baseStart_669040 baseEnd_669040 := by
    simpa [prefixWord, tailWord_669040, baseEnd_669040] using wordTrace_append hprefix tailTrace_669040
  have hstable : (prefixWord ++ tailWord_669040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669040).length < 2 ^ (prefixWord ++ tailWord_669040).sum := by decide
  have hdescent : baseEnd_669040 < baseStart_669040 := by decide
  rcases family_descends (prefixWord ++ tailWord_669040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669053 : List Nat := [1, 4, 1, 1, 2, 2, 2, 1, 2, 1, 6]
def baseStart_669053 : Nat := 118140960795 + 669053 * 2 ^ 59
def prefixEnd_669053 : Nat := 4983230072969 + 3 ^ 40 * 669053 * 2
def baseEnd_669053 : Nat := 343545772332676060760587

theorem tailTrace_669053 : CollatzResearch.WordTrace tailWord_669053 prefixEnd_669053 343545772332676060760587 := by
  unfold tailWord_669053
  simp only [CollatzResearch.WordTrace]
  refine ⟨24402367645142721000395813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16268245096761814000263875 24402367645142721000395813)
  ·
    refine ⟨4575443933464260187574215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24402367645142721000395813 4575443933464260187574215)
    ·
      refine ⟨6863165900196390281361323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4575443933464260187574215 6863165900196390281361323)
      ·
        refine ⟨10294748850294585422041985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6863165900196390281361323 10294748850294585422041985)
        ·
          refine ⟨7721061637720939066531489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10294748850294585422041985 7721061637720939066531489)
          ·
            refine ⟨5790796228290704299898617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7721061637720939066531489 5790796228290704299898617)
            ·
              refine ⟨4343097171218028224923963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5790796228290704299898617 4343097171218028224923963)
              ·
                refine ⟨6514645756827042337385945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4343097171218028224923963 6514645756827042337385945)
                ·
                  refine ⟨4885984317620281753039459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6514645756827042337385945 4885984317620281753039459)
                  ·
                    refine ⟨7328976476430422629559189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4885984317620281753039459 7328976476430422629559189)
                    ·
                      refine ⟨343545772332676060760587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7328976476430422629559189 343545772332676060760587)
                      ·
                        rfl

theorem cell23_669053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_669053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669053 prefixEnd_669053 := by exact prefixLift 669053
  have htrace : WordTrace (prefixWord ++ tailWord_669053) baseStart_669053 baseEnd_669053 := by
    simpa [prefixWord, tailWord_669053, baseEnd_669053] using wordTrace_append hprefix tailTrace_669053
  have hstable : (prefixWord ++ tailWord_669053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669053).length < 2 ^ (prefixWord ++ tailWord_669053).sum := by decide
  have hdescent : baseEnd_669053 < baseStart_669053 := by decide
  rcases family_descends (prefixWord ++ tailWord_669053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669067 : List Nat := [1, 1, 1, 1, 4, 3, 3, 4, 1, 4]
def baseStart_669067 : Nat := 118140960795 + 669067 * 2 ^ 59
def prefixEnd_669067 : Nat := 4983230072969 + 3 ^ 40 * 669067 * 2
def baseEnd_669067 : Nat := 114517653687279668661841

theorem tailTrace_669067 : CollatzResearch.WordTrace tailWord_669067 prefixEnd_669067 114517653687279668661841 := by
  unfold tailWord_669067
  simp only [CollatzResearch.WordTrace]
  refine ⟨24402878267092001391405455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16268585511394667594270303 24402878267092001391405455)
  ·
    refine ⟨36604317400638002087108183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24402878267092001391405455 36604317400638002087108183)
    ·
      refine ⟨54906476100957003130662275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36604317400638002087108183 54906476100957003130662275)
      ·
        refine ⟨82359714151435504695993413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54906476100957003130662275 82359714151435504695993413)
        ·
          refine ⟨15442446403394157130498765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82359714151435504695993413 15442446403394157130498765)
          ·
            refine ⟨5790917401272808923937037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15442446403394157130498765 5790917401272808923937037)
            ·
              refine ⟨2171594025477303346476389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5790917401272808923937037 2171594025477303346476389)
              ·
                refine ⟨407173879776994377464323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2171594025477303346476389 407173879776994377464323)
                ·
                  refine ⟨610760819665491566196485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 407173879776994377464323 610760819665491566196485)
                  ·
                    refine ⟨114517653687279668661841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 610760819665491566196485 114517653687279668661841)
                    ·
                      rfl

theorem cell23_669067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 4, 1, 4].length) (baseStart_669067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669067 prefixEnd_669067 := by exact prefixLift 669067
  have htrace : WordTrace (prefixWord ++ tailWord_669067) baseStart_669067 baseEnd_669067 := by
    simpa [prefixWord, tailWord_669067, baseEnd_669067] using wordTrace_append hprefix tailTrace_669067
  have hstable : (prefixWord ++ tailWord_669067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669067).length < 2 ^ (prefixWord ++ tailWord_669067).sum := by decide
  have hdescent : baseEnd_669067 < baseStart_669067 := by decide
  rcases family_descends (prefixWord ++ tailWord_669067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669084 : List Nat := [2, 2, 3, 4, 1, 1, 1, 2, 3, 4]
def baseStart_669084 : Nat := 118140960795 + 669084 * 2 ^ 59
def prefixEnd_669084 : Nat := 4983230072969 + 3 ^ 40 * 669084 * 2
def baseEnd_669084 : Nat := 114520563410988479824315

theorem tailTrace_669084 : CollatzResearch.WordTrace tailWord_669084 prefixEnd_669084 114520563410988479824315 := by
  unfold tailWord_669084
  simp only [CollatzResearch.WordTrace]
  refine ⟨12201749154015206647387153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16268998872020275529849537 12201749154015206647387153)
  ·
    refine ⟨9151311865511404985540365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12201749154015206647387153 9151311865511404985540365)
    ·
      refine ⟨3431741949566776869577637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9151311865511404985540365 3431741949566776869577637)
      ·
        refine ⟨643451615543770663045807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3431741949566776869577637 643451615543770663045807)
        ·
          refine ⟨965177423315655994568711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 643451615543770663045807 965177423315655994568711)
          ·
            refine ⟨1447766134973483991853067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 965177423315655994568711 1447766134973483991853067)
            ·
              refine ⟨2171649202460225987779601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1447766134973483991853067 2171649202460225987779601)
              ·
                refine ⟨1628736901845169490834701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2171649202460225987779601 1628736901845169490834701)
                ·
                  refine ⟨610776338191938559063013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1628736901845169490834701 610776338191938559063013)
                  ·
                    refine ⟨114520563410988479824315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 610776338191938559063013 114520563410988479824315)
                    ·
                      rfl

theorem cell23_669084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_669084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669084 prefixEnd_669084 := by exact prefixLift 669084
  have htrace : WordTrace (prefixWord ++ tailWord_669084) baseStart_669084 baseEnd_669084 := by
    simpa [prefixWord, tailWord_669084, baseEnd_669084] using wordTrace_append hprefix tailTrace_669084
  have hstable : (prefixWord ++ tailWord_669084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669084).length < 2 ^ (prefixWord ++ tailWord_669084).sum := by decide
  have hdescent : baseEnd_669084 < baseStart_669084 := by decide
  rcases family_descends (prefixWord ++ tailWord_669084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669101 : List Nat := [1, 5, 2, 2, 1, 2, 2, 3, 1, 4]
def baseStart_669101 : Nat := 118140960795 + 669101 * 2 ^ 59
def prefixEnd_669101 : Nat := 4983230072969 + 3 ^ 40 * 669101 * 2
def baseEnd_669101 : Nat := 114523473134697290986789

theorem tailTrace_669101 : CollatzResearch.WordTrace tailWord_669101 prefixEnd_669101 114523473134697290986789 := by
  unfold tailWord_669101
  simp only [CollatzResearch.WordTrace]
  refine ⟨24404118348968825198143157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16269412232645883465428771 24404118348968825198143157)
  ·
    refine ⟨2287886095215827362325921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24404118348968825198143157 2287886095215827362325921)
    ·
      refine ⟨1715914571411870521744441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2287886095215827362325921 1715914571411870521744441)
      ·
        refine ⟨1286935928558902891308331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1715914571411870521744441 1286935928558902891308331)
        ·
          refine ⟨1930403892838354336962497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1286935928558902891308331 1930403892838354336962497)
          ·
            refine ⟨1447802919628765752721873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1930403892838354336962497 1447802919628765752721873)
            ·
              refine ⟨1085852189721574314541405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1447802919628765752721873 1085852189721574314541405)
              ·
                refine ⟨407194571145590367953027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1085852189721574314541405 407194571145590367953027)
                ·
                  refine ⟨610791856718385551929541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 407194571145590367953027 610791856718385551929541)
                  ·
                    refine ⟨114523473134697290986789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 610791856718385551929541 114523473134697290986789)
                    ·
                      rfl

theorem cell23_669101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_669101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669101 prefixEnd_669101 := by exact prefixLift 669101
  have htrace : WordTrace (prefixWord ++ tailWord_669101) baseStart_669101 baseEnd_669101 := by
    simpa [prefixWord, tailWord_669101, baseEnd_669101] using wordTrace_append hprefix tailTrace_669101
  have hstable : (prefixWord ++ tailWord_669101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669101).length < 2 ^ (prefixWord ++ tailWord_669101).sum := by decide
  have hdescent : baseEnd_669101 < baseStart_669101 := by decide
  rcases family_descends (prefixWord ++ tailWord_669101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669117 : List Nat := [1, 4, 1, 2, 2, 1, 2, 1, 4, 3, 2]
def baseStart_669117 : Nat := 118140960795 + 669117 * 2 ^ 59
def prefixEnd_669117 : Nat := 4983230072969 + 3 ^ 40 * 669117 * 2
def baseEnd_669117 : Nat := 343578635094563810360293

theorem tailTrace_669117 : CollatzResearch.WordTrace tailWord_669117 prefixEnd_669117 343578635094563810360293 := by
  unfold tailWord_669117
  simp only [CollatzResearch.WordTrace]
  refine ⟨24404701916910859930725605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16269801277940573287150403 24404701916910859930725605)
  ·
    refine ⟨4575881609420786237011051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24404701916910859930725605 4575881609420786237011051)
    ·
      refine ⟨6863822414131179355516577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4575881609420786237011051 6863822414131179355516577)
      ·
        refine ⟨5147866810598384516637433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6863822414131179355516577 5147866810598384516637433)
        ·
          refine ⟨3860900107948788387478075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5147866810598384516637433 3860900107948788387478075)
          ·
            refine ⟨5791350161923182581217113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3860900107948788387478075 5791350161923182581217113)
            ·
              refine ⟨4343512621442386935912835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5791350161923182581217113 4343512621442386935912835)
              ·
                refine ⟨6515268932163580403869253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4343512621442386935912835 6515268932163580403869253)
                ·
                  refine ⟨1221612924780671325725485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6515268932163580403869253 1221612924780671325725485)
                  ·
                    refine ⟨458104846792751747147057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1221612924780671325725485 458104846792751747147057)
                    ·
                      refine ⟨343578635094563810360293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 458104846792751747147057 343578635094563810360293)
                      ·
                        rfl

theorem cell23_669117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_669117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669117 prefixEnd_669117 := by exact prefixLift 669117
  have htrace : WordTrace (prefixWord ++ tailWord_669117) baseStart_669117 baseEnd_669117 := by
    simpa [prefixWord, tailWord_669117, baseEnd_669117] using wordTrace_append hprefix tailTrace_669117
  have hstable : (prefixWord ++ tailWord_669117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669117).length < 2 ^ (prefixWord ++ tailWord_669117).sum := by decide
  have hdescent : baseEnd_669117 < baseStart_669117 := by decide
  rcases family_descends (prefixWord ++ tailWord_669117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669123 : List Nat := [1, 1, 1, 3, 1, 1, 4, 2, 3, 6]
def baseStart_669123 : Nat := 118140960795 + 669123 * 2 ^ 59
def prefixEnd_669123 : Nat := 4983230072969 + 3 ^ 40 * 669123 * 2
def baseEnd_669123 : Nat := 114527238659496928961755

theorem tailTrace_669123 : CollatzResearch.WordTrace tailWord_669123 prefixEnd_669123 114527238659496928961755 := by
  unfold tailWord_669123
  simp only [CollatzResearch.WordTrace]
  refine ⟨24404920754889122955444023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16269947169926081970296015 24404920754889122955444023)
  ·
    refine ⟨36607381132333684433166035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24404920754889122955444023 36607381132333684433166035)
    ·
      refine ⟨54911071698500526649749053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36607381132333684433166035 54911071698500526649749053)
      ·
        refine ⟨20591651886937697493655895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54911071698500526649749053 20591651886937697493655895)
        ·
          refine ⟨30887477830406546240483843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20591651886937697493655895 30887477830406546240483843)
          ·
            refine ⟨46331216745609819360725765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30887477830406546240483843 46331216745609819360725765)
            ·
              refine ⟨8687103139801841130136081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46331216745609819360725765 8687103139801841130136081)
              ·
                refine ⟨6515327354851380847602061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8687103139801841130136081 6515327354851380847602061)
                ·
                  refine ⟨2443247758069267817850773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6515327354851380847602061 2443247758069267817850773)
                  ·
                    refine ⟨114527238659496928961755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2443247758069267817850773 114527238659496928961755)
                    ·
                      rfl

theorem cell23_669123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 6].length) (baseStart_669123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669123 prefixEnd_669123 := by exact prefixLift 669123
  have htrace : WordTrace (prefixWord ++ tailWord_669123) baseStart_669123 baseEnd_669123 := by
    simpa [prefixWord, tailWord_669123, baseEnd_669123] using wordTrace_append hprefix tailTrace_669123
  have hstable : (prefixWord ++ tailWord_669123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669123).length < 2 ^ (prefixWord ++ tailWord_669123).sum := by decide
  have hdescent : baseEnd_669123 < baseStart_669123 := by decide
  rcases family_descends (prefixWord ++ tailWord_669123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669124 : List Nat := [2, 3, 3, 2, 1, 1, 1, 3, 3, 1, 3]
def baseStart_669124 : Nat := 118140960795 + 669124 * 2 ^ 59
def prefixEnd_669124 : Nat := 4983230072969 + 3 ^ 40 * 669124 * 2
def baseEnd_669124 : Nat := 343582229459145282972761

theorem tailTrace_669124 : CollatzResearch.WordTrace tailWord_669124 prefixEnd_669124 343582229459145282972761 := by
  unfold tailWord_669124
  simp only [CollatzResearch.WordTrace]
  refine ⟨12202478613942750063115213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16269971485257000084153617 12202478613942750063115213)
  ·
    refine ⟨4575929480228531273668205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12202478613942750063115213 4575929480228531273668205)
    ·
      refine ⟨1715973555085699227625577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4575929480228531273668205 1715973555085699227625577)
      ·
        refine ⟨1286980166314274420719183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1715973555085699227625577 1286980166314274420719183)
        ·
          refine ⟨1930470249471411631078775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1286980166314274420719183 1930470249471411631078775)
          ·
            refine ⟨2895705374207117446618163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1930470249471411631078775 2895705374207117446618163)
            ·
              refine ⟨4343558061310676169927245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2895705374207117446618163 4343558061310676169927245)
              ·
                refine ⟨1628834272991503563722717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4343558061310676169927245 1628834272991503563722717)
                ·
                  refine ⟨610812852371813836396019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1628834272991503563722717 610812852371813836396019)
                  ·
                    refine ⟨916219278557720754594029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 610812852371813836396019 916219278557720754594029)
                    ·
                      refine ⟨343582229459145282972761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 916219278557720754594029 343582229459145282972761)
                      ·
                        rfl

theorem cell23_669124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_669124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669124 prefixEnd_669124 := by exact prefixLift 669124
  have htrace : WordTrace (prefixWord ++ tailWord_669124) baseStart_669124 baseEnd_669124 := by
    simpa [prefixWord, tailWord_669124, baseEnd_669124] using wordTrace_append hprefix tailTrace_669124
  have hstable : (prefixWord ++ tailWord_669124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669124).length < 2 ^ (prefixWord ++ tailWord_669124).sum := by decide
  have hdescent : baseEnd_669124 < baseStart_669124 := by decide
  rcases family_descends (prefixWord ++ tailWord_669124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669157 : List Nat := [1, 3, 1, 5, 1, 1, 1, 2, 4, 4]
def baseStart_669157 : Nat := 118140960795 + 669157 * 2 ^ 59
def prefixEnd_669157 : Nat := 4983230072969 + 3 ^ 40 * 669157 * 2
def baseEnd_669157 : Nat := 114533058106914551286703

theorem tailTrace_669157 : CollatzResearch.WordTrace tailWord_669157 prefixEnd_669157 114533058106914551286703 := by
  unfold tailWord_669157
  simp only [CollatzResearch.WordTrace]
  refine ⟨24406160836765946762181725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16270773891177297841454483 24406160836765946762181725)
  ·
    refine ⟨9152310313787230035818147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24406160836765946762181725 9152310313787230035818147)
    ·
      refine ⟨13728465470680845053727221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9152310313787230035818147 13728465470680845053727221)
      ·
        refine ⟨1287043637876329223786927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13728465470680845053727221 1287043637876329223786927)
        ·
          refine ⟨1930565456814493835680391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1287043637876329223786927 1930565456814493835680391)
          ·
            refine ⟨2895848185221740753520587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1930565456814493835680391 2895848185221740753520587)
            ·
              refine ⟨4343772277832611130280881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2895848185221740753520587 4343772277832611130280881)
              ·
                refine ⟨3257829208374458347710661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4343772277832611130280881 3257829208374458347710661)
                ·
                  refine ⟨610842976570210940195749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3257829208374458347710661 610842976570210940195749)
                  ·
                    refine ⟨114533058106914551286703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 610842976570210940195749 114533058106914551286703)
                    ·
                      rfl

theorem cell23_669157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 4, 4].length) (baseStart_669157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669157 prefixEnd_669157 := by exact prefixLift 669157
  have htrace : WordTrace (prefixWord ++ tailWord_669157) baseStart_669157 baseEnd_669157 := by
    simpa [prefixWord, tailWord_669157, baseEnd_669157] using wordTrace_append hprefix tailTrace_669157
  have hstable : (prefixWord ++ tailWord_669157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669157).length < 2 ^ (prefixWord ++ tailWord_669157).sum := by decide
  have hdescent : baseEnd_669157 < baseStart_669157 := by decide
  rcases family_descends (prefixWord ++ tailWord_669157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669160 : List Nat := [2, 1, 4, 1, 1, 2, 2, 1, 3, 2, 4]
def baseStart_669160 : Nat := 118140960795 + 669160 * 2 ^ 59
def prefixEnd_669160 : Nat := 4983230072969 + 3 ^ 40 * 669160 * 2
def baseEnd_669160 : Nat := 343600714762707142122595

theorem tailTrace_669160 : CollatzResearch.WordTrace tailWord_669160 prefixEnd_669160 343600714762707142122595 := by
  unfold tailWord_669160
  simp only [CollatzResearch.WordTrace]
  refine ⟨12203135127877539137270467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16270846837170052183027289 12203135127877539137270467)
  ·
    refine ⟨18304702691816308705905701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12203135127877539137270467 18304702691816308705905701)
    ·
      refine ⟨3432131754715557882357319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18304702691816308705905701 3432131754715557882357319)
      ·
        refine ⟨5148197632073336823535979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3432131754715557882357319 5148197632073336823535979)
        ·
          refine ⟨7722296448110005235303969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5148197632073336823535979 7722296448110005235303969)
          ·
            refine ⟨5791722336082503926477977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7722296448110005235303969 5791722336082503926477977)
            ·
              refine ⟨4343791752061877944858483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5791722336082503926477977 4343791752061877944858483)
              ·
                refine ⟨6515687628092816917287725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4343791752061877944858483 6515687628092816917287725)
                ·
                  refine ⟨2443382860534806343982897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6515687628092816917287725 2443382860534806343982897)
                  ·
                    refine ⟨1832537145401104757987173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2443382860534806343982897 1832537145401104757987173)
                    ·
                      refine ⟨343600714762707142122595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1832537145401104757987173 343600714762707142122595)
                      ·
                        rfl

theorem cell23_669160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_669160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669160 prefixEnd_669160 := by exact prefixLift 669160
  have htrace : WordTrace (prefixWord ++ tailWord_669160) baseStart_669160 baseEnd_669160 := by
    simpa [prefixWord, tailWord_669160, baseEnd_669160] using wordTrace_append hprefix tailTrace_669160
  have hstable : (prefixWord ++ tailWord_669160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669160).length < 2 ^ (prefixWord ++ tailWord_669160).sum := by decide
  have hdescent : baseEnd_669160 < baseStart_669160 := by decide
  rcases family_descends (prefixWord ++ tailWord_669160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669167 : List Nat := [1, 1, 2, 1, 4, 1, 4, 3, 1, 2, 3]
def baseStart_669167 : Nat := 118140960795 + 669167 * 2 ^ 59
def prefixEnd_669167 : Nat := 4983230072969 + 3 ^ 40 * 669167 * 2
def baseEnd_669167 : Nat := 343604309127288614735063

theorem tailTrace_669167 : CollatzResearch.WordTrace tailWord_669167 prefixEnd_669167 343604309127288614735063 := by
  unfold tailWord_669167
  simp only [CollatzResearch.WordTrace]
  refine ⟨24406525566729718470045755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16271017044486478980030503 24406525566729718470045755)
  ·
    refine ⟨36609788350094577705068633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24406525566729718470045755 36609788350094577705068633)
    ·
      refine ⟨27457341262570933278801475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36609788350094577705068633 27457341262570933278801475)
      ·
        refine ⟨41186011893856399918202213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27457341262570933278801475 41186011893856399918202213)
        ·
          refine ⟨7722377230098074984662915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41186011893856399918202213 7722377230098074984662915)
          ·
            refine ⟨11583565845147112476994373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7722377230098074984662915 11583565845147112476994373)
            ·
              refine ⟨2171918595965083589436445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11583565845147112476994373 2171918595965083589436445)
              ·
                refine ⟨814469473486906346038667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2171918595965083589436445 814469473486906346038667)
                ·
                  refine ⟨1221704210230359519058001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 814469473486906346038667 1221704210230359519058001)
                  ·
                    refine ⟨916278157672769639293501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1221704210230359519058001 916278157672769639293501)
                    ·
                      refine ⟨343604309127288614735063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 916278157672769639293501 343604309127288614735063)
                      ·
                        rfl

theorem cell23_669167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 2, 3].length) (baseStart_669167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669167 prefixEnd_669167 := by exact prefixLift 669167
  have htrace : WordTrace (prefixWord ++ tailWord_669167) baseStart_669167 baseEnd_669167 := by
    simpa [prefixWord, tailWord_669167, baseEnd_669167] using wordTrace_append hprefix tailTrace_669167
  have hstable : (prefixWord ++ tailWord_669167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669167).length < 2 ^ (prefixWord ++ tailWord_669167).sum := by decide
  have hdescent : baseEnd_669167 < baseStart_669167 := by decide
  rcases family_descends (prefixWord ++ tailWord_669167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669170 : List Nat := [3, 2, 1, 4, 1, 1, 11]
def baseStart_669170 : Nat := 118140960795 + 669170 * 2 ^ 59
def prefixEnd_669170 : Nat := 4983230072969 + 3 ^ 40 * 669170 * 2
def baseEnd_669170 : Nat := 4242047525546322259229

theorem tailTrace_669170 : CollatzResearch.WordTrace tailWord_669170 prefixEnd_669170 4242047525546322259229 := by
  unfold tailWord_669170
  simp only [CollatzResearch.WordTrace]
  refine ⟨6101658746429712495601241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16271089990479233321603309 6101658746429712495601241)
  ·
    refine ⟨4576244059822284371700931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6101658746429712495601241 4576244059822284371700931)
    ·
      refine ⟨6864366089733426557551397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4576244059822284371700931 6864366089733426557551397)
      ·
        refine ⟨1287068641825017479540887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6864366089733426557551397 1287068641825017479540887)
        ·
          refine ⟨1930602962737526219311331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1287068641825017479540887 1930602962737526219311331)
          ·
            refine ⟨2895904444106289328966997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1930602962737526219311331 2895904444106289328966997)
            ·
              refine ⟨4242047525546322259229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 2895904444106289328966997 4242047525546322259229)
              ·
                rfl

theorem cell23_669170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 11].length) (baseStart_669170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669170 prefixEnd_669170 := by exact prefixLift 669170
  have htrace : WordTrace (prefixWord ++ tailWord_669170) baseStart_669170 baseEnd_669170 := by
    simpa [prefixWord, tailWord_669170, baseEnd_669170] using wordTrace_append hprefix tailTrace_669170
  have hstable : (prefixWord ++ tailWord_669170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669170).length < 2 ^ (prefixWord ++ tailWord_669170).sum := by decide
  have hdescent : baseEnd_669170 < baseStart_669170 := by decide
  rcases family_descends (prefixWord ++ tailWord_669170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669181 : List Nat := [1, 4, 1, 1, 1, 6, 1, 1, 3, 2, 2]
def baseStart_669181 : Nat := 118140960795 + 669181 * 2 ^ 59
def prefixEnd_669181 : Nat := 4983230072969 + 3 ^ 40 * 669181 * 2
def baseEnd_669181 : Nat := 343611497856451559959999

theorem tailTrace_669181 : CollatzResearch.WordTrace tailWord_669181 prefixEnd_669181 343611497856451559959999 := by
  unfold tailWord_669181
  simp only [CollatzResearch.WordTrace]
  refine ⟨24407036188678998861055397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16271357459119332574036931 24407036188678998861055397)
  ·
    refine ⟨4576319285377312286447887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24407036188678998861055397 4576319285377312286447887)
    ·
      refine ⟨6864478928065968429671831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4576319285377312286447887 6864478928065968429671831)
      ·
        refine ⟨10296718392098952644507747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6864478928065968429671831 10296718392098952644507747)
        ·
          refine ⟨15445077588148428966761621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10296718392098952644507747 15445077588148428966761621)
          ·
            refine ⟨723988011944457607816951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15445077588148428966761621 723988011944457607816951)
            ·
              refine ⟨1085982017916686411725427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 723988011944457607816951 1085982017916686411725427)
              ·
                refine ⟨1628973026875029617588141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1085982017916686411725427 1628973026875029617588141)
                ·
                  refine ⟨610864885078136106595553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1628973026875029617588141 610864885078136106595553)
                  ·
                    refine ⟨458148663808602079946665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 610864885078136106595553 458148663808602079946665)
                    ·
                      refine ⟨343611497856451559959999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 458148663808602079946665 343611497856451559959999)
                      ·
                        rfl

theorem cell23_669181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 3, 2, 2].length) (baseStart_669181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669181 prefixEnd_669181 := by exact prefixLift 669181
  have htrace : WordTrace (prefixWord ++ tailWord_669181) baseStart_669181 baseEnd_669181 := by
    simpa [prefixWord, tailWord_669181, baseEnd_669181] using wordTrace_append hprefix tailTrace_669181
  have hstable : (prefixWord ++ tailWord_669181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669181).length < 2 ^ (prefixWord ++ tailWord_669181).sum := by decide
  have hdescent : baseEnd_669181 < baseStart_669181 := by decide
  rcases family_descends (prefixWord ++ tailWord_669181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669191 : List Nat := [1, 1, 4, 3, 2, 3, 2, 1, 2, 4]
def baseStart_669191 : Nat := 118140960795 + 669191 * 2 ^ 59
def prefixEnd_669191 : Nat := 4983230072969 + 3 ^ 40 * 669191 * 2
def baseEnd_669191 : Nat := 114538877554332173611651

theorem tailTrace_669191 : CollatzResearch.WordTrace tailWord_669191 prefixEnd_669191 114538877554332173611651 := by
  unfold tailWord_669191
  simp only [CollatzResearch.WordTrace]
  refine ⟨24407400918642770568919427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16271600612428513712612951 24407400918642770568919427)
  ·
    refine ⟨36611101377964155853379141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24407400918642770568919427 36611101377964155853379141)
    ·
      refine ⟨6864581508368279222508589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36611101377964155853379141 6864581508368279222508589)
      ·
        refine ⟨2574218065638104708440721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6864581508368279222508589 2574218065638104708440721)
        ·
          refine ⟨1930663549228578531330541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2574218065638104708440721 1930663549228578531330541)
          ·
            refine ⟨723998830960716949248953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1930663549228578531330541 723998830960716949248953)
            ·
              refine ⟨542999123220537711936715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 723998830960716949248953 542999123220537711936715)
              ·
                refine ⟨814498684830806567905073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 542999123220537711936715 814498684830806567905073)
                ·
                  refine ⟨610874013623104925928805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 814498684830806567905073 610874013623104925928805)
                  ·
                    refine ⟨114538877554332173611651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 610874013623104925928805 114538877554332173611651)
                    ·
                      rfl

theorem cell23_669191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 2, 4].length) (baseStart_669191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669191 prefixEnd_669191 := by exact prefixLift 669191
  have htrace : WordTrace (prefixWord ++ tailWord_669191) baseStart_669191 baseEnd_669191 := by
    simpa [prefixWord, tailWord_669191, baseEnd_669191] using wordTrace_append hprefix tailTrace_669191
  have hstable : (prefixWord ++ tailWord_669191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669191).length < 2 ^ (prefixWord ++ tailWord_669191).sum := by decide
  have hdescent : baseEnd_669191 < baseStart_669191 := by decide
  rcases family_descends (prefixWord ++ tailWord_669191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669260 : List Nat := [2, 2, 1, 3, 1, 3, 1, 1, 9]
def baseStart_669260 : Nat := 118140960795 + 669260 * 2 ^ 59
def prefixEnd_669260 : Nat := 4983230072969 + 3 ^ 40 * 669260 * 2
def baseEnd_669260 : Nat := 38183562536461861208015

theorem tailTrace_669260 : CollatzResearch.WordTrace tailWord_669260 prefixEnd_669260 38183562536461861208015 := by
  unfold tailWord_669260
  simp only [CollatzResearch.WordTrace]
  refine ⟨12204958777696397676590617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16273278370261863568787489 12204958777696397676590617)
  ·
    refine ⟨9153719083272298257442963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12204958777696397676590617 9153719083272298257442963)
    ·
      refine ⟨13730578624908447386164445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9153719083272298257442963 13730578624908447386164445)
      ·
        refine ⟨5148966984340667769811667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13730578624908447386164445 5148966984340667769811667)
        ·
          refine ⟨7723450476511001654717501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5148966984340667769811667 7723450476511001654717501)
          ·
            refine ⟨2896293928691625620519063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7723450476511001654717501 2896293928691625620519063)
            ·
              refine ⟨4344440893037438430778595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2896293928691625620519063 4344440893037438430778595)
              ·
                refine ⟨6516661339556157646167893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4344440893037438430778595 6516661339556157646167893)
                ·
                  refine ⟨38183562536461861208015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6516661339556157646167893 38183562536461861208015)
                  ·
                    rfl

theorem cell23_669260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 9].length) (baseStart_669260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669260 prefixEnd_669260 := by exact prefixLift 669260
  have htrace : WordTrace (prefixWord ++ tailWord_669260) baseStart_669260 baseEnd_669260 := by
    simpa [prefixWord, tailWord_669260, baseEnd_669260] using wordTrace_append hprefix tailTrace_669260
  have hstable : (prefixWord ++ tailWord_669260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669260).length < 2 ^ (prefixWord ++ tailWord_669260).sum := by decide
  have hdescent : baseEnd_669260 < baseStart_669260 := by decide
  rcases family_descends (prefixWord ++ tailWord_669260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669287 : List Nat := [1, 1, 5, 1, 1, 1, 3, 2, 2, 3, 3]
def baseStart_669287 : Nat := 118140960795 + 669287 * 2 ^ 59
def prefixEnd_669287 : Nat := 4983230072969 + 3 ^ 40 * 669287 * 2
def baseEnd_669287 : Nat := 343665926805828145234511

theorem tailTrace_669287 : CollatzResearch.WordTrace tailWord_669287 prefixEnd_669287 343665926805828145234511 := by
  unfold tailWord_669287
  simp only [CollatzResearch.WordTrace]
  refine ⟨24410902326294978964414115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16273934884196652642942743 24410902326294978964414115)
  ·
    refine ⟨36616353489442468446621173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24410902326294978964414115 36616353489442468446621173)
    ·
      refine ⟨3432783139635231416870735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36616353489442468446621173 3432783139635231416870735)
      ·
        refine ⟨5149174709452847125306103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3432783139635231416870735 5149174709452847125306103)
        ·
          refine ⟨7723762064179270687959155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5149174709452847125306103 7723762064179270687959155)
          ·
            refine ⟨11585643096268906031938733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7723762064179270687959155 11585643096268906031938733)
            ·
              refine ⟨4344616161100839761977025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11585643096268906031938733 4344616161100839761977025)
              ·
                refine ⟨3258462120825629821482769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4344616161100839761977025 3258462120825629821482769)
                ·
                  refine ⟨2443846590619222366112077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3258462120825629821482769 2443846590619222366112077)
                  ·
                    refine ⟨916442471482208387292029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2443846590619222366112077 916442471482208387292029)
                    ·
                      refine ⟨343665926805828145234511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 916442471482208387292029 343665926805828145234511)
                      ·
                        rfl

theorem cell23_669287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_669287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669287 prefixEnd_669287 := by exact prefixLift 669287
  have htrace : WordTrace (prefixWord ++ tailWord_669287) baseStart_669287 baseEnd_669287 := by
    simpa [prefixWord, tailWord_669287, baseEnd_669287] using wordTrace_append hprefix tailTrace_669287
  have hstable : (prefixWord ++ tailWord_669287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669287).length < 2 ^ (prefixWord ++ tailWord_669287).sum := by decide
  have hdescent : baseEnd_669287 < baseStart_669287 := by decide
  rcases family_descends (prefixWord ++ tailWord_669287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669288 : List Nat := [2, 1, 4, 3, 1, 1, 3, 2, 2, 2, 2]
def baseStart_669288 : Nat := 118140960795 + 669288 * 2 ^ 59
def prefixEnd_669288 : Nat := 4983230072969 + 3 ^ 40 * 669288 * 2
def baseEnd_669288 : Nat := 343666440286482641322007

theorem tailTrace_669288 : CollatzResearch.WordTrace tailWord_669288 prefixEnd_669288 343666440286482641322007 := by
  unfold tailWord_669288
  simp only [CollatzResearch.WordTrace]
  refine ⟨12205469399645678067600259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16273959199527570756800345 12205469399645678067600259)
  ·
    refine ⟨18308204099468517101400389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12205469399645678067600259 18308204099468517101400389)
    ·
      refine ⟨3432788268650346956512573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18308204099468517101400389 3432788268650346956512573)
      ·
        refine ⟨1287295600743880108692215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3432788268650346956512573 1287295600743880108692215)
        ·
          refine ⟨1930943401115820163038323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1287295600743880108692215 1930943401115820163038323)
          ·
            refine ⟨2896415101673730244557485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1930943401115820163038323 2896415101673730244557485)
            ·
              refine ⟨1086155663127648841709057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2896415101673730244557485 1086155663127648841709057)
              ·
                refine ⟨814616747345736631281793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1086155663127648841709057 814616747345736631281793)
                ·
                  refine ⟨610962560509302473461345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 814616747345736631281793 610962560509302473461345)
                  ·
                    refine ⟨458221920381976855096009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 610962560509302473461345 458221920381976855096009)
                    ·
                      refine ⟨343666440286482641322007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 458221920381976855096009 343666440286482641322007)
                      ·
                        rfl

theorem cell23_669288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_669288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669288 prefixEnd_669288 := by exact prefixLift 669288
  have htrace : WordTrace (prefixWord ++ tailWord_669288) baseStart_669288 baseEnd_669288 := by
    simpa [prefixWord, tailWord_669288, baseEnd_669288] using wordTrace_append hprefix tailTrace_669288
  have hstable : (prefixWord ++ tailWord_669288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669288).length < 2 ^ (prefixWord ++ tailWord_669288).sum := by decide
  have hdescent : baseEnd_669288 < baseStart_669288 := by decide
  rcases family_descends (prefixWord ++ tailWord_669288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669294 : List Nat := [4, 1, 2, 2, 3, 1, 2, 1, 7]
def baseStart_669294 : Nat := 118140960795 + 669294 * 2 ^ 59
def prefixEnd_669294 : Nat := 4983230072969 + 3 ^ 40 * 669294 * 2
def baseEnd_669294 : Nat := 38185502352267735316331

theorem tailTrace_669294 : CollatzResearch.WordTrace tailWord_669294 prefixEnd_669294 38185502352267735316331 := by
  unfold tailWord_669294
  simp only [CollatzResearch.WordTrace]
  refine ⟨3051394704658702394989867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16274105091513079439945957 3051394704658702394989867)
  ·
    refine ⟨4577092056988053592484801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3051394704658702394989867 4577092056988053592484801)
    ·
      refine ⟨3432819042741040194363601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4577092056988053592484801 3432819042741040194363601)
      ·
        refine ⟨2574614282055780145772701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3432819042741040194363601 2574614282055780145772701)
        ·
          refine ⟨965480355770917554664763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2574614282055780145772701 965480355770917554664763)
          ·
            refine ⟨1448220533656376331997145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 965480355770917554664763 1448220533656376331997145)
            ·
              refine ⟨1086165400242282248997859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1448220533656376331997145 1086165400242282248997859)
              ·
                refine ⟨1629248100363423373496789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1086165400242282248997859 1629248100363423373496789)
                ·
                  refine ⟨38185502352267735316331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1629248100363423373496789 38185502352267735316331)
                  ·
                    rfl

theorem cell23_669294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 7].length) (baseStart_669294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669294 prefixEnd_669294 := by exact prefixLift 669294
  have htrace : WordTrace (prefixWord ++ tailWord_669294) baseStart_669294 baseEnd_669294 := by
    simpa [prefixWord, tailWord_669294, baseEnd_669294] using wordTrace_append hprefix tailTrace_669294
  have hstable : (prefixWord ++ tailWord_669294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669294).length < 2 ^ (prefixWord ++ tailWord_669294).sum := by decide
  have hdescent : baseEnd_669294 < baseStart_669294 := by decide
  rcases family_descends (prefixWord ++ tailWord_669294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669297 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 1, 7, 2]
def baseStart_669297 : Nat := 118140960795 + 669297 * 2 ^ 59
def prefixEnd_669297 : Nat := 4983230072969 + 3 ^ 40 * 669297 * 2
def baseEnd_669297 : Nat := 343671061612373106109465

theorem tailTrace_669297 : CollatzResearch.WordTrace tailWord_669297 prefixEnd_669297 343671061612373106109465 := by
  unfold tailWord_669297
  simp only [CollatzResearch.WordTrace]
  refine ⟨24411267056258750672278145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16274178037505833781518763 24411267056258750672278145)
  ·
    refine ⟨18308450292194063004208609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24411267056258750672278145 18308450292194063004208609)
    ·
      refine ⟨13731337719145547253156457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18308450292194063004208609 13731337719145547253156457)
      ·
        refine ⟨10298503289359160439867343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13731337719145547253156457 10298503289359160439867343)
        ·
          refine ⟨15447754934038740659801015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10298503289359160439867343 15447754934038740659801015)
          ·
            refine ⟨23171632401058110989701523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15447754934038740659801015 23171632401058110989701523)
            ·
              refine ⟨34757448601587166484552285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23171632401058110989701523 34757448601587166484552285)
              ·
                refine ⟨13034043225595187431707107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34757448601587166484552285 13034043225595187431707107)
                ·
                  refine ⟨19551064838392781147560661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13034043225595187431707107 19551064838392781147560661)
                  ·
                    refine ⟨458228082149830808145953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19551064838392781147560661 458228082149830808145953)
                    ·
                      refine ⟨343671061612373106109465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 458228082149830808145953 343671061612373106109465)
                      ·
                        rfl

theorem cell23_669297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 7, 2].length) (baseStart_669297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669297 prefixEnd_669297 := by exact prefixLift 669297
  have htrace : WordTrace (prefixWord ++ tailWord_669297) baseStart_669297 baseEnd_669297 := by
    simpa [prefixWord, tailWord_669297, baseEnd_669297] using wordTrace_append hprefix tailTrace_669297
  have hstable : (prefixWord ++ tailWord_669297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669297).length < 2 ^ (prefixWord ++ tailWord_669297).sum := by decide
  have hdescent : baseEnd_669297 < baseStart_669297 := by decide
  rcases family_descends (prefixWord ++ tailWord_669297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669344 : List Nat := [2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 4]
def baseStart_669344 : Nat := 118140960795 + 669344 * 2 ^ 59
def prefixEnd_669344 : Nat := 4983230072969 + 3 ^ 40 * 669344 * 2
def baseEnd_669344 : Nat := 343695195203134422221749

theorem tailTrace_669344 : CollatzResearch.WordTrace tailWord_669344 prefixEnd_669344 343695195203134422221749 := by
  unfold tailWord_669344
  simp only [CollatzResearch.WordTrace]
  refine ⟨12206490643544238849619543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16275320858058985132826057 12206490643544238849619543)
  ·
    refine ⟨18309735965316358274429315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12206490643544238849619543 18309735965316358274429315)
    ·
      refine ⟨27464603947974537411643973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18309735965316358274429315 27464603947974537411643973)
      ·
        refine ⟨5149613240245225764683245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27464603947974537411643973 5149613240245225764683245)
        ·
          refine ⟨1931104965091959661756217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5149613240245225764683245 1931104965091959661756217)
          ·
            refine ⟨1448328723818969746317163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1931104965091959661756217 1448328723818969746317163)
            ·
              refine ⟨2172493085728454619475745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1448328723818969746317163 2172493085728454619475745)
              ·
                refine ⟨1629369814296340964606809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2172493085728454619475745 1629369814296340964606809)
                ·
                  refine ⟨1222027360722255723455107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1629369814296340964606809 1222027360722255723455107)
                  ·
                    refine ⟨1833041041083383585182661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1222027360722255723455107 1833041041083383585182661)
                    ·
                      refine ⟨343695195203134422221749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1833041041083383585182661 343695195203134422221749)
                      ·
                        rfl

theorem cell23_669344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_669344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669344 prefixEnd_669344 := by exact prefixLift 669344
  have htrace : WordTrace (prefixWord ++ tailWord_669344) baseStart_669344 baseEnd_669344 := by
    simpa [prefixWord, tailWord_669344, baseEnd_669344] using wordTrace_append hprefix tailTrace_669344
  have hstable : (prefixWord ++ tailWord_669344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669344).length < 2 ^ (prefixWord ++ tailWord_669344).sum := by decide
  have hdescent : baseEnd_669344 < baseStart_669344 := by decide
  rcases family_descends (prefixWord ++ tailWord_669344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669405 : List Nat := [1, 4, 3, 3, 1, 1, 1, 4, 1, 4]
def baseStart_669405 : Nat := 118140960795 + 669405 * 2 ^ 59
def prefixEnd_669405 : Nat := 4983230072969 + 3 ^ 40 * 669405 * 2
def baseEnd_669405 : Nat := 114575505841019561186323

theorem tailTrace_669405 : CollatzResearch.WordTrace tailWord_669405 prefixEnd_669405 114575505841019561186323 := by
  unfold tailWord_669405
  simp only [CollatzResearch.WordTrace]
  refine ⟨24415206139867485117209669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16276804093244990078139779 24415206139867485117209669)
  ·
    refine ⟨4577851151225153459476813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24415206139867485117209669 4577851151225153459476813)
    ·
      refine ⟨1716694181709432547303805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4577851151225153459476813 1716694181709432547303805)
      ·
        refine ⟨643760318141037205238927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1716694181709432547303805 643760318141037205238927)
        ·
          refine ⟨965640477211555807858391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 643760318141037205238927 965640477211555807858391)
          ·
            refine ⟨1448460715817333711787587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 965640477211555807858391 1448460715817333711787587)
            ·
              refine ⟨2172691073726000567681381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1448460715817333711787587 2172691073726000567681381)
              ·
                refine ⟨407379576323625106440259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2172691073726000567681381 407379576323625106440259)
                ·
                  refine ⟨611069364485437659660389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 407379576323625106440259 611069364485437659660389)
                  ·
                    refine ⟨114575505841019561186323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 611069364485437659660389 114575505841019561186323)
                    ·
                      rfl

theorem cell23_669405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_669405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669405 prefixEnd_669405 := by exact prefixLift 669405
  have htrace : WordTrace (prefixWord ++ tailWord_669405) baseStart_669405 baseEnd_669405 := by
    simpa [prefixWord, tailWord_669405, baseEnd_669405] using wordTrace_append hprefix tailTrace_669405
  have hstable : (prefixWord ++ tailWord_669405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669405).length < 2 ^ (prefixWord ++ tailWord_669405).sum := by decide
  have hdescent : baseEnd_669405 < baseStart_669405 := by decide
  rcases family_descends (prefixWord ++ tailWord_669405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669427 : List Nat := [1, 1, 1, 2, 2, 3, 3, 3, 1, 6]
def baseStart_669427 : Nat := 118140960795 + 669427 * 2 ^ 59
def prefixEnd_669427 : Nat := 4983230072969 + 3 ^ 40 * 669427 * 2
def baseEnd_669427 : Nat := 114579271365819199161289

theorem tailTrace_669427 : CollatzResearch.WordTrace tailWord_669427 prefixEnd_669427 114579271365819199161289 := by
  unfold tailWord_669427
  simp only [CollatzResearch.WordTrace]
  refine ⟨24416008545787782874510535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16277339030525188583007023 24416008545787782874510535)
  ·
    refine ⟨36624012818681674311765803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24416008545787782874510535 36624012818681674311765803)
    ·
      refine ⟨54936019228022511467648705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36624012818681674311765803 54936019228022511467648705)
      ·
        refine ⟨41202014421016883600736529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54936019228022511467648705 41202014421016883600736529)
        ·
          refine ⟨30901510815762662700552397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41202014421016883600736529 30901510815762662700552397)
          ·
            refine ⟨11588066555910998512707149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30901510815762662700552397 11588066555910998512707149)
            ·
              refine ⟨4345524958466624442265181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11588066555910998512707149 4345524958466624442265181)
              ·
                refine ⟨1629571859424984165849443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4345524958466624442265181 1629571859424984165849443)
                ·
                  refine ⟨2444357789137476248774165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1629571859424984165849443 2444357789137476248774165)
                  ·
                    refine ⟨114579271365819199161289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2444357789137476248774165 114579271365819199161289)
                    ·
                      rfl

theorem cell23_669427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 6].length) (baseStart_669427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669427 prefixEnd_669427 := by exact prefixLift 669427
  have htrace : WordTrace (prefixWord ++ tailWord_669427) baseStart_669427 baseEnd_669427 := by
    simpa [prefixWord, tailWord_669427, baseEnd_669427] using wordTrace_append hprefix tailTrace_669427
  have hstable : (prefixWord ++ tailWord_669427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669427).length < 2 ^ (prefixWord ++ tailWord_669427).sum := by decide
  have hdescent : baseEnd_669427 < baseStart_669427 := by decide
  rcases family_descends (prefixWord ++ tailWord_669427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669434 : List Nat := [3, 1, 1, 1, 1, 3, 1, 6, 1, 1, 4]
def baseStart_669434 : Nat := 118140960795 + 669434 * 2 ^ 59
def prefixEnd_669434 : Nat := 4983230072969 + 3 ^ 40 * 669434 * 2
def baseEnd_669434 : Nat := 343741408462039070096335

theorem tailTrace_669434 : CollatzResearch.WordTrace tailWord_669434 prefixEnd_669434 343741408462039070096335 := by
  unfold tailWord_669434
  simp only [CollatzResearch.WordTrace]
  refine ⟨6104065964190605767503839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16277509237841615380010237 6104065964190605767503839)
  ·
    refine ⟨9156098946285908651255759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6104065964190605767503839 9156098946285908651255759)
    ·
      refine ⟨13734148419428862976883639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9156098946285908651255759 13734148419428862976883639)
      ·
        refine ⟨20601222629143294465325459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13734148419428862976883639 20601222629143294465325459)
        ·
          refine ⟨30901833943714941697988189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20601222629143294465325459 30901833943714941697988189)
          ·
            refine ⟨11588187728893103136745571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30901833943714941697988189 11588187728893103136745571)
            ·
              refine ⟨17382281593339654705118357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11588187728893103136745571 17382281593339654705118357)
              ·
                refine ⟨814794449687796314302423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17382281593339654705118357 814794449687796314302423)
                ·
                  refine ⟨1222191674531694471453635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 814794449687796314302423 1222191674531694471453635)
                  ·
                    refine ⟨1833287511797541707180453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1222191674531694471453635 1833287511797541707180453)
                    ·
                      refine ⟨343741408462039070096335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1833287511797541707180453 343741408462039070096335)
                      ·
                        rfl

theorem cell23_669434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 1, 1, 4].length) (baseStart_669434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669434 prefixEnd_669434 := by exact prefixLift 669434
  have htrace : WordTrace (prefixWord ++ tailWord_669434) baseStart_669434 baseEnd_669434 := by
    simpa [prefixWord, tailWord_669434, baseEnd_669434] using wordTrace_append hprefix tailTrace_669434
  have hstable : (prefixWord ++ tailWord_669434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669434).length < 2 ^ (prefixWord ++ tailWord_669434).sum := by decide
  have hdescent : baseEnd_669434 < baseStart_669434 := by decide
  rcases family_descends (prefixWord ++ tailWord_669434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669437 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 5, 1, 5]
def baseStart_669437 : Nat := 118140960795 + 669437 * 2 ^ 59
def prefixEnd_669437 : Nat := 4983230072969 + 3 ^ 40 * 669437 * 2
def baseEnd_669437 : Nat := 343742948904002558358821

theorem tailTrace_669437 : CollatzResearch.WordTrace tailWord_669437 prefixEnd_669437 343742948904002558358821 := by
  unfold tailWord_669437
  simp only [CollatzResearch.WordTrace]
  refine ⟨24416373275751554582374565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16277582183834369721583043 24416373275751554582374565)
  ·
    refine ⟨4578069989203416484195231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24416373275751554582374565 4578069989203416484195231)
    ·
      refine ⟨6867104983805124726292847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4578069989203416484195231 6867104983805124726292847)
      ·
        refine ⟨10300657475707687089439271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6867104983805124726292847 10300657475707687089439271)
        ·
          refine ⟨15450986213561530634158907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10300657475707687089439271 15450986213561530634158907)
          ·
            refine ⟨23176479320342295951238361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15450986213561530634158907 23176479320342295951238361)
            ·
              refine ⟨17382359490256721963428771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23176479320342295951238361 17382359490256721963428771)
              ·
                refine ⟨26073539235385082945143157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17382359490256721963428771 26073539235385082945143157)
                ·
                  refine ⟨2444394303317351526107171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26073539235385082945143157 2444394303317351526107171)
                  ·
                    refine ⟨3666591454976027289160757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2444394303317351526107171 3666591454976027289160757)
                    ·
                      refine ⟨343742948904002558358821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3666591454976027289160757 343742948904002558358821)
                      ·
                        rfl

theorem cell23_669437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_669437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669437 prefixEnd_669437 := by exact prefixLift 669437
  have htrace : WordTrace (prefixWord ++ tailWord_669437) baseStart_669437 baseEnd_669437 := by
    simpa [prefixWord, tailWord_669437, baseEnd_669437] using wordTrace_append hprefix tailTrace_669437
  have hstable : (prefixWord ++ tailWord_669437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669437).length < 2 ^ (prefixWord ++ tailWord_669437).sum := by decide
  have hdescent : baseEnd_669437 < baseStart_669437 := by decide
  rcases family_descends (prefixWord ++ tailWord_669437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669438 : List Nat := [4, 2, 2, 1, 3, 1, 1, 1, 1, 5, 2]
def baseStart_669438 : Nat := 118140960795 + 669438 * 2 ^ 59
def prefixEnd_669438 : Nat := 4983230072969 + 3 ^ 40 * 669438 * 2
def baseEnd_669438 : Nat := 343743462384657054446317

theorem tailTrace_669438 : CollatzResearch.WordTrace tailWord_669438 prefixEnd_669438 343743462384657054446317 := by
  unfold tailWord_669438
  simp only [CollatzResearch.WordTrace]
  refine ⟨3052051218593491469145121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16277606499165287835440645 3052051218593491469145121)
  ·
    refine ⟨2289038413945118601858841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3052051218593491469145121 2289038413945118601858841)
    ·
      refine ⟨1716778810458838951394131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2289038413945118601858841 1716778810458838951394131)
      ·
        refine ⟨2575168215688258427091197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1716778810458838951394131 2575168215688258427091197)
        ·
          refine ⟨965688080883096910159199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2575168215688258427091197 965688080883096910159199)
          ·
            refine ⟨1448532121324645365238799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 965688080883096910159199 1448532121324645365238799)
            ·
              refine ⟨2172798181986968047858199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1448532121324645365238799 2172798181986968047858199)
              ·
                refine ⟨3259197272980452071787299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2172798181986968047858199 3259197272980452071787299)
                ·
                  refine ⟨4888795909470678107680949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3259197272980452071787299 4888795909470678107680949)
                  ·
                    refine ⟨458324616512876072595089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4888795909470678107680949 458324616512876072595089)
                    ·
                      refine ⟨343743462384657054446317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 458324616512876072595089 343743462384657054446317)
                      ·
                        rfl

theorem cell23_669438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_669438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669438 prefixEnd_669438 := by exact prefixLift 669438
  have htrace : WordTrace (prefixWord ++ tailWord_669438) baseStart_669438 baseEnd_669438 := by
    simpa [prefixWord, tailWord_669438, baseEnd_669438] using wordTrace_append hprefix tailTrace_669438
  have hstable : (prefixWord ++ tailWord_669438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669438).length < 2 ^ (prefixWord ++ tailWord_669438).sum := by decide
  have hdescent : baseEnd_669438 < baseStart_669438 := by decide
  rcases family_descends (prefixWord ++ tailWord_669438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669444 : List Nat := [2, 3, 2, 2, 1, 2, 2, 2, 1, 6]
def baseStart_669444 : Nat := 118140960795 + 669444 * 2 ^ 59
def prefixEnd_669444 : Nat := 4983230072969 + 3 ^ 40 * 669444 * 2
def baseEnd_669444 : Nat := 114582181089528010323763

theorem tailTrace_669444 : CollatzResearch.WordTrace tailWord_669444 prefixEnd_669444 114582181089528010323763 := by
  unfold tailWord_669444
  simp only [CollatzResearch.WordTrace]
  refine ⟨12208314293363097388939693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16277752391150796518586257 12208314293363097388939693)
  ·
    refine ⟨4578117860011161520852385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12208314293363097388939693 4578117860011161520852385)
    ·
      refine ⟨3433588395008371140639289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4578117860011161520852385 3433588395008371140639289)
      ·
        refine ⟨2575191296256278355479467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3433588395008371140639289 2575191296256278355479467)
        ·
          refine ⟨3862786944384417533219201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2575191296256278355479467 3862786944384417533219201)
          ·
            refine ⟨2897090208288313149914401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3862786944384417533219201 2897090208288313149914401)
            ·
              refine ⟨2172817656216234862435801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2897090208288313149914401 2172817656216234862435801)
              ·
                refine ⟨1629613242162176146826851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2172817656216234862435801 1629613242162176146826851)
                ·
                  refine ⟨2444419863243264220240277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1629613242162176146826851 2444419863243264220240277)
                  ·
                    refine ⟨114582181089528010323763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2444419863243264220240277 114582181089528010323763)
                    ·
                      rfl

theorem cell23_669444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_669444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669444 prefixEnd_669444 := by exact prefixLift 669444
  have htrace : WordTrace (prefixWord ++ tailWord_669444) baseStart_669444 baseEnd_669444 := by
    simpa [prefixWord, tailWord_669444, baseEnd_669444] using wordTrace_append hprefix tailTrace_669444
  have hstable : (prefixWord ++ tailWord_669444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669444).length < 2 ^ (prefixWord ++ tailWord_669444).sum := by decide
  have hdescent : baseEnd_669444 < baseStart_669444 := by decide
  rcases family_descends (prefixWord ++ tailWord_669444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669451 : List Nat := [1, 1, 1, 1, 5, 1, 6, 1, 1, 1, 4]
def baseStart_669451 : Nat := 118140960795 + 669451 * 2 ^ 59
def prefixEnd_669451 : Nat := 4983230072969 + 3 ^ 40 * 669451 * 2
def baseEnd_669451 : Nat := 343750137633165503583757

theorem tailTrace_669451 : CollatzResearch.WordTrace tailWord_669451 prefixEnd_669451 343750137633165503583757 := by
  unfold tailWord_669451
  simp only [CollatzResearch.WordTrace]
  refine ⟨24416883897700834973384207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16277922598467223315589471 24416883897700834973384207)
  ·
    refine ⟨36625325846551252460076311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24416883897700834973384207 36625325846551252460076311)
    ·
      refine ⟨54937988769826878690114467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36625325846551252460076311 54937988769826878690114467)
      ·
        refine ⟨82406983154740318035171701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54937988769826878690114467 82406983154740318035171701)
        ·
          refine ⟨7725654670756904815797347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82406983154740318035171701 7725654670756904815797347)
          ·
            refine ⟨11588482006135357223696021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7725654670756904815797347 11588482006135357223696021)
            ·
              refine ⟨543210094037594869860751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11588482006135357223696021 543210094037594869860751)
              ·
                refine ⟨814815141056392304791127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 543210094037594869860751 814815141056392304791127)
                ·
                  refine ⟨1222222711584588457186691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 814815141056392304791127 1222222711584588457186691)
                  ·
                    refine ⟨1833334067376882685780037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1222222711584588457186691 1833334067376882685780037)
                    ·
                      refine ⟨343750137633165503583757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1833334067376882685780037 343750137633165503583757)
                      ·
                        rfl

theorem cell23_669451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 1, 1, 4].length) (baseStart_669451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669451 prefixEnd_669451 := by exact prefixLift 669451
  have htrace : WordTrace (prefixWord ++ tailWord_669451) baseStart_669451 baseEnd_669451 := by
    simpa [prefixWord, tailWord_669451, baseEnd_669451] using wordTrace_append hprefix tailTrace_669451
  have hstable : (prefixWord ++ tailWord_669451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669451).length < 2 ^ (prefixWord ++ tailWord_669451).sum := by decide
  have hdescent : baseEnd_669451 < baseStart_669451 := by decide
  rcases family_descends (prefixWord ++ tailWord_669451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669461 : List Nat := [1, 3, 2, 1, 2, 3, 3, 2, 2, 4]
def baseStart_669461 : Nat := 118140960795 + 669461 * 2 ^ 59
def prefixEnd_669461 : Nat := 4983230072969 + 3 ^ 40 * 669461 * 2
def baseEnd_669461 : Nat := 114585090813236821486237

theorem tailTrace_669461 : CollatzResearch.WordTrace tailWord_669461 prefixEnd_669461 114585090813236821486237 := by
  unfold tailWord_669461
  simp only [CollatzResearch.WordTrace]
  refine ⟨24417248627664606681248237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16278165751776404454165491 24417248627664606681248237)
  ·
    refine ⟨9156468235374227505468089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24417248627664606681248237 9156468235374227505468089)
    ·
      refine ⟨6867351176530670629101067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9156468235374227505468089 6867351176530670629101067)
      ·
        refine ⟨10301026764796005943651601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6867351176530670629101067 10301026764796005943651601)
        ·
          refine ⟨7725770073597004457738701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10301026764796005943651601 7725770073597004457738701)
          ·
            refine ⟨2897163777598876671652013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7725770073597004457738701 2897163777598876671652013)
            ·
              refine ⟨1086436416599578751869505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2897163777598876671652013 1086436416599578751869505)
              ·
                refine ⟨814827312449684063902129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1086436416599578751869505 814827312449684063902129)
                ·
                  refine ⟨611120484337263047926597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 814827312449684063902129 611120484337263047926597)
                  ·
                    refine ⟨114585090813236821486237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 611120484337263047926597 114585090813236821486237)
                    ·
                      rfl

theorem cell23_669461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_669461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669461 prefixEnd_669461 := by exact prefixLift 669461
  have htrace : WordTrace (prefixWord ++ tailWord_669461) baseStart_669461 baseEnd_669461 := by
    simpa [prefixWord, tailWord_669461, baseEnd_669461] using wordTrace_append hprefix tailTrace_669461
  have hstable : (prefixWord ++ tailWord_669461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669461).length < 2 ^ (prefixWord ++ tailWord_669461).sum := by decide
  have hdescent : baseEnd_669461 < baseStart_669461 := by decide
  rcases family_descends (prefixWord ++ tailWord_669461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669468 : List Nat := [2, 2, 3, 1, 1, 2, 4, 1, 3, 2, 2]
def baseStart_669468 : Nat := 118140960795 + 669468 * 2 ^ 59
def prefixEnd_669468 : Nat := 4983230072969 + 3 ^ 40 * 669468 * 2
def baseEnd_669468 : Nat := 343758866804291937071179

theorem tailTrace_669468 : CollatzResearch.WordTrace tailWord_669468 prefixEnd_669468 343758866804291937071179 := by
  unfold tailWord_669468
  simp only [CollatzResearch.WordTrace]
  refine ⟨12208751969319623438376529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16278335959092831251168705 12208751969319623438376529)
  ·
    refine ⟨9156563976989717578782397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12208751969319623438376529 9156563976989717578782397)
    ·
      refine ⟨3433711491371144092043399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9156563976989717578782397 3433711491371144092043399)
      ·
        refine ⟨5150567237056716138065099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3433711491371144092043399 5150567237056716138065099)
        ·
          refine ⟨7725850855585074207097649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5150567237056716138065099 7725850855585074207097649)
          ·
            refine ⟨5794388141688805655323237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7725850855585074207097649 5794388141688805655323237)
            ·
              refine ⟨1086447776566651060373107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5794388141688805655323237 1086447776566651060373107)
              ·
                refine ⟨1629671664849976590559661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1086447776566651060373107 1629671664849976590559661)
                ·
                  refine ⟨611126874318741221459873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1629671664849976590559661 611126874318741221459873)
                  ·
                    refine ⟨458345155739055916094905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 611126874318741221459873 458345155739055916094905)
                    ·
                      refine ⟨343758866804291937071179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 458345155739055916094905 343758866804291937071179)
                      ·
                        rfl

theorem cell23_669468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_669468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669468 prefixEnd_669468 := by exact prefixLift 669468
  have htrace : WordTrace (prefixWord ++ tailWord_669468) baseStart_669468 baseEnd_669468 := by
    simpa [prefixWord, tailWord_669468, baseEnd_669468] using wordTrace_append hprefix tailTrace_669468
  have hstable : (prefixWord ++ tailWord_669468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669468).length < 2 ^ (prefixWord ++ tailWord_669468).sum := by decide
  have hdescent : baseEnd_669468 < baseStart_669468 := by decide
  rcases family_descends (prefixWord ++ tailWord_669468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669491 : List Nat := [1, 1, 1, 2, 7, 2, 2, 7]
def baseStart_669491 : Nat := 118140960795 + 669491 * 2 ^ 59
def prefixEnd_669491 : Nat := 4983230072969 + 3 ^ 40 * 669491 * 2
def baseEnd_669491 : Nat := 12732247291086864706799

theorem tailTrace_669491 : CollatzResearch.WordTrace tailWord_669491 prefixEnd_669491 12732247291086864706799 := by
  unfold tailWord_669491
  simp only [CollatzResearch.WordTrace]
  refine ⟨24418342817555921804840327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16278895211703947869893551 24418342817555921804840327)
  ·
    refine ⟨36627514226333882707260491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24418342817555921804840327 36627514226333882707260491)
    ·
      refine ⟨54941271339500824060890737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36627514226333882707260491 54941271339500824060890737)
      ·
        refine ⟨41205953504625618045668053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54941271339500824060890737 41205953504625618045668053)
        ·
          refine ⟨965764535264662922945345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 41205953504625618045668053 965764535264662922945345)
          ·
            refine ⟨724323401448497192209009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 965764535264662922945345 724323401448497192209009)
            ·
              refine ⟨543242551086372894156757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 724323401448497192209009 543242551086372894156757)
              ·
                refine ⟨12732247291086864706799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 543242551086372894156757 12732247291086864706799)
                ·
                  rfl

theorem cell23_669491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 7].length) (baseStart_669491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669491 prefixEnd_669491 := by exact prefixLift 669491
  have htrace : WordTrace (prefixWord ++ tailWord_669491) baseStart_669491 baseEnd_669491 := by
    simpa [prefixWord, tailWord_669491, baseEnd_669491] using wordTrace_append hprefix tailTrace_669491
  have hstable : (prefixWord ++ tailWord_669491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669491).length < 2 ^ (prefixWord ++ tailWord_669491).sum := by decide
  have hdescent : baseEnd_669491 < baseStart_669491 := by decide
  rcases family_descends (prefixWord ++ tailWord_669491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669502 : List Nat := [4, 2, 1, 2, 2, 1, 3, 3, 1, 2, 2]
def baseStart_669502 : Nat := 118140960795 + 669502 * 2 ^ 59
def prefixEnd_669502 : Nat := 4983230072969 + 3 ^ 40 * 669502 * 2
def baseEnd_669502 : Nat := 343776325146544804046023

theorem tailTrace_669502 : CollatzResearch.WordTrace tailWord_669502 prefixEnd_669502 343776325146544804046023 := by
  unfold tailWord_669502
  simp only [CollatzResearch.WordTrace]
  refine ⟨3052343002564508835436345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16279162680344047122327173 3052343002564508835436345)
  ·
    refine ⟨2289257251923381626577259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3052343002564508835436345 2289257251923381626577259)
    ·
      refine ⟨3433885877885072439865889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2289257251923381626577259 3433885877885072439865889)
      ·
        refine ⟨2575414408413804329899417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3433885877885072439865889 2575414408413804329899417)
        ·
          refine ⟨1931560806310353247424563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2575414408413804329899417 1931560806310353247424563)
          ·
            refine ⟨2897341209465529871136845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1931560806310353247424563 2897341209465529871136845)
            ·
              refine ⟨1086502953549573701676317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2897341209465529871136845 1086502953549573701676317)
              ·
                refine ⟨407438607581090138128619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1086502953549573701676317 407438607581090138128619)
                ·
                  refine ⟨611157911371635207192929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 407438607581090138128619 611157911371635207192929)
                  ·
                    refine ⟨458368433528726405394697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 611157911371635207192929 458368433528726405394697)
                    ·
                      refine ⟨343776325146544804046023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 458368433528726405394697 343776325146544804046023)
                      ·
                        rfl

theorem cell23_669502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_669502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669502 prefixEnd_669502 := by exact prefixLift 669502
  have htrace : WordTrace (prefixWord ++ tailWord_669502) baseStart_669502 baseEnd_669502 := by
    simpa [prefixWord, tailWord_669502, baseEnd_669502] using wordTrace_append hprefix tailTrace_669502
  have hstable : (prefixWord ++ tailWord_669502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669502).length < 2 ^ (prefixWord ++ tailWord_669502).sum := by decide
  have hdescent : baseEnd_669502 < baseStart_669502 := by decide
  rcases family_descends (prefixWord ++ tailWord_669502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669535 : List Nat := [1, 1, 2, 3, 1, 6, 2, 1, 2, 1, 3]
def baseStart_669535 : Nat := 118140960795 + 669535 * 2 ^ 59
def prefixEnd_669535 : Nat := 4983230072969 + 3 ^ 40 * 669535 * 2
def baseEnd_669535 : Nat := 343793270008143174933371

theorem tailTrace_669535 : CollatzResearch.WordTrace tailWord_669535 prefixEnd_669535 343793270008143174933371 := by
  unfold tailWord_669535
  simp only [CollatzResearch.WordTrace]
  refine ⟨24419947629396517319442059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16279965086264344879628039 24419947629396517319442059)
  ·
    refine ⟨36629921444094775979163089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24419947629396517319442059 36629921444094775979163089)
    ·
      refine ⟨27472441083071081984372317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36629921444094775979163089 27472441083071081984372317)
      ·
        refine ⟨10302165406151655744139619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27472441083071081984372317 10302165406151655744139619)
        ·
          refine ⟨15453248109227483616209429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10302165406151655744139619 15453248109227483616209429)
          ·
            refine ⟨724371005120038294509817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15453248109227483616209429 724371005120038294509817)
            ·
              refine ⟨543278253840028720882363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 724371005120038294509817 543278253840028720882363)
              ·
                refine ⟨814917380760043081323545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 543278253840028720882363 814917380760043081323545)
                ·
                  refine ⟨611188035570032310992659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 814917380760043081323545 611188035570032310992659)
                  ·
                    refine ⟨916782053355048466488989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 611188035570032310992659 916782053355048466488989)
                    ·
                      refine ⟨343793270008143174933371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 916782053355048466488989 343793270008143174933371)
                      ·
                        rfl

theorem cell23_669535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 2, 1, 3].length) (baseStart_669535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669535 prefixEnd_669535 := by exact prefixLift 669535
  have htrace : WordTrace (prefixWord ++ tailWord_669535) baseStart_669535 baseEnd_669535 := by
    simpa [prefixWord, tailWord_669535, baseEnd_669535] using wordTrace_append hprefix tailTrace_669535
  have hstable : (prefixWord ++ tailWord_669535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669535).length < 2 ^ (prefixWord ++ tailWord_669535).sum := by decide
  have hdescent : baseEnd_669535 < baseStart_669535 := by decide
  rcases family_descends (prefixWord ++ tailWord_669535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669541 : List Nat := [1, 3, 1, 3, 1, 1, 1, 5, 1, 4, 2]
def baseStart_669541 : Nat := 118140960795 + 669541 * 2 ^ 59
def prefixEnd_669541 : Nat := 4983230072969 + 3 ^ 40 * 669541 * 2
def baseEnd_669541 : Nat := 343796350892070151458343

theorem tailTrace_669541 : CollatzResearch.WordTrace tailWord_669541 prefixEnd_669541 343796350892070151458343 := by
  unfold tailWord_669541
  simp only [CollatzResearch.WordTrace]
  refine ⟨24420166467374780344160477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16280110978249853562773651 24420166467374780344160477)
  ·
    refine ⟨9157562425265542629060179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24420166467374780344160477 9157562425265542629060179)
    ·
      refine ⟨13736343637898313943590269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9157562425265542629060179 13736343637898313943590269)
      ·
        refine ⟨5151128864211867728846351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13736343637898313943590269 5151128864211867728846351)
        ·
          refine ⟨7726693296317801593269527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5151128864211867728846351 7726693296317801593269527)
          ·
            refine ⟨11590039944476702389904291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7726693296317801593269527 11590039944476702389904291)
            ·
              refine ⟨17385059916715053584856437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11590039944476702389904291 17385059916715053584856437)
              ·
                refine ⟨1629849367192036273580291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17385059916715053584856437 1629849367192036273580291)
                ·
                  refine ⟨2444774050788054410370437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1629849367192036273580291 2444774050788054410370437)
                  ·
                    refine ⟨458395134522760201944457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2444774050788054410370437 458395134522760201944457)
                    ·
                      refine ⟨343796350892070151458343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 458395134522760201944457 343796350892070151458343)
                      ·
                        rfl

theorem cell23_669541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_669541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669541 prefixEnd_669541 := by exact prefixLift 669541
  have htrace : WordTrace (prefixWord ++ tailWord_669541) baseStart_669541 baseEnd_669541 := by
    simpa [prefixWord, tailWord_669541, baseEnd_669541] using wordTrace_append hprefix tailTrace_669541
  have hstable : (prefixWord ++ tailWord_669541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669541).length < 2 ^ (prefixWord ++ tailWord_669541).sum := by decide
  have hdescent : baseEnd_669541 < baseStart_669541 := by decide
  rcases family_descends (prefixWord ++ tailWord_669541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669544 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 4, 1, 5]
def baseStart_669544 : Nat := 118140960795 + 669544 * 2 ^ 59
def prefixEnd_669544 : Nat := 4983230072969 + 3 ^ 40 * 669544 * 2
def baseEnd_669544 : Nat := 343797891334033639720829

theorem tailTrace_669544 : CollatzResearch.WordTrace tailWord_669544 prefixEnd_669544 343797891334033639720829 := by
  unfold tailWord_669544
  simp only [CollatzResearch.WordTrace]
  refine ⟨12210137943181955928259843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16280183924242607904346457 12210137943181955928259843)
  ·
    refine ⟨18315206914772933892389765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12210137943181955928259843 18315206914772933892389765)
    ·
      refine ⟨3434101296519925104823081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18315206914772933892389765 3434101296519925104823081)
      ·
        refine ⟨2575575972389943828617311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3434101296519925104823081 2575575972389943828617311)
        ·
          refine ⟨3863363958584915742925967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2575575972389943828617311 3863363958584915742925967)
          ·
            refine ⟨5795045937877373614388951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3863363958584915742925967 5795045937877373614388951)
            ·
              refine ⟨8692568906816060421583427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5795045937877373614388951 8692568906816060421583427)
              ·
                refine ⟨13038853360224090632375141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8692568906816060421583427 13038853360224090632375141)
                ·
                  refine ⟨2444785005042016993570339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13038853360224090632375141 2444785005042016993570339)
                  ·
                    refine ⟨3667177507563025490355509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2444785005042016993570339 3667177507563025490355509)
                    ·
                      refine ⟨343797891334033639720829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3667177507563025490355509 343797891334033639720829)
                      ·
                        rfl

theorem cell23_669544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_669544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669544 prefixEnd_669544 := by exact prefixLift 669544
  have htrace : WordTrace (prefixWord ++ tailWord_669544) baseStart_669544 baseEnd_669544 := by
    simpa [prefixWord, tailWord_669544, baseEnd_669544] using wordTrace_append hprefix tailTrace_669544
  have hstable : (prefixWord ++ tailWord_669544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669544).length < 2 ^ (prefixWord ++ tailWord_669544).sum := by decide
  have hdescent : baseEnd_669544 < baseStart_669544 := by decide
  rcases family_descends (prefixWord ++ tailWord_669544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669547 : List Nat := [1, 1, 1, 1, 2, 2, 3, 3, 9]
def baseStart_669547 : Nat := 118140960795 + 669547 * 2 ^ 59
def prefixEnd_669547 : Nat := 4983230072969 + 3 ^ 40 * 669547 * 2
def baseEnd_669547 : Nat := 38199936863999680887035

theorem tailTrace_669547 : CollatzResearch.WordTrace tailWord_669547 prefixEnd_669547 38199936863999680887035 := by
  unfold tailWord_669547
  simp only [CollatzResearch.WordTrace]
  refine ⟨24420385305353043368878895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16280256870235362245919263 24420385305353043368878895)
  ·
    refine ⟨36630577958029565053318343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24420385305353043368878895 36630577958029565053318343)
    ·
      refine ⟨54945866937044347579977515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36630577958029565053318343 54945866937044347579977515)
      ·
        refine ⟨82418800405566521369966273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54945866937044347579977515 82418800405566521369966273)
        ·
          refine ⟨61814100304174891027474705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82418800405566521369966273 61814100304174891027474705)
          ·
            refine ⟨46360575228131168270606029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61814100304174891027474705 46360575228131168270606029)
            ·
              refine ⟨17385215710549188101477261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46360575228131168270606029 17385215710549188101477261)
              ·
                refine ⟨6519455891455945538053973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17385215710549188101477261 6519455891455945538053973)
                ·
                  refine ⟨38199936863999680887035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6519455891455945538053973 38199936863999680887035)
                  ·
                    rfl

theorem cell23_669547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 9].length) (baseStart_669547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669547 prefixEnd_669547 := by exact prefixLift 669547
  have htrace : WordTrace (prefixWord ++ tailWord_669547) baseStart_669547 baseEnd_669547 := by
    simpa [prefixWord, tailWord_669547, baseEnd_669547] using wordTrace_append hprefix tailTrace_669547
  have hstable : (prefixWord ++ tailWord_669547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669547).length < 2 ^ (prefixWord ++ tailWord_669547).sum := by decide
  have hdescent : baseEnd_669547 < baseStart_669547 := by decide
  rcases family_descends (prefixWord ++ tailWord_669547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669554 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 4, 2, 4]
def baseStart_669554 : Nat := 118140960795 + 669554 * 2 ^ 59
def prefixEnd_669554 : Nat := 4983230072969 + 3 ^ 40 * 669554 * 2
def baseEnd_669554 : Nat := 343803026140578600595783

theorem tailTrace_669554 : CollatzResearch.WordTrace tailWord_669554 prefixEnd_669554 343803026140578600595783 := by
  unfold tailWord_669554
  simp only [CollatzResearch.WordTrace]
  refine ⟨6105160154081920891095929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16280427077551789042922477 6105160154081920891095929)
  ·
    refine ⟨4578870115561440668321947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6105160154081920891095929 4578870115561440668321947)
    ·
      refine ⟨6868305173342161002482921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4578870115561440668321947 6868305173342161002482921)
      ·
        refine ⟨5151228880006620751862191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6868305173342161002482921 5151228880006620751862191)
        ·
          refine ⟨7726843320009931127793287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5151228880006620751862191 7726843320009931127793287)
          ·
            refine ⟨11590264980014896691689931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7726843320009931127793287 11590264980014896691689931)
            ·
              refine ⟨17385397470022345037534897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11590264980014896691689931 17385397470022345037534897)
              ·
                refine ⟨13039048102516758778151173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17385397470022345037534897 13039048102516758778151173)
                ·
                  refine ⟨2444821519221892270903345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13039048102516758778151173 2444821519221892270903345)
                  ·
                    refine ⟨1833616139416419203177509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2444821519221892270903345 1833616139416419203177509)
                    ·
                      refine ⟨343803026140578600595783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1833616139416419203177509 343803026140578600595783)
                      ·
                        rfl

theorem cell23_669554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_669554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669554 prefixEnd_669554 := by exact prefixLift 669554
  have htrace : WordTrace (prefixWord ++ tailWord_669554) baseStart_669554 baseEnd_669554 := by
    simpa [prefixWord, tailWord_669554, baseEnd_669554] using wordTrace_append hprefix tailTrace_669554
  have hstable : (prefixWord ++ tailWord_669554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669554).length < 2 ^ (prefixWord ++ tailWord_669554).sum := by decide
  have hdescent : baseEnd_669554 < baseStart_669554 := by decide
  rcases family_descends (prefixWord ++ tailWord_669554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669591 : List Nat := [1, 1, 3, 3, 1, 4, 1, 1, 2, 3, 3]
def baseStart_669591 : Nat := 118140960795 + 669591 * 2 ^ 59
def prefixEnd_669591 : Nat := 4983230072969 + 3 ^ 40 * 669591 * 2
def baseEnd_669591 : Nat := 343822024924794955833113

theorem tailTrace_669591 : CollatzResearch.WordTrace tailWord_669591 prefixEnd_669591 343822024924794955833113 := by
  unfold tailWord_669591
  simp only [CollatzResearch.WordTrace]
  refine ⟨24421990117193638883480627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16281326744795759255653751 24421990117193638883480627)
  ·
    refine ⟨36632985175790458325220941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24421990117193638883480627 36632985175790458325220941)
    ·
      refine ⟨13737369440921421871957853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36632985175790458325220941 13737369440921421871957853)
      ·
        refine ⟨5151513540345533201984195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13737369440921421871957853 5151513540345533201984195)
        ·
          refine ⟨7727270310518299802976293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5151513540345533201984195 7727270310518299802976293)
          ·
            refine ⟨1448863183222181213058055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7727270310518299802976293 1448863183222181213058055)
            ·
              refine ⟨2173294774833271819587083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1448863183222181213058055 2173294774833271819587083)
              ·
                refine ⟨3259942162249907729380625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2173294774833271819587083 3259942162249907729380625)
                ·
                  refine ⟨2444956621687430797035469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3259942162249907729380625 2444956621687430797035469)
                  ·
                    refine ⟨916858733132786548888301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2444956621687430797035469 916858733132786548888301)
                    ·
                      refine ⟨343822024924794955833113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 916858733132786548888301 343822024924794955833113)
                      ·
                        rfl

theorem cell23_669591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_669591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669591 prefixEnd_669591 := by exact prefixLift 669591
  have htrace : WordTrace (prefixWord ++ tailWord_669591) baseStart_669591 baseEnd_669591 := by
    simpa [prefixWord, tailWord_669591, baseEnd_669591] using wordTrace_append hprefix tailTrace_669591
  have hstable : (prefixWord ++ tailWord_669591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669591).length < 2 ^ (prefixWord ++ tailWord_669591).sum := by decide
  have hdescent : baseEnd_669591 < baseStart_669591 := by decide
  rcases family_descends (prefixWord ++ tailWord_669591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669631 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 4, 4, 2]
def baseStart_669631 : Nat := 118140960795 + 669631 * 2 ^ 59
def prefixEnd_669631 : Nat := 4983230072969 + 3 ^ 40 * 669631 * 2
def baseEnd_669631 : Nat := 343842564150974799332929

theorem tailTrace_669631 : CollatzResearch.WordTrace tailWord_669631 prefixEnd_669631 343842564150974799332929 := by
  unfold tailWord_669631
  simp only [CollatzResearch.WordTrace]
  refine ⟨24423449037048725714936747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16282299358032483809957831 24423449037048725714936747)
  ·
    refine ⟨36635173555573088572405121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24423449037048725714936747 36635173555573088572405121)
    ·
      refine ⟨27476380166679816429303841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36635173555573088572405121 27476380166679816429303841)
      ·
        refine ⟨20607285125009862321977881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27476380166679816429303841 20607285125009862321977881)
        ·
          refine ⟨15455463843757396741483411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20607285125009862321977881 15455463843757396741483411)
          ·
            refine ⟨23183195765636095112225117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15455463843757396741483411 23183195765636095112225117)
            ·
              refine ⟨8693698412113535667084419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23183195765636095112225117 8693698412113535667084419)
              ·
                refine ⟨13040547618170303500626629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8693698412113535667084419 13040547618170303500626629)
                ·
                  refine ⟨2445102678406931906367493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13040547618170303500626629 2445102678406931906367493)
                  ·
                    refine ⟨458456752201299732443905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2445102678406931906367493 458456752201299732443905)
                    ·
                      refine ⟨343842564150974799332929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 458456752201299732443905 343842564150974799332929)
                      ·
                        rfl

theorem cell23_669631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 4, 2].length) (baseStart_669631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669631 prefixEnd_669631 := by exact prefixLift 669631
  have htrace : WordTrace (prefixWord ++ tailWord_669631) baseStart_669631 baseEnd_669631 := by
    simpa [prefixWord, tailWord_669631, baseEnd_669631] using wordTrace_append hprefix tailTrace_669631
  have hstable : (prefixWord ++ tailWord_669631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669631).length < 2 ^ (prefixWord ++ tailWord_669631).sum := by decide
  have hdescent : baseEnd_669631 < baseStart_669631 := by decide
  rcases family_descends (prefixWord ++ tailWord_669631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669708 : List Nat := [2, 2, 1, 2, 3, 1, 1, 2, 4, 3, 2]
def baseStart_669708 : Nat := 118140960795 + 669708 * 2 ^ 59
def prefixEnd_669708 : Nat := 4983230072969 + 3 ^ 40 * 669708 * 2
def baseEnd_669708 : Nat := 343882102161370998070075

theorem tailTrace_669708 : CollatzResearch.WordTrace tailWord_669708 prefixEnd_669708 343882102161370998070075 := by
  unfold tailWord_669708
  simp only [CollatzResearch.WordTrace]
  refine ⟨12213128728884883932744889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16284171638513178576993185 12213128728884883932744889)
  ·
    refine ⟨9159846546663662949558667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12213128728884883932744889 9159846546663662949558667)
    ·
      refine ⟨13739769819995494424338001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9159846546663662949558667 13739769819995494424338001)
      ·
        refine ⟨10304827364996620818253501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13739769819995494424338001 10304827364996620818253501)
        ·
          refine ⟨3864310261873732806845063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10304827364996620818253501 3864310261873732806845063)
          ·
            refine ⟨5796465392810599210267595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3864310261873732806845063 5796465392810599210267595)
            ·
              refine ⟨8694698089215898815401393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5796465392810599210267595 8694698089215898815401393)
              ·
                refine ⟨6521023566911924111551045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8694698089215898815401393 6521023566911924111551045)
                ·
                  refine ⟨1222691918795985770915821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6521023566911924111551045 1222691918795985770915821)
                  ·
                    refine ⟨458509469548494664093433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1222691918795985770915821 458509469548494664093433)
                    ·
                      refine ⟨343882102161370998070075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 458509469548494664093433 343882102161370998070075)
                      ·
                        rfl

theorem cell23_669708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 4, 3, 2].length) (baseStart_669708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669708 prefixEnd_669708 := by exact prefixLift 669708
  have htrace : WordTrace (prefixWord ++ tailWord_669708) baseStart_669708 baseEnd_669708 := by
    simpa [prefixWord, tailWord_669708, baseEnd_669708] using wordTrace_append hprefix tailTrace_669708
  have hstable : (prefixWord ++ tailWord_669708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669708).length < 2 ^ (prefixWord ++ tailWord_669708).sum := by decide
  have hdescent : baseEnd_669708 < baseStart_669708 := by decide
  rcases family_descends (prefixWord ++ tailWord_669708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669725 : List Nat := [1, 4, 2, 2, 2, 1, 1, 3, 2, 3, 2]
def baseStart_669725 : Nat := 118140960795 + 669725 * 2 ^ 59
def prefixEnd_669725 : Nat := 4983230072969 + 3 ^ 40 * 669725 * 2
def baseEnd_669725 : Nat := 343890831332497431557497

theorem tailTrace_669725 : CollatzResearch.WordTrace tailWord_669725 prefixEnd_669725 343890831332497431557497 := by
  unfold tailWord_669725
  simp only [CollatzResearch.WordTrace]
  refine ⟨24426877498708179768858629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16284584999138786512572419 24426877498708179768858629)
  ·
    refine ⟨4580039531007783706660993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24426877498708179768858629 4580039531007783706660993)
    ·
      refine ⟨3435029648255837779995745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4580039531007783706660993 3435029648255837779995745)
      ·
        refine ⟨2576272236191878334996809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3435029648255837779995745 2576272236191878334996809)
        ·
          refine ⟨1932204177143908751247607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2576272236191878334996809 1932204177143908751247607)
          ·
            refine ⟨2898306265715863126871411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1932204177143908751247607 2898306265715863126871411)
            ·
              refine ⟨4347459398573794690307117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2898306265715863126871411 4347459398573794690307117)
              ·
                refine ⟨1630297274465173008865169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4347459398573794690307117 1630297274465173008865169)
                ·
                  refine ⟨1222722955848879756648877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1630297274465173008865169 1222722955848879756648877)
                  ·
                    refine ⟨458521108443329908743329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1222722955848879756648877 458521108443329908743329)
                    ·
                      refine ⟨343890831332497431557497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 458521108443329908743329 343890831332497431557497)
                      ·
                        rfl

theorem cell23_669725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_669725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669725 prefixEnd_669725 := by exact prefixLift 669725
  have htrace : WordTrace (prefixWord ++ tailWord_669725) baseStart_669725 baseEnd_669725 := by
    simpa [prefixWord, tailWord_669725, baseEnd_669725] using wordTrace_append hprefix tailTrace_669725
  have hstable : (prefixWord ++ tailWord_669725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669725).length < 2 ^ (prefixWord ++ tailWord_669725).sum := by decide
  have hdescent : baseEnd_669725 < baseStart_669725 := by decide
  rcases family_descends (prefixWord ++ tailWord_669725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669731 : List Nat := [1, 1, 1, 4, 3, 1, 3, 2, 1, 6]
def baseStart_669731 : Nat := 118140960795 + 669731 * 2 ^ 59
def prefixEnd_669731 : Nat := 4983230072969 + 3 ^ 40 * 669731 * 2
def baseEnd_669731 : Nat := 114631304072141469360823

theorem tailTrace_669731 : CollatzResearch.WordTrace tailWord_669731 prefixEnd_669731 114631304072141469360823 := by
  unfold tailWord_669731
  simp only [CollatzResearch.WordTrace]
  refine ⟨24427096336686442793577047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16284730891124295195718031 24427096336686442793577047)
  ·
    refine ⟨36640644505029664190365571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24427096336686442793577047 36640644505029664190365571)
    ·
      refine ⟨54960966757544496285548357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36640644505029664190365571 54960966757544496285548357)
      ·
        refine ⟨10305181267039593053540317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54960966757544496285548357 10305181267039593053540317)
        ·
          refine ⟨3864442975139847395077619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10305181267039593053540317 3864442975139847395077619)
          ·
            refine ⟨5796664462709771092616429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3864442975139847395077619 5796664462709771092616429)
            ·
              refine ⟨2173749173516164159731161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5796664462709771092616429 2173749173516164159731161)
              ·
                refine ⟨1630311880137123119798371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2173749173516164159731161 1630311880137123119798371)
                ·
                  refine ⟨2445467820205684679697557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1630311880137123119798371 2445467820205684679697557)
                  ·
                    refine ⟨114631304072141469360823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2445467820205684679697557 114631304072141469360823)
                    ·
                      rfl

theorem cell23_669731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 6].length) (baseStart_669731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669731 prefixEnd_669731 := by exact prefixLift 669731
  have htrace : WordTrace (prefixWord ++ tailWord_669731) baseStart_669731 baseEnd_669731 := by
    simpa [prefixWord, tailWord_669731, baseEnd_669731] using wordTrace_append hprefix tailTrace_669731
  have hstable : (prefixWord ++ tailWord_669731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669731).length < 2 ^ (prefixWord ++ tailWord_669731).sum := by decide
  have hdescent : baseEnd_669731 < baseStart_669731 := by decide
  rcases family_descends (prefixWord ++ tailWord_669731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669744 : List Nat := [2, 1, 1, 1, 2, 16]
def baseStart_669744 : Nat := 118140960795 + 669744 * 2 ^ 59
def prefixEnd_669744 : Nat := 4983230072969 + 3 ^ 40 * 669744 * 2
def baseEnd_669744 : Nat := 1415228754999723692263

theorem tailTrace_669744 : CollatzResearch.WordTrace tailWord_669744 prefixEnd_669744 1415228754999723692263 := by
  unfold tailWord_669744
  simp only [CollatzResearch.WordTrace]
  refine ⟨12213785242819673006900143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16285046990426230675866857 12213785242819673006900143)
  ·
    refine ⟨18320677864229509510350215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12213785242819673006900143 18320677864229509510350215)
    ·
      refine ⟨27481016796344264265525323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18320677864229509510350215 27481016796344264265525323)
      ·
        refine ⟨41221525194516396398287985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27481016796344264265525323 41221525194516396398287985)
        ·
          refine ⟨30916143895887297298715989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41221525194516396398287985 30916143895887297298715989)
          ·
            refine ⟨1415228754999723692263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 16 30916143895887297298715989 1415228754999723692263)
            ·
              rfl

theorem cell23_669744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 16].length) (baseStart_669744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669744 prefixEnd_669744 := by exact prefixLift 669744
  have htrace : WordTrace (prefixWord ++ tailWord_669744) baseStart_669744 baseEnd_669744 := by
    simpa [prefixWord, tailWord_669744, baseEnd_669744] using wordTrace_append hprefix tailTrace_669744
  have hstable : (prefixWord ++ tailWord_669744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669744).length < 2 ^ (prefixWord ++ tailWord_669744).sum := by decide
  have hdescent : baseEnd_669744 < baseStart_669744 := by decide
  rcases family_descends (prefixWord ++ tailWord_669744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669771 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 5, 3, 3]
def baseStart_669771 : Nat := 118140960795 + 669771 * 2 ^ 59
def prefixEnd_669771 : Nat := 4983230072969 + 3 ^ 40 * 669771 * 2
def baseEnd_669771 : Nat := 343914451442604251582285

theorem tailTrace_669771 : CollatzResearch.WordTrace tailWord_669771 prefixEnd_669771 343914451442604251582285 := by
  unfold tailWord_669771
  simp only [CollatzResearch.WordTrace]
  refine ⟨24428555256541529625033167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16285703504361019750022111 24428555256541529625033167)
  ·
    refine ⟨36642832884812294437549751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24428555256541529625033167 36642832884812294437549751)
    ·
      refine ⟨54964249327218441656324627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36642832884812294437549751 54964249327218441656324627)
      ·
        refine ⟨82446373990827662484486941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54964249327218441656324627 82446373990827662484486941)
        ·
          refine ⟨30917390246560373431682603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82446373990827662484486941 30917390246560373431682603)
          ·
            refine ⟨46376085369840560147523905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30917390246560373431682603 46376085369840560147523905)
            ·
              refine ⟨34782064027380420110642929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46376085369840560147523905 34782064027380420110642929)
              ·
                refine ⟨26086548020535315082982197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34782064027380420110642929 26086548020535315082982197)
                ·
                  refine ⟨2445613876925185789029581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26086548020535315082982197 2445613876925185789029581)
                  ·
                    refine ⟨917105203846944670886093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2445613876925185789029581 917105203846944670886093)
                    ·
                      refine ⟨343914451442604251582285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 917105203846944670886093 343914451442604251582285)
                      ·
                        rfl

theorem cell23_669771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 3, 3].length) (baseStart_669771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669771 prefixEnd_669771 := by exact prefixLift 669771
  have htrace : WordTrace (prefixWord ++ tailWord_669771) baseStart_669771 baseEnd_669771 := by
    simpa [prefixWord, tailWord_669771, baseEnd_669771] using wordTrace_append hprefix tailTrace_669771
  have hstable : (prefixWord ++ tailWord_669771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669771).length < 2 ^ (prefixWord ++ tailWord_669771).sum := by decide
  have hdescent : baseEnd_669771 < baseStart_669771 := by decide
  rcases family_descends (prefixWord ++ tailWord_669771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669789 : List Nat := [1, 4, 4, 1, 1, 3, 2, 1, 1, 1, 4]
def baseStart_669789 : Nat := 118140960795 + 669789 * 2 ^ 59
def prefixEnd_669789 : Nat := 4983230072969 + 3 ^ 40 * 669789 * 2
def baseEnd_669789 : Nat := 343923694094385181157203

theorem tailTrace_669789 : CollatzResearch.WordTrace tailWord_669789 prefixEnd_669789 343923694094385181157203 := by
  unfold tailWord_669789
  simp only [CollatzResearch.WordTrace]
  refine ⟨24429211770476318699188421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16286141180317545799458947 24429211770476318699188421)
  ·
    refine ⟨4580477206964309756097829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24429211770476318699188421 4580477206964309756097829)
    ·
      refine ⟨858839476305808079268343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4580477206964309756097829 858839476305808079268343)
      ·
        refine ⟨1288259214458712118902515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 858839476305808079268343 1288259214458712118902515)
        ·
          refine ⟨1932388821688068178353773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1288259214458712118902515 1932388821688068178353773)
          ·
            refine ⟨724645808133025566882665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1932388821688068178353773 724645808133025566882665)
            ·
              refine ⟨543484356099769175161999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 724645808133025566882665 543484356099769175161999)
              ·
                refine ⟨815226534149653762742999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 543484356099769175161999 815226534149653762742999)
                ·
                  refine ⟨1222839801224480644114499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 815226534149653762742999 1222839801224480644114499)
                  ·
                    refine ⟨1834259701836720966171749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1222839801224480644114499 1834259701836720966171749)
                    ·
                      refine ⟨343923694094385181157203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1834259701836720966171749 343923694094385181157203)
                      ·
                        rfl

theorem cell23_669789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_669789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669789 prefixEnd_669789 := by exact prefixLift 669789
  have htrace : WordTrace (prefixWord ++ tailWord_669789) baseStart_669789 baseEnd_669789 := by
    simpa [prefixWord, tailWord_669789, baseEnd_669789] using wordTrace_append hprefix tailTrace_669789
  have hstable : (prefixWord ++ tailWord_669789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669789).length < 2 ^ (prefixWord ++ tailWord_669789).sum := by decide
  have hdescent : baseEnd_669789 < baseStart_669789 := by decide
  rcases family_descends (prefixWord ++ tailWord_669789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669792 : List Nat := [2, 1, 1, 3, 2, 5, 2, 1, 1, 2, 3]
def baseStart_669792 : Nat := 118140960795 + 669792 * 2 ^ 59
def prefixEnd_669792 : Nat := 4983230072969 + 3 ^ 40 * 669792 * 2
def baseEnd_669792 : Nat := 343925234536348669419689

theorem tailTrace_669792 : CollatzResearch.WordTrace tailWord_669792 prefixEnd_669792 343925234536348669419689 := by
  unfold tailWord_669792
  simp only [CollatzResearch.WordTrace]
  refine ⟨12214660594732725105773815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16286214126310300141031753 12214660594732725105773815)
  ·
    refine ⟨18321990892099087658660723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12214660594732725105773815 18321990892099087658660723)
    ·
      refine ⟨27482986338148631487991085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18321990892099087658660723 27482986338148631487991085)
      ·
        refine ⟨10306119876805736807996657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27482986338148631487991085 10306119876805736807996657)
        ·
          refine ⟨7729589907604302605997493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10306119876805736807996657 7729589907604302605997493)
          ·
            refine ⟨724649053837903369312265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7729589907604302605997493 724649053837903369312265)
            ·
              refine ⟨543486790378427526984199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 724649053837903369312265 543486790378427526984199)
              ·
                refine ⟨815230185567641290476299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 543486790378427526984199 815230185567641290476299)
                ·
                  refine ⟨1222845278351461935714449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 815230185567641290476299 1222845278351461935714449)
                  ·
                    refine ⟨917133958763596451785837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1222845278351461935714449 917133958763596451785837)
                    ·
                      refine ⟨343925234536348669419689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 917133958763596451785837 343925234536348669419689)
                      ·
                        rfl

theorem cell23_669792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 1, 2, 3].length) (baseStart_669792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669792 prefixEnd_669792 := by exact prefixLift 669792
  have htrace : WordTrace (prefixWord ++ tailWord_669792) baseStart_669792 baseEnd_669792 := by
    simpa [prefixWord, tailWord_669792, baseEnd_669792] using wordTrace_append hprefix tailTrace_669792
  have hstable : (prefixWord ++ tailWord_669792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669792).length < 2 ^ (prefixWord ++ tailWord_669792).sum := by decide
  have hdescent : baseEnd_669792 < baseStart_669792 := by decide
  rcases family_descends (prefixWord ++ tailWord_669792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669805 : List Nat := [1, 5, 1, 1, 2, 1, 3, 1, 4, 1, 3]
def baseStart_669805 : Nat := 118140960795 + 669805 * 2 ^ 59
def prefixEnd_669805 : Nat := 4983230072969 + 3 ^ 40 * 669805 * 2
def baseEnd_669805 : Nat := 343931909784857118557129

theorem tailTrace_669805 : CollatzResearch.WordTrace tailWord_669805 prefixEnd_669805 343931909784857118557129 := by
  unfold tailWord_669805
  simp only [CollatzResearch.WordTrace]
  refine ⟨24429795338418353431770869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16286530225612235621180579 24429795338418353431770869)
  ·
    refine ⟨2290293312976720634228519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24429795338418353431770869 2290293312976720634228519)
    ·
      refine ⟨3435439969465080951342779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2290293312976720634228519 3435439969465080951342779)
      ·
        refine ⟨5153159954197621427014169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3435439969465080951342779 5153159954197621427014169)
        ·
          refine ⟨3864869965648216070260627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5153159954197621427014169 3864869965648216070260627)
          ·
            refine ⟨5797304948472324105390941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3864869965648216070260627 5797304948472324105390941)
            ·
              refine ⟨2173989355677121539521603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5797304948472324105390941 2173989355677121539521603)
              ·
                refine ⟨3260984033515682309282405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2173989355677121539521603 3260984033515682309282405)
                ·
                  refine ⟨611434506284190432990451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3260984033515682309282405 611434506284190432990451)
                  ·
                    refine ⟨917151759426285649485677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 611434506284190432990451 917151759426285649485677)
                    ·
                      refine ⟨343931909784857118557129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 917151759426285649485677 343931909784857118557129)
                      ·
                        rfl

theorem cell23_669805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_669805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669805 prefixEnd_669805 := by exact prefixLift 669805
  have htrace : WordTrace (prefixWord ++ tailWord_669805) baseStart_669805 baseEnd_669805 := by
    simpa [prefixWord, tailWord_669805, baseEnd_669805] using wordTrace_append hprefix tailTrace_669805
  have hstable : (prefixWord ++ tailWord_669805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669805).length < 2 ^ (prefixWord ++ tailWord_669805).sum := by decide
  have hdescent : baseEnd_669805 < baseStart_669805 := by decide
  rcases family_descends (prefixWord ++ tailWord_669805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669832 : List Nat := [2, 1, 3, 4, 1, 1, 1, 4, 1, 3, 2]
def baseStart_669832 : Nat := 118140960795 + 669832 * 2 ^ 59
def prefixEnd_669832 : Nat := 4983230072969 + 3 ^ 40 * 669832 * 2
def baseEnd_669832 : Nat := 343945773762528512919505

theorem tailTrace_669832 : CollatzResearch.WordTrace tailWord_669832 prefixEnd_669832 343945773762528512919505 := by
  unfold tailWord_669832
  simp only [CollatzResearch.WordTrace]
  refine ⟨12215390054660268521501875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16287186739547024695335833 12215390054660268521501875)
  ·
    refine ⟨18323085081990402782252813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12215390054660268521501875 18323085081990402782252813)
    ·
      refine ⟨6871156905746401043344805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18323085081990402782252813 6871156905746401043344805)
      ·
        refine ⟨1288341919827450195627151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6871156905746401043344805 1288341919827450195627151)
        ·
          refine ⟨1932512879741175293440727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1288341919827450195627151 1932512879741175293440727)
          ·
            refine ⟨2898769319611762940161091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1932512879741175293440727 2898769319611762940161091)
            ·
              refine ⟨4348153979417644410241637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2898769319611762940161091 4348153979417644410241637)
              ·
                refine ⟨815278871140808326920307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4348153979417644410241637 815278871140808326920307)
                ·
                  refine ⟨1222918306711212490380461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 815278871140808326920307 1222918306711212490380461)
                  ·
                    refine ⟨458594365016704683892673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1222918306711212490380461 458594365016704683892673)
                    ·
                      refine ⟨343945773762528512919505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 458594365016704683892673 343945773762528512919505)
                      ·
                        rfl

theorem cell23_669832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_669832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669832 prefixEnd_669832 := by exact prefixLift 669832
  have htrace : WordTrace (prefixWord ++ tailWord_669832) baseStart_669832 baseEnd_669832 := by
    simpa [prefixWord, tailWord_669832, baseEnd_669832] using wordTrace_append hprefix tailTrace_669832
  have hstable : (prefixWord ++ tailWord_669832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669832).length < 2 ^ (prefixWord ++ tailWord_669832).sum := by decide
  have hdescent : baseEnd_669832 < baseStart_669832 := by decide
  rcases family_descends (prefixWord ++ tailWord_669832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669845 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 6, 2, 2]
def baseStart_669845 : Nat := 118140960795 + 669845 * 2 ^ 59
def prefixEnd_669845 : Nat := 4983230072969 + 3 ^ 40 * 669845 * 2
def baseEnd_669845 : Nat := 343952449011036962056945

theorem tailTrace_669845 : CollatzResearch.WordTrace tailWord_669845 prefixEnd_669845 343952449011036962056945 := by
  unfold tailWord_669845
  simp only [CollatzResearch.WordTrace]
  refine ⟨24431254258273440263226989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16287502838848960175484659 24431254258273440263226989)
  ·
    refine ⟨9161720346852540098710121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24431254258273440263226989 9161720346852540098710121)
    ·
      refine ⟨6871290260139405074032591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9161720346852540098710121 6871290260139405074032591)
      ·
        refine ⟨10306935390209107611048887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6871290260139405074032591 10306935390209107611048887)
        ·
          refine ⟨15460403085313661416573331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10306935390209107611048887 15460403085313661416573331)
          ·
            refine ⟨23190604627970492124859997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15460403085313661416573331 23190604627970492124859997)
            ·
              refine ⟨8696476735488934546822499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23190604627970492124859997 8696476735488934546822499)
              ·
                refine ⟨13044715103233401820233749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8696476735488934546822499 13044715103233401820233749)
                ·
                  refine ⟨611471020464065710323457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 13044715103233401820233749 611471020464065710323457)
                  ·
                    refine ⟨458603265348049282742593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 611471020464065710323457 458603265348049282742593)
                    ·
                      refine ⟨343952449011036962056945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 458603265348049282742593 343952449011036962056945)
                      ·
                        rfl

theorem cell23_669845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 6, 2, 2].length) (baseStart_669845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669845 prefixEnd_669845 := by exact prefixLift 669845
  have htrace : WordTrace (prefixWord ++ tailWord_669845) baseStart_669845 baseEnd_669845 := by
    simpa [prefixWord, tailWord_669845, baseEnd_669845] using wordTrace_append hprefix tailTrace_669845
  have hstable : (prefixWord ++ tailWord_669845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669845).length < 2 ^ (prefixWord ++ tailWord_669845).sum := by decide
  have hdescent : baseEnd_669845 < baseStart_669845 := by decide
  rcases family_descends (prefixWord ++ tailWord_669845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669846 : List Nat := [5, 3, 2, 1, 2, 1, 9]
def baseStart_669846 : Nat := 118140960795 + 669846 * 2 ^ 59
def prefixEnd_669846 : Nat := 4983230072969 + 3 ^ 40 * 669846 * 2
def baseEnd_669846 : Nat := 4246332870267795779561

theorem tailTrace_669846 : CollatzResearch.WordTrace tailWord_669846 prefixEnd_669846 4246332870267795779561 := by
  unfold tailWord_669846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1526955670704363589625837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16287527154179878289342261 1526955670704363589625837)
  ·
    refine ⟨572608376514136346109689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1526955670704363589625837 572608376514136346109689)
    ·
      refine ⟨429456282385602259582267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 572608376514136346109689 429456282385602259582267)
      ·
        refine ⟨644184423578403389373401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 429456282385602259582267 644184423578403389373401)
        ·
          refine ⟨483138317683802542030051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 644184423578403389373401 483138317683802542030051)
          ·
            refine ⟨724707476525703813045077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 483138317683802542030051 724707476525703813045077)
            ·
              refine ⟨4246332870267795779561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 724707476525703813045077 4246332870267795779561)
              ·
                rfl

theorem cell23_669846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 9].length) (baseStart_669846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669846 prefixEnd_669846 := by exact prefixLift 669846
  have htrace : WordTrace (prefixWord ++ tailWord_669846) baseStart_669846 baseEnd_669846 := by
    simpa [prefixWord, tailWord_669846, baseEnd_669846] using wordTrace_append hprefix tailTrace_669846
  have hstable : (prefixWord ++ tailWord_669846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669846).length < 2 ^ (prefixWord ++ tailWord_669846).sum := by decide
  have hdescent : baseEnd_669846 < baseStart_669846 := by decide
  rcases family_descends (prefixWord ++ tailWord_669846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669861 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 1, 2, 7]
def baseStart_669861 : Nat := 118140960795 + 669861 * 2 ^ 59
def prefixEnd_669861 : Nat := 4983230072969 + 3 ^ 40 * 669861 * 2
def baseEnd_669861 : Nat := 343960664701508899456871

theorem tailTrace_669861 : CollatzResearch.WordTrace tailWord_669861 prefixEnd_669861 343960664701508899456871 := by
  unfold tailWord_669861
  simp only [CollatzResearch.WordTrace]
  refine ⟨24431837826215474995809437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16287891884143649997206291 24431837826215474995809437)
  ·
    refine ⟨9161939184830803123428539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24431837826215474995809437 9161939184830803123428539)
    ·
      refine ⟨13742908777246204685142809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9161939184830803123428539 13742908777246204685142809)
      ·
        refine ⟨10307181582934653513857107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13742908777246204685142809 10307181582934653513857107)
        ·
          refine ⟨15460772374401980270785661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10307181582934653513857107 15460772374401980270785661)
          ·
            refine ⟨5797789640400742601544623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15460772374401980270785661 5797789640400742601544623)
            ·
              refine ⟨8696684460601113902316935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5797789640400742601544623 8696684460601113902316935)
              ·
                refine ⟨13045026690901670853475403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8696684460601113902316935 13045026690901670853475403)
                ·
                  refine ⟨19567540036352506280213105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13045026690901670853475403 19567540036352506280213105)
                  ·
                    refine ⟨14675655027264379710159829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19567540036352506280213105 14675655027264379710159829)
                    ·
                      refine ⟨343960664701508899456871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 14675655027264379710159829 343960664701508899456871)
                      ·
                        rfl

theorem cell23_669861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_669861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669861 prefixEnd_669861 := by exact prefixLift 669861
  have htrace : WordTrace (prefixWord ++ tailWord_669861) baseStart_669861 baseEnd_669861 := by
    simpa [prefixWord, tailWord_669861, baseEnd_669861] using wordTrace_append hprefix tailTrace_669861
  have hstable : (prefixWord ++ tailWord_669861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669861).length < 2 ^ (prefixWord ++ tailWord_669861).sum := by decide
  have hdescent : baseEnd_669861 < baseStart_669861 := by decide
  rcases family_descends (prefixWord ++ tailWord_669861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669879 : List Nat := [1, 1, 3, 1, 4, 2, 4, 1, 2, 2, 2]
def baseStart_669879 : Nat := 118140960795 + 669879 * 2 ^ 59
def prefixEnd_669879 : Nat := 4983230072969 + 3 ^ 40 * 669879 * 2
def baseEnd_669879 : Nat := 343969907353289829031789

theorem tailTrace_669879 : CollatzResearch.WordTrace tailWord_669879 prefixEnd_669879 343969907353289829031789 := by
  unfold tailWord_669879
  simp only [CollatzResearch.WordTrace]
  refine ⟨24432494340150264069964691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16288329560100176046643127 24432494340150264069964691)
  ·
    refine ⟨36648741510225396104947037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24432494340150264069964691 36648741510225396104947037)
    ·
      refine ⟨13743278066334523539355139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36648741510225396104947037 13743278066334523539355139)
      ·
        refine ⟨20614917099501785309032709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13743278066334523539355139 20614917099501785309032709)
        ·
          refine ⟨3865296956156584745443633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20614917099501785309032709 3865296956156584745443633)
          ·
            refine ⟨2898972717117438559082725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3865296956156584745443633 2898972717117438559082725)
            ·
              refine ⟨543557384459519729828011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2898972717117438559082725 543557384459519729828011)
              ·
                refine ⟨815336076689279594742017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 543557384459519729828011 815336076689279594742017)
                ·
                  refine ⟨611502057516959696056513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 815336076689279594742017 611502057516959696056513)
                  ·
                    refine ⟨458626543137719772042385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 611502057516959696056513 458626543137719772042385)
                    ·
                      refine ⟨343969907353289829031789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 458626543137719772042385 343969907353289829031789)
                      ·
                        rfl

theorem cell23_669879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 2, 2, 2].length) (baseStart_669879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669879 prefixEnd_669879 := by exact prefixLift 669879
  have htrace : WordTrace (prefixWord ++ tailWord_669879) baseStart_669879 baseEnd_669879 := by
    simpa [prefixWord, tailWord_669879, baseEnd_669879] using wordTrace_append hprefix tailTrace_669879
  have hstable : (prefixWord ++ tailWord_669879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669879).length < 2 ^ (prefixWord ++ tailWord_669879).sum := by decide
  have hdescent : baseEnd_669879 < baseStart_669879 := by decide
  rcases family_descends (prefixWord ++ tailWord_669879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669935 : List Nat := [1, 1, 2, 1, 6, 1, 1, 1, 1, 6, 2]
def baseStart_669935 : Nat := 118140960795 + 669935 * 2 ^ 59
def prefixEnd_669935 : Nat := 4983230072969 + 3 ^ 40 * 669935 * 2
def baseEnd_669935 : Nat := 343998662269941609931531

theorem tailTrace_669935 : CollatzResearch.WordTrace tailWord_669935 prefixEnd_669935 343998662269941609931531 := by
  unfold tailWord_669935
  simp only [CollatzResearch.WordTrace]
  refine ⟨24434536827947385634003259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16289691218631590422668839 24434536827947385634003259)
  ·
    refine ⟨36651805241921078451004889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24434536827947385634003259 36651805241921078451004889)
    ·
      refine ⟨27488853931440808838253667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36651805241921078451004889 27488853931440808838253667)
      ·
        refine ⟨41233280897161213257380501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27488853931440808838253667 41233280897161213257380501)
        ·
          refine ⟨1932810042054431871439711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41233280897161213257380501 1932810042054431871439711)
          ·
            refine ⟨2899215063081647807159567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1932810042054431871439711 2899215063081647807159567)
            ·
              refine ⟨4348822594622471710739351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2899215063081647807159567 4348822594622471710739351)
              ·
                refine ⟨6523233891933707566109027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4348822594622471710739351 6523233891933707566109027)
                ·
                  refine ⟨9784850837900561349163541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6523233891933707566109027 9784850837900561349163541)
                  ·
                    refine ⟨458664883026588813242041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9784850837900561349163541 458664883026588813242041)
                    ·
                      refine ⟨343998662269941609931531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 458664883026588813242041 343998662269941609931531)
                      ·
                        rfl

theorem cell23_669935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 6, 2].length) (baseStart_669935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669935 prefixEnd_669935 := by exact prefixLift 669935
  have htrace : WordTrace (prefixWord ++ tailWord_669935) baseStart_669935 baseEnd_669935 := by
    simpa [prefixWord, tailWord_669935, baseEnd_669935] using wordTrace_append hprefix tailTrace_669935
  have hstable : (prefixWord ++ tailWord_669935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669935).length < 2 ^ (prefixWord ++ tailWord_669935).sum := by decide
  have hdescent : baseEnd_669935 < baseStart_669935 := by decide
  rcases family_descends (prefixWord ++ tailWord_669935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669962 : List Nat := [3, 1, 2, 2, 1, 1, 3, 5, 1, 4]
def baseStart_669962 : Nat := 118140960795 + 669962 * 2 ^ 59
def prefixEnd_669962 : Nat := 4983230072969 + 3 ^ 40 * 669962 * 2
def baseEnd_669962 : Nat := 114670842082537668097969

theorem tailTrace_669962 : CollatzResearch.WordTrace tailWord_669962 prefixEnd_669962 114670842082537668097969 := by
  unfold tailWord_669962
  simp only [CollatzResearch.WordTrace]
  refine ⟨6108880399712392311309035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16290347732566379496824093 6108880399712392311309035)
  ·
    refine ⟨9163320599568588466963553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6108880399712392311309035 9163320599568588466963553)
    ·
      refine ⟨6872490449676441350222665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9163320599568588466963553 6872490449676441350222665)
      ·
        refine ⟨5154367837257331012666999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6872490449676441350222665 5154367837257331012666999)
        ·
          refine ⟨7731551755885996519000499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5154367837257331012666999 7731551755885996519000499)
          ·
            refine ⟨11597327633828994778500749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7731551755885996519000499 11597327633828994778500749)
            ·
              refine ⟨4348997862685873041937781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11597327633828994778500749 4348997862685873041937781)
              ·
                refine ⟨407718549626800597681667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4348997862685873041937781 407718549626800597681667)
                ·
                  refine ⟨611577824440200896522501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 407718549626800597681667 611577824440200896522501)
                  ·
                    refine ⟨114670842082537668097969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 611577824440200896522501 114670842082537668097969)
                    ·
                      rfl

theorem cell23_669962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 5, 1, 4].length) (baseStart_669962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669962 prefixEnd_669962 := by exact prefixLift 669962
  have htrace : WordTrace (prefixWord ++ tailWord_669962) baseStart_669962 baseEnd_669962 := by
    simpa [prefixWord, tailWord_669962, baseEnd_669962] using wordTrace_append hprefix tailTrace_669962
  have hstable : (prefixWord ++ tailWord_669962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669962).length < 2 ^ (prefixWord ++ tailWord_669962).sum := by decide
  have hdescent : baseEnd_669962 < baseStart_669962 := by decide
  rcases family_descends (prefixWord ++ tailWord_669962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669975 : List Nat := [1, 1, 3, 4, 1, 2, 3, 2, 6]
def baseStart_669975 : Nat := 118140960795 + 669975 * 2 ^ 59
def prefixEnd_669975 : Nat := 4983230072969 + 3 ^ 40 * 669975 * 2
def baseEnd_669975 : Nat := 38224355721791272603483

theorem tailTrace_669975 : CollatzResearch.WordTrace tailWord_669975 prefixEnd_669975 38224355721791272603483 := by
  unfold tailWord_669975
  simp only [CollatzResearch.WordTrace]
  refine ⟨24435995747802472465459379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16290663831868314976972919 24435995747802472465459379)
  ·
    refine ⟨36653993621703708698189069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24435995747802472465459379 36653993621703708698189069)
    ·
      refine ⟨13745247608138890761820901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36653993621703708698189069 13745247608138890761820901)
      ·
        refine ⟨2577233926526042017841419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13745247608138890761820901 2577233926526042017841419)
        ·
          refine ⟨3865850889789063026762129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2577233926526042017841419 3865850889789063026762129)
          ·
            refine ⟨2899388167341797270071597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3865850889789063026762129 2899388167341797270071597)
            ·
              refine ⟨1087270562753173976276849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2899388167341797270071597 1087270562753173976276849)
              ·
                refine ⟨815452922064880482207637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1087270562753173976276849 815452922064880482207637)
                ·
                  refine ⟨38224355721791272603483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 815452922064880482207637 38224355721791272603483)
                  ·
                    rfl

theorem cell23_669975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 6].length) (baseStart_669975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_669975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_669975 prefixEnd_669975 := by exact prefixLift 669975
  have htrace : WordTrace (prefixWord ++ tailWord_669975) baseStart_669975 baseEnd_669975 := by
    simpa [prefixWord, tailWord_669975, baseEnd_669975] using wordTrace_append hprefix tailTrace_669975
  have hstable : (prefixWord ++ tailWord_669975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669975).length < 2 ^ (prefixWord ++ tailWord_669975).sum := by decide
  have hdescent : baseEnd_669975 < baseStart_669975 := by decide
  rcases family_descends (prefixWord ++ tailWord_669975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670012 : List Nat := [2, 2, 2, 2, 1, 2, 2, 3, 2, 3, 2]
def baseStart_670012 : Nat := 118140960795 + 670012 * 2 ^ 59
def prefixEnd_670012 : Nat := 4983230072969 + 3 ^ 40 * 670012 * 2
def baseEnd_670012 : Nat := 344038200280337808668677

theorem tailTrace_670012 : CollatzResearch.WordTrace tailWord_670012 prefixEnd_670012 344038200280337808668677 := by
  unfold tailWord_670012
  simp only [CollatzResearch.WordTrace]
  refine ⟨12218672624334213892278145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16291563499112285189704193 12218672624334213892278145)
  ·
    refine ⟨9164004468250660419208609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12218672624334213892278145 9164004468250660419208609)
    ·
      refine ⟨6873003351187995314406457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9164004468250660419208609 6873003351187995314406457)
      ·
        refine ⟨5154752513390996485804843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6873003351187995314406457 5154752513390996485804843)
        ·
          refine ⟨7732128770086494728707265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5154752513390996485804843 7732128770086494728707265)
          ·
            refine ⟨5799096577564871046530449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7732128770086494728707265 5799096577564871046530449)
            ·
              refine ⟨4349322433173653284897837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5799096577564871046530449 4349322433173653284897837)
              ·
                refine ⟨1630995912440119981836689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4349322433173653284897837 1630995912440119981836689)
                ·
                  refine ⟨1223246934330089986377517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1630995912440119981836689 1223246934330089986377517)
                  ·
                    refine ⟨458717600373783744891569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1223246934330089986377517 458717600373783744891569)
                    ·
                      refine ⟨344038200280337808668677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 458717600373783744891569 344038200280337808668677)
                      ·
                        rfl

theorem cell23_670012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_670012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670012 prefixEnd_670012 := by exact prefixLift 670012
  have htrace : WordTrace (prefixWord ++ tailWord_670012) baseStart_670012 baseEnd_670012 := by
    simpa [prefixWord, tailWord_670012, baseEnd_670012] using wordTrace_append hprefix tailTrace_670012
  have hstable : (prefixWord ++ tailWord_670012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670012).length < 2 ^ (prefixWord ++ tailWord_670012).sum := by decide
  have hdescent : baseEnd_670012 < baseStart_670012 := by decide
  rcases family_descends (prefixWord ++ tailWord_670012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670019 : List Nat := [1, 1, 1, 3, 1, 3, 5, 3, 1, 1, 3]
def baseStart_670019 : Nat := 118140960795 + 670019 * 2 ^ 59
def prefixEnd_670019 : Nat := 4983230072969 + 3 ^ 40 * 670019 * 2
def baseEnd_670019 : Nat := 344041794644919281281145

theorem tailTrace_670019 : CollatzResearch.WordTrace tailWord_670019 prefixEnd_670019 344041794644919281281145 := by
  unfold tailWord_670019
  simp only [CollatzResearch.WordTrace]
  refine ⟨24437600559643067980061111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16291733706428711986707407 24437600559643067980061111)
  ·
    refine ⟨36656400839464601970091667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24437600559643067980061111 36656400839464601970091667)
    ·
      refine ⟨54984601259196902955137501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36656400839464601970091667 54984601259196902955137501)
      ·
        refine ⟨20619225472198838608176563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54984601259196902955137501 20619225472198838608176563)
        ·
          refine ⟨30928838208298257912264845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20619225472198838608176563 30928838208298257912264845)
          ·
            refine ⟨11598314328111846717099317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30928838208298257912264845 11598314328111846717099317)
            ·
              refine ⟨1087341968260485629728061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11598314328111846717099317 1087341968260485629728061)
              ·
                refine ⟨407753238097682111148023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1087341968260485629728061 407753238097682111148023)
                ·
                  refine ⟨611629857146523166722035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 407753238097682111148023 611629857146523166722035)
                  ·
                    refine ⟨917444785719784750083053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 611629857146523166722035 917444785719784750083053)
                    ·
                      refine ⟨344041794644919281281145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 917444785719784750083053 344041794644919281281145)
                      ·
                        rfl

theorem cell23_670019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 3, 1, 1, 3].length) (baseStart_670019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670019 prefixEnd_670019 := by exact prefixLift 670019
  have htrace : WordTrace (prefixWord ++ tailWord_670019) baseStart_670019 baseEnd_670019 := by
    simpa [prefixWord, tailWord_670019, baseEnd_670019] using wordTrace_append hprefix tailTrace_670019
  have hstable : (prefixWord ++ tailWord_670019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670019).length < 2 ^ (prefixWord ++ tailWord_670019).sum := by decide
  have hdescent : baseEnd_670019 < baseStart_670019 := by decide
  rcases family_descends (prefixWord ++ tailWord_670019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670052 : List Nat := [2, 3, 1, 1, 3, 1, 3, 3, 2, 4]
def baseStart_670052 : Nat := 118140960795 + 670052 * 2 ^ 59
def prefixEnd_670052 : Nat := 4983230072969 + 3 ^ 40 * 670052 * 2
def baseEnd_670052 : Nat := 114686246502172550722831

theorem tailTrace_670052 : CollatzResearch.WordTrace tailWord_670052 prefixEnd_670052 114686246502172550722831 := by
  unfold tailWord_670052
  simp only [CollatzResearch.WordTrace]
  refine ⟨12219402084261757308006205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16292536112349009744008273 12219402084261757308006205)
  ·
    refine ⟨4582275781598158990502327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12219402084261757308006205 4582275781598158990502327)
    ·
      refine ⟨6873413672397238485753491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4582275781598158990502327 6873413672397238485753491)
      ·
        refine ⟨10310120508595857728630237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6873413672397238485753491 10310120508595857728630237)
        ·
          refine ⟨3866295190723446648236339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10310120508595857728630237 3866295190723446648236339)
          ·
            refine ⟨5799442786085169972354509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3866295190723446648236339 5799442786085169972354509)
            ·
              refine ⟨2174791044781938739632941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5799442786085169972354509 2174791044781938739632941)
              ·
                refine ⟨815546641793227027362353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2174791044781938739632941 815546641793227027362353)
                ·
                  refine ⟨611659981344920270521765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 815546641793227027362353 611659981344920270521765)
                  ·
                    refine ⟨114686246502172550722831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 611659981344920270521765 114686246502172550722831)
                    ·
                      rfl

theorem cell23_670052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_670052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670052 prefixEnd_670052 := by exact prefixLift 670052
  have htrace : WordTrace (prefixWord ++ tailWord_670052) baseStart_670052 baseEnd_670052 := by
    simpa [prefixWord, tailWord_670052, baseEnd_670052] using wordTrace_append hprefix tailTrace_670052
  have hstable : (prefixWord ++ tailWord_670052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670052).length < 2 ^ (prefixWord ++ tailWord_670052).sum := by decide
  have hdescent : baseEnd_670052 < baseStart_670052 := by decide
  rcases family_descends (prefixWord ++ tailWord_670052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670055 : List Nat := [1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 6]
def baseStart_670055 : Nat := 118140960795 + 670055 * 2 ^ 59
def prefixEnd_670055 : Nat := 4983230072969 + 3 ^ 40 * 670055 * 2
def baseEnd_670055 : Nat := 344060279948481140430979

theorem tailTrace_670055 : CollatzResearch.WordTrace tailWord_670055 prefixEnd_670055 344060279948481140430979 := by
  unfold tailWord_670055
  simp only [CollatzResearch.WordTrace]
  refine ⟨24438913587512646128371619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16292609058341764085581079 24438913587512646128371619)
  ·
    refine ⟨36658370381268969192557429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24438913587512646128371619 36658370381268969192557429)
    ·
      refine ⟨3436722223243965861802259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36658370381268969192557429 3436722223243965861802259)
      ·
        refine ⟨5155083334865948792703389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3436722223243965861802259 5155083334865948792703389)
        ·
          refine ⟨1933156250574730797263771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5155083334865948792703389 1933156250574730797263771)
          ·
            refine ⟨2899734375862096195895657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1933156250574730797263771 2899734375862096195895657)
            ·
              refine ⟨2174800781896572146921743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2899734375862096195895657 2174800781896572146921743)
              ·
                refine ⟨3262201172844858220382615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2174800781896572146921743 3262201172844858220382615)
                ·
                  refine ⟨4893301759267287330573923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3262201172844858220382615 4893301759267287330573923)
                  ·
                    refine ⟨7339952638900930995860885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4893301759267287330573923 7339952638900930995860885)
                    ·
                      refine ⟨344060279948481140430979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7339952638900930995860885 344060279948481140430979)
                      ·
                        rfl

theorem cell23_670055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_670055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670055 prefixEnd_670055 := by exact prefixLift 670055
  have htrace : WordTrace (prefixWord ++ tailWord_670055) baseStart_670055 baseEnd_670055 := by
    simpa [prefixWord, tailWord_670055, baseEnd_670055] using wordTrace_append hprefix tailTrace_670055
  have hstable : (prefixWord ++ tailWord_670055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670055).length < 2 ^ (prefixWord ++ tailWord_670055).sum := by decide
  have hdescent : baseEnd_670055 < baseStart_670055 := by decide
  rcases family_descends (prefixWord ++ tailWord_670055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670075 : List Nat := [1, 1, 1, 1, 1, 7, 1, 1, 3, 3, 3]
def baseStart_670075 : Nat := 118140960795 + 670075 * 2 ^ 59
def prefixEnd_670075 : Nat := 4983230072969 + 3 ^ 40 * 670075 * 2
def baseEnd_670075 : Nat := 344070549561571062180887

theorem tailTrace_670075 : CollatzResearch.WordTrace tailWord_670075 prefixEnd_670075 344070549561571062180887 := by
  unfold tailWord_670075
  simp only [CollatzResearch.WordTrace]
  refine ⟨24439643047440189544099679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16293095364960126362733119 24439643047440189544099679)
  ·
    refine ⟨36659464571160284316149519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24439643047440189544099679 36659464571160284316149519)
    ·
      refine ⟨54989196856740426474224279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36659464571160284316149519 54989196856740426474224279)
      ·
        refine ⟨82483795285110639711336419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54989196856740426474224279 82483795285110639711336419)
        ·
          refine ⟨123725692927665959567004629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82483795285110639711336419 123725692927665959567004629)
          ·
            refine ⟨2899820927992170927351671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 123725692927665959567004629 2899820927992170927351671)
            ·
              refine ⟨4349731391988256391027507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2899820927992170927351671 4349731391988256391027507)
              ·
                refine ⟨6524597087982384586541261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4349731391988256391027507 6524597087982384586541261)
                ·
                  refine ⟨2446723907993394219952973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6524597087982384586541261 2446723907993394219952973)
                  ·
                    refine ⟨917521465497522832482365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2446723907993394219952973 917521465497522832482365)
                    ·
                      refine ⟨344070549561571062180887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 917521465497522832482365 344070549561571062180887)
                      ·
                        rfl

theorem cell23_670075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 3, 3].length) (baseStart_670075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670075 prefixEnd_670075 := by exact prefixLift 670075
  have htrace : WordTrace (prefixWord ++ tailWord_670075) baseStart_670075 baseEnd_670075 := by
    simpa [prefixWord, tailWord_670075, baseEnd_670075] using wordTrace_append hprefix tailTrace_670075
  have hstable : (prefixWord ++ tailWord_670075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670075).length < 2 ^ (prefixWord ++ tailWord_670075).sum := by decide
  have hdescent : baseEnd_670075 < baseStart_670075 := by decide
  rcases family_descends (prefixWord ++ tailWord_670075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670082 : List Nat := [3, 4, 2, 1, 2, 11]
def baseStart_670082 : Nat := 118140960795 + 670082 * 2 ^ 59
def prefixEnd_670082 : Nat := 4983230072969 + 3 ^ 40 * 670082 * 2
def baseEnd_670082 : Nat := 1415942979119969278985

theorem tailTrace_670082 : CollatzResearch.WordTrace tailWord_670082 prefixEnd_670082 1415942979119969278985 := by
  unfold tailWord_670082
  simp only [CollatzResearch.WordTrace]
  refine ⟨6109974589603707434901125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16293265572276553159736333 6109974589603707434901125)
  ·
    refine ⟨1145620235550695144043961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6109974589603707434901125 1145620235550695144043961)
    ·
      refine ⟨859215176663021358032971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1145620235550695144043961 859215176663021358032971)
      ·
        refine ⟨1288822764994532037049457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 859215176663021358032971 1288822764994532037049457)
        ·
          refine ⟨966617073745899027787093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1288822764994532037049457 966617073745899027787093)
          ·
            refine ⟨1415942979119969278985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 966617073745899027787093 1415942979119969278985)
            ·
              rfl

theorem cell23_670082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 11].length) (baseStart_670082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670082 prefixEnd_670082 := by exact prefixLift 670082
  have htrace : WordTrace (prefixWord ++ tailWord_670082) baseStart_670082 baseEnd_670082 := by
    simpa [prefixWord, tailWord_670082, baseEnd_670082] using wordTrace_append hprefix tailTrace_670082
  have hstable : (prefixWord ++ tailWord_670082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670082).length < 2 ^ (prefixWord ++ tailWord_670082).sum := by decide
  have hdescent : baseEnd_670082 < baseStart_670082 := by decide
  rcases family_descends (prefixWord ++ tailWord_670082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670109 : List Nat := [1, 4, 2, 1, 4, 1, 2, 1, 1, 3, 3]
def baseStart_670109 : Nat := 118140960795 + 670109 * 2 ^ 59
def prefixEnd_670109 : Nat := 4983230072969 + 3 ^ 40 * 670109 * 2
def baseEnd_670109 : Nat := 344088007903823929155731

theorem tailTrace_670109 : CollatzResearch.WordTrace tailWord_670109 prefixEnd_670109 344088007903823929155731 := by
  unfold tailWord_670109
  simp only [CollatzResearch.WordTrace]
  refine ⟨24440883129317013350837381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16293922086211342233891587 24440883129317013350837381)
  ·
    refine ⟨4582665586746940003282009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24440883129317013350837381 4582665586746940003282009)
    ·
      refine ⟨3436999190060205002461507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4582665586746940003282009 3436999190060205002461507)
      ·
        refine ⟨5155498785090307503692261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3436999190060205002461507 5155498785090307503692261)
        ·
          refine ⟨966656022204432656942299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5155498785090307503692261 966656022204432656942299)
          ·
            refine ⟨1449984033306648985413449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 966656022204432656942299 1449984033306648985413449)
            ·
              refine ⟨1087488024979986739060087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1449984033306648985413449 1087488024979986739060087)
              ·
                refine ⟨1631232037469980108590131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1087488024979986739060087 1631232037469980108590131)
                ·
                  refine ⟨2446848056204970162885197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1631232037469980108590131 2446848056204970162885197)
                  ·
                    refine ⟨917568021076863811081949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2446848056204970162885197 917568021076863811081949)
                    ·
                      refine ⟨344088007903823929155731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 917568021076863811081949 344088007903823929155731)
                      ·
                        rfl

theorem cell23_670109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_670109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670109 prefixEnd_670109 := by exact prefixLift 670109
  have htrace : WordTrace (prefixWord ++ tailWord_670109) baseStart_670109 baseEnd_670109 := by
    simpa [prefixWord, tailWord_670109, baseEnd_670109] using wordTrace_append hprefix tailTrace_670109
  have hstable : (prefixWord ++ tailWord_670109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670109).length < 2 ^ (prefixWord ++ tailWord_670109).sum := by decide
  have hdescent : baseEnd_670109 < baseStart_670109 := by decide
  rcases family_descends (prefixWord ++ tailWord_670109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670119 : List Nat := [1, 1, 6, 1, 1, 2, 2, 1, 3, 3, 2]
def baseStart_670119 : Nat := 118140960795 + 670119 * 2 ^ 59
def prefixEnd_670119 : Nat := 4983230072969 + 3 ^ 40 * 670119 * 2
def baseEnd_670119 : Nat := 344093142710368890030685

theorem tailTrace_670119 : CollatzResearch.WordTrace tailWord_670119 prefixEnd_670119 344093142710368890030685 := by
  unfold tailWord_670119
  simp only [CollatzResearch.WordTrace]
  refine ⟨24441247859280785058701411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16294165239520523372467607 24441247859280785058701411)
  ·
    refine ⟨36661871788921177588052117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24441247859280785058701411 36661871788921177588052117)
    ·
      refine ⟨1718525240105680199439943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 36661871788921177588052117 1718525240105680199439943)
      ·
        refine ⟨2577787860158520299159915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1718525240105680199439943 2577787860158520299159915)
        ·
          refine ⟨3866681790237780448739873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2577787860158520299159915 3866681790237780448739873)
          ·
            refine ⟨2900011342678335336554905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3866681790237780448739873 2900011342678335336554905)
            ·
              refine ⟨2175008507008751502416179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2900011342678335336554905 2175008507008751502416179)
              ·
                refine ⟨3262512760513127253624269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2175008507008751502416179 3262512760513127253624269)
                ·
                  refine ⟨1223442285192422720109101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3262512760513127253624269 1223442285192422720109101)
                  ·
                    refine ⟨458790856947158520040913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1223442285192422720109101 458790856947158520040913)
                    ·
                      refine ⟨344093142710368890030685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 458790856947158520040913 344093142710368890030685)
                      ·
                        rfl

theorem cell23_670119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_670119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670119 prefixEnd_670119 := by exact prefixLift 670119
  have htrace : WordTrace (prefixWord ++ tailWord_670119) baseStart_670119 baseEnd_670119 := by
    simpa [prefixWord, tailWord_670119, baseEnd_670119] using wordTrace_append hprefix tailTrace_670119
  have hstable : (prefixWord ++ tailWord_670119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670119).length < 2 ^ (prefixWord ++ tailWord_670119).sum := by decide
  have hdescent : baseEnd_670119 < baseStart_670119 := by decide
  rcases family_descends (prefixWord ++ tailWord_670119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670195 : List Nat := [1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 5]
def baseStart_670195 : Nat := 118140960795 + 670195 * 2 ^ 59
def prefixEnd_670195 : Nat := 4983230072969 + 3 ^ 40 * 670195 * 2
def baseEnd_670195 : Nat := 344132167240110592680335

theorem tailTrace_670195 : CollatzResearch.WordTrace tailWord_670195 prefixEnd_670195 344132167240110592680335 := by
  unfold tailWord_670195
  simp only [CollatzResearch.WordTrace]
  refine ⟨24444019807005450038468039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16296013204670300025645359 24444019807005450038468039)
  ·
    refine ⟨36666029710508175057702059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24444019807005450038468039 36666029710508175057702059)
    ·
      refine ⟨54999044565762262586553089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36666029710508175057702059 54999044565762262586553089)
      ·
        refine ⟨41249283424321696939914817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54999044565762262586553089 41249283424321696939914817)
        ·
          refine ⟨30936962568241272704936113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41249283424321696939914817 30936962568241272704936113)
          ·
            refine ⟨23202721926180954528702085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30936962568241272704936113 23202721926180954528702085)
            ·
              refine ⟨4350510361158928974131641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23202721926180954528702085 4350510361158928974131641)
              ·
                refine ⟨3262882770869196730598731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4350510361158928974131641 3262882770869196730598731)
                ·
                  refine ⟨4894324156303795095898097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3262882770869196730598731 4894324156303795095898097)
                  ·
                    refine ⟨3670743117227846321923573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4894324156303795095898097 3670743117227846321923573)
                    ·
                      refine ⟨344132167240110592680335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3670743117227846321923573 344132167240110592680335)
                      ·
                        rfl

theorem cell23_670195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 5].length) (baseStart_670195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670195 prefixEnd_670195 := by exact prefixLift 670195
  have htrace : WordTrace (prefixWord ++ tailWord_670195) baseStart_670195 baseEnd_670195 := by
    simpa [prefixWord, tailWord_670195, baseEnd_670195] using wordTrace_append hprefix tailTrace_670195
  have hstable : (prefixWord ++ tailWord_670195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670195).length < 2 ^ (prefixWord ++ tailWord_670195).sum := by decide
  have hdescent : baseEnd_670195 < baseStart_670195 := by decide
  rcases family_descends (prefixWord ++ tailWord_670195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670212 : List Nat := [2, 3, 2, 3, 1, 1, 1, 1, 1, 1, 7]
def baseStart_670212 : Nat := 118140960795 + 670212 * 2 ^ 59
def prefixEnd_670212 : Nat := 4983230072969 + 3 ^ 40 * 670212 * 2
def baseEnd_670212 : Nat := 344140896411237026167757

theorem tailTrace_670212 : CollatzResearch.WordTrace tailWord_670212 prefixEnd_670212 344140896411237026167757 := by
  unfold tailWord_670212
  simp only [CollatzResearch.WordTrace]
  refine ⟨12222319923971930970918445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16296426565295907961224593 12222319923971930970918445)
  ·
    refine ⟨4583369971489474114094417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12222319923971930970918445 4583369971489474114094417)
    ·
      refine ⟨3437527478617105585570813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4583369971489474114094417 3437527478617105585570813)
      ·
        refine ⟨1289072804481414594589055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3437527478617105585570813 1289072804481414594589055)
        ·
          refine ⟨1933609206722121891883583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1289072804481414594589055 1933609206722121891883583)
          ·
            refine ⟨2900413810083182837825375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1933609206722121891883583 2900413810083182837825375)
            ·
              refine ⟨4350620715124774256738063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2900413810083182837825375 4350620715124774256738063)
              ·
                refine ⟨6525931072687161385107095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4350620715124774256738063 6525931072687161385107095)
                ·
                  refine ⟨9788896609030742077660643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6525931072687161385107095 9788896609030742077660643)
                  ·
                    refine ⟨14683344913546113116490965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9788896609030742077660643 14683344913546113116490965)
                    ·
                      refine ⟨344140896411237026167757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 14683344913546113116490965 344140896411237026167757)
                      ·
                        rfl

theorem cell23_670212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_670212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670212 prefixEnd_670212 := by exact prefixLift 670212
  have htrace : WordTrace (prefixWord ++ tailWord_670212) baseStart_670212 baseEnd_670212 := by
    simpa [prefixWord, tailWord_670212, baseEnd_670212] using wordTrace_append hprefix tailTrace_670212
  have hstable : (prefixWord ++ tailWord_670212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670212).length < 2 ^ (prefixWord ++ tailWord_670212).sum := by decide
  have hdescent : baseEnd_670212 < baseStart_670212 := by decide
  rcases family_descends (prefixWord ++ tailWord_670212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670245 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 10]
def baseStart_670245 : Nat := 118140960795 + 670245 * 2 ^ 59
def prefixEnd_670245 : Nat := 4983230072969 + 3 ^ 40 * 670245 * 2
def baseEnd_670245 : Nat := 38239760141426155228345

theorem tailTrace_670245 : CollatzResearch.WordTrace tailWord_670245 prefixEnd_670245 38239760141426155228345 := by
  unfold tailWord_670245
  simp only [CollatzResearch.WordTrace]
  refine ⟨24445843456824308577788189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16297228971216205718525459 24445843456824308577788189)
  ·
    refine ⟨9167191296309115716670571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24445843456824308577788189 9167191296309115716670571)
    ·
      refine ⟨13750786944463673575005857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9167191296309115716670571 13750786944463673575005857)
      ·
        refine ⟨10313090208347755181254393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13750786944463673575005857 10313090208347755181254393)
        ·
          refine ⟨7734817656260816385940795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10313090208347755181254393 7734817656260816385940795)
          ·
            refine ⟨11602226484391224578911193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7734817656260816385940795 11602226484391224578911193)
            ·
              refine ⟨8701669863293418434183395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11602226484391224578911193 8701669863293418434183395)
              ·
                refine ⟨13052504794940127651275093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8701669863293418434183395 13052504794940127651275093)
                ·
                  refine ⟨38239760141426155228345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 13052504794940127651275093 38239760141426155228345)
                  ·
                    rfl

theorem cell23_670245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 10].length) (baseStart_670245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670245 prefixEnd_670245 := by exact prefixLift 670245
  have htrace : WordTrace (prefixWord ++ tailWord_670245) baseStart_670245 baseEnd_670245 := by
    simpa [prefixWord, tailWord_670245, baseEnd_670245] using wordTrace_append hprefix tailTrace_670245
  have hstable : (prefixWord ++ tailWord_670245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670245).length < 2 ^ (prefixWord ++ tailWord_670245).sum := by decide
  have hdescent : baseEnd_670245 < baseStart_670245 := by decide
  rcases family_descends (prefixWord ++ tailWord_670245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670266 : List Nat := [3, 1, 1, 1, 3, 4, 1, 4, 1, 4]
def baseStart_670266 : Nat := 118140960795 + 670266 * 2 ^ 59
def prefixEnd_670266 : Nat := 4983230072969 + 3 ^ 40 * 670266 * 2
def baseEnd_670266 : Nat := 114722874788859938297503

theorem tailTrace_670266 : CollatzResearch.WordTrace tailWord_670266 prefixEnd_670266 114722874788859938297503 := by
  unfold tailWord_670266
  simp only [CollatzResearch.WordTrace]
  refine ⟨6111652347437057291075663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16297739593165486109535101 6111652347437057291075663)
  ·
    refine ⟨9167478521155585936613495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6111652347437057291075663 9167478521155585936613495)
    ·
      refine ⟨13751217781733378904920243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9167478521155585936613495 13751217781733378904920243)
      ·
        refine ⟨20626826672600068357380365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13751217781733378904920243 20626826672600068357380365)
        ·
          refine ⟨7735060002225025634017637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20626826672600068357380365 7735060002225025634017637)
          ·
            refine ⟨1450323750417192306378307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7735060002225025634017637 1450323750417192306378307)
            ·
              refine ⟨2175485625625788459567461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1450323750417192306378307 2175485625625788459567461)
              ·
                refine ⟨407903554804835336168899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2175485625625788459567461 407903554804835336168899)
                ·
                  refine ⟨611855332207253004253349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 407903554804835336168899 611855332207253004253349)
                  ·
                    refine ⟨114722874788859938297503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 611855332207253004253349 114722874788859938297503)
                    ·
                      rfl

theorem cell23_670266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 4, 1, 4].length) (baseStart_670266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670266 prefixEnd_670266 := by exact prefixLift 670266
  have htrace : WordTrace (prefixWord ++ tailWord_670266) baseStart_670266 baseEnd_670266 := by
    simpa [prefixWord, tailWord_670266, baseEnd_670266] using wordTrace_append hprefix tailTrace_670266
  have hstable : (prefixWord ++ tailWord_670266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670266).length < 2 ^ (prefixWord ++ tailWord_670266).sum := by decide
  have hdescent : baseEnd_670266 < baseStart_670266 := by decide
  rcases family_descends (prefixWord ++ tailWord_670266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670289 : List Nat := [1, 2, 2, 1, 3, 3, 1, 1, 5, 1, 3]
def baseStart_670289 : Nat := 118140960795 + 670289 * 2 ^ 59
def prefixEnd_670289 : Nat := 4983230072969 + 3 ^ 40 * 670289 * 2
def baseEnd_670289 : Nat := 344180434421633224904903

theorem tailTrace_670289 : CollatzResearch.WordTrace tailWord_670289 prefixEnd_670289 344180434421633224904903 := by
  unfold tailWord_670289
  simp only [CollatzResearch.WordTrace]
  refine ⟨24447448268664904092389921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16298298845776602728259947 24447448268664904092389921)
  ·
    refine ⟨18335586201498678069292441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24447448268664904092389921 18335586201498678069292441)
    ·
      refine ⟨13751689651124008551969331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18335586201498678069292441 13751689651124008551969331)
      ·
        refine ⟨20627534476686012827953997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13751689651124008551969331 20627534476686012827953997)
        ·
          refine ⟨7735325428757254810482749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20627534476686012827953997 7735325428757254810482749)
          ·
            refine ⟨2900747035783970553931031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7735325428757254810482749 2900747035783970553931031)
            ·
              refine ⟨4351120553675955830896547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2900747035783970553931031 4351120553675955830896547)
              ·
                refine ⟨6526680830513933746344821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4351120553675955830896547 6526680830513933746344821)
                ·
                  refine ⟨611876327860681288719827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6526680830513933746344821 611876327860681288719827)
                  ·
                    refine ⟨917814491791021933079741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 611876327860681288719827 917814491791021933079741)
                    ·
                      refine ⟨344180434421633224904903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 917814491791021933079741 344180434421633224904903)
                      ·
                        rfl

theorem cell23_670289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 5, 1, 3].length) (baseStart_670289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670289 prefixEnd_670289 := by exact prefixLift 670289
  have htrace : WordTrace (prefixWord ++ tailWord_670289) baseStart_670289 baseEnd_670289 := by
    simpa [prefixWord, tailWord_670289, baseEnd_670289] using wordTrace_append hprefix tailTrace_670289
  have hstable : (prefixWord ++ tailWord_670289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670289).length < 2 ^ (prefixWord ++ tailWord_670289).sum := by decide
  have hdescent : baseEnd_670289 < baseStart_670289 := by decide
  rcases family_descends (prefixWord ++ tailWord_670289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670332 : List Nat := [2, 2, 2, 1, 1, 2, 3, 1, 3, 1, 5]
def baseStart_670332 : Nat := 118140960795 + 670332 * 2 ^ 59
def prefixEnd_670332 : Nat := 4983230072969 + 3 ^ 40 * 670332 * 2
def baseEnd_670332 : Nat := 344202514089776556667205

theorem tailTrace_670332 : CollatzResearch.WordTrace tailWord_670332 prefixEnd_670332 344202514089776556667205 := by
  unfold tailWord_670332
  simp only [CollatzResearch.WordTrace]
  refine ⟨12224508303754561218102625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16299344405006081624136833 12224508303754561218102625)
  ·
    refine ⟨9168381227815920913576969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12224508303754561218102625 9168381227815920913576969)
    ·
      refine ⟨6876285920861940685182727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9168381227815920913576969 6876285920861940685182727)
      ·
        refine ⟨10314428881292911027774091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6876285920861940685182727 10314428881292911027774091)
        ·
          refine ⟨15471643321939366541661137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10314428881292911027774091 15471643321939366541661137)
          ·
            refine ⟨11603732491454524906245853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15471643321939366541661137 11603732491454524906245853)
            ·
              refine ⟨4351399684295446839842195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11603732491454524906245853 4351399684295446839842195)
              ·
                refine ⟨6527099526443170259763293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4351399684295446839842195 6527099526443170259763293)
                ·
                  refine ⟨2447662322416188847411235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6527099526443170259763293 2447662322416188847411235)
                  ·
                    refine ⟨3671493483624283271116853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2447662322416188847411235 3671493483624283271116853)
                    ·
                      refine ⟨344202514089776556667205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3671493483624283271116853 344202514089776556667205)
                      ·
                        rfl

theorem cell23_670332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_670332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670332 prefixEnd_670332 := by exact prefixLift 670332
  have htrace : WordTrace (prefixWord ++ tailWord_670332) baseStart_670332 baseEnd_670332 := by
    simpa [prefixWord, tailWord_670332, baseEnd_670332] using wordTrace_append hprefix tailTrace_670332
  have hstable : (prefixWord ++ tailWord_670332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670332).length < 2 ^ (prefixWord ++ tailWord_670332).sum := by decide
  have hdescent : baseEnd_670332 < baseStart_670332 := by decide
  rcases family_descends (prefixWord ++ tailWord_670332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670339 : List Nat := [1, 1, 1, 3, 3, 1, 2, 5, 2, 4]
def baseStart_670339 : Nat := 118140960795 + 670339 * 2 ^ 59
def prefixEnd_670339 : Nat := 4983230072969 + 3 ^ 40 * 670339 * 2
def baseEnd_670339 : Nat := 114735369484786009759891

theorem tailTrace_670339 : CollatzResearch.WordTrace tailWord_670339 prefixEnd_670339 114735369484786009759891 := by
  unfold tailWord_670339
  simp only [CollatzResearch.WordTrace]
  refine ⟨24449271918483762631710071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16299514612322508421140047 24449271918483762631710071)
  ·
    refine ⟨36673907877725643947565107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24449271918483762631710071 36673907877725643947565107)
    ·
      refine ⟨55010861816588465921347661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36673907877725643947565107 55010861816588465921347661)
      ·
        refine ⟨20629073181220674720505373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55010861816588465921347661 20629073181220674720505373)
        ·
          refine ⟨7735902442957753020189515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20629073181220674720505373 7735902442957753020189515)
          ·
            refine ⟨11603853664436629530284273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7735902442957753020189515 11603853664436629530284273)
            ·
              refine ⟨8702890248327472147713205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11603853664436629530284273 8702890248327472147713205)
              ·
                refine ⟨815895960780700513848113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8702890248327472147713205 815895960780700513848113)
                ·
                  refine ⟨611921970585525385386085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 815895960780700513848113 611921970585525385386085)
                  ·
                    refine ⟨114735369484786009759891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 611921970585525385386085 114735369484786009759891)
                    ·
                      rfl

theorem cell23_670339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 2, 4].length) (baseStart_670339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670339 prefixEnd_670339 := by exact prefixLift 670339
  have htrace : WordTrace (prefixWord ++ tailWord_670339) baseStart_670339 baseEnd_670339 := by
    simpa [prefixWord, tailWord_670339, baseEnd_670339] using wordTrace_append hprefix tailTrace_670339
  have hstable : (prefixWord ++ tailWord_670339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670339).length < 2 ^ (prefixWord ++ tailWord_670339).sum := by decide
  have hdescent : baseEnd_670339 < baseStart_670339 := by decide
  rcases family_descends (prefixWord ++ tailWord_670339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670356 : List Nat := [2, 4, 2, 2, 1, 1, 1, 2, 4, 4]
def baseStart_670356 : Nat := 118140960795 + 670356 * 2 ^ 59
def prefixEnd_670356 : Nat := 4983230072969 + 3 ^ 40 * 670356 * 2
def baseEnd_670356 : Nat := 114738279208494820922365

theorem tailTrace_670356 : CollatzResearch.WordTrace tailWord_670356 prefixEnd_670356 114738279208494820922365 := by
  unfold tailWord_670356
  simp only [CollatzResearch.WordTrace]
  refine ⟨12224945979711087267539461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16299927972948116356719281 12224945979711087267539461)
  ·
    refine ⟨2292177371195828862663649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12224945979711087267539461 2292177371195828862663649)
    ·
      refine ⟨1719133028396871646997737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2292177371195828862663649 1719133028396871646997737)
      ·
        refine ⟨1289349771297653735248303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1719133028396871646997737 1289349771297653735248303)
        ·
          refine ⟨1934024656946480602872455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1289349771297653735248303 1934024656946480602872455)
          ·
            refine ⟨2901036985419720904308683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1934024656946480602872455 2901036985419720904308683)
            ·
              refine ⟨4351555478129581356463025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2901036985419720904308683 4351555478129581356463025)
              ·
                refine ⟨3263666608597186017347269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4351555478129581356463025 3263666608597186017347269)
                ·
                  refine ⟨611937489111972378252613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3263666608597186017347269 611937489111972378252613)
                  ·
                    refine ⟨114738279208494820922365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 611937489111972378252613 114738279208494820922365)
                    ·
                      rfl

theorem cell23_670356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_670356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670356 prefixEnd_670356 := by exact prefixLift 670356
  have htrace : WordTrace (prefixWord ++ tailWord_670356) baseStart_670356 baseEnd_670356 := by
    simpa [prefixWord, tailWord_670356, baseEnd_670356] using wordTrace_append hprefix tailTrace_670356
  have hstable : (prefixWord ++ tailWord_670356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670356).length < 2 ^ (prefixWord ++ tailWord_670356).sum := by decide
  have hdescent : baseEnd_670356 < baseStart_670356 := by decide
  rcases family_descends (prefixWord ++ tailWord_670356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670366 : List Nat := [4, 3, 1, 1, 1, 1, 4, 1, 1, 1, 5]
def baseStart_670366 : Nat := 118140960795 + 670366 * 2 ^ 59
def prefixEnd_670366 : Nat := 4983230072969 + 3 ^ 40 * 670366 * 2
def baseEnd_670366 : Nat := 344219972432029423642049

theorem tailTrace_670366 : CollatzResearch.WordTrace tailWord_670366 prefixEnd_670366 344219972432029423642049 := by
  unfold tailWord_670366
  simp only [CollatzResearch.WordTrace]
  refine ⟨3056282086173243280367869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16300171126257297495295301 3056282086173243280367869)
  ·
    refine ⟨1146105782314966230137951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3056282086173243280367869 1146105782314966230137951)
    ·
      refine ⟨1719158673472449345206927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1146105782314966230137951 1719158673472449345206927)
      ·
        refine ⟨2578738010208674017810391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1719158673472449345206927 2578738010208674017810391)
        ·
          refine ⟨3868107015313011026715587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2578738010208674017810391 3868107015313011026715587)
          ·
            refine ⟨5802160522969516540073381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3868107015313011026715587 5802160522969516540073381)
            ·
              refine ⟨1087905098056784351263759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5802160522969516540073381 1087905098056784351263759)
              ·
                refine ⟨1631857647085176526895639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1087905098056784351263759 1631857647085176526895639)
                ·
                  refine ⟨2447786470627764790343459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1631857647085176526895639 2447786470627764790343459)
                  ·
                    refine ⟨3671679705941647185515189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2447786470627764790343459 3671679705941647185515189)
                    ·
                      refine ⟨344219972432029423642049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3671679705941647185515189 344219972432029423642049)
                      ·
                        rfl

theorem cell23_670366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_670366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670366 prefixEnd_670366 := by exact prefixLift 670366
  have htrace : WordTrace (prefixWord ++ tailWord_670366) baseStart_670366 baseEnd_670366 := by
    simpa [prefixWord, tailWord_670366, baseEnd_670366] using wordTrace_append hprefix tailTrace_670366
  have hstable : (prefixWord ++ tailWord_670366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670366).length < 2 ^ (prefixWord ++ tailWord_670366).sum := by decide
  have hdescent : baseEnd_670366 < baseStart_670366 := by decide
  rcases family_descends (prefixWord ++ tailWord_670366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670369 : List Nat := [1, 2, 3, 3, 3, 2, 9]
def baseStart_670369 : Nat := 118140960795 + 670369 * 2 ^ 59
def prefixEnd_670369 : Nat := 4983230072969 + 3 ^ 40 * 670369 * 2
def baseEnd_670369 : Nat := 4249648307086332245735

theorem tailTrace_670369 : CollatzResearch.WordTrace tailWord_670369 prefixEnd_670369 4249648307086332245735 := by
  unfold tailWord_670369
  simp only [CollatzResearch.WordTrace]
  refine ⟨24450366108375077755302161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16300244072250051836868107 24450366108375077755302161)
  ·
    refine ⟨18337774581281308316476621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24450366108375077755302161 18337774581281308316476621)
    ·
      refine ⟨6876665467980490618678733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18337774581281308316476621 6876665467980490618678733)
      ·
        refine ⟨2578749550492683982004525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6876665467980490618678733 2578749550492683982004525)
        ·
          refine ⟨967031081434756493251697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2578749550492683982004525 967031081434756493251697)
          ·
            refine ⟨725273311076067369938773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 967031081434756493251697 725273311076067369938773)
            ·
              refine ⟨4249648307086332245735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 725273311076067369938773 4249648307086332245735)
              ·
                rfl

theorem cell23_670369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 9].length) (baseStart_670369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670369 prefixEnd_670369 := by exact prefixLift 670369
  have htrace : WordTrace (prefixWord ++ tailWord_670369) baseStart_670369 baseEnd_670369 := by
    simpa [prefixWord, tailWord_670369, baseEnd_670369] using wordTrace_append hprefix tailTrace_670369
  have hstable : (prefixWord ++ tailWord_670369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670369).length < 2 ^ (prefixWord ++ tailWord_670369).sum := by decide
  have hdescent : baseEnd_670369 < baseStart_670369 := by decide
  rcases family_descends (prefixWord ++ tailWord_670369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670390 : List Nat := [5, 1, 3, 1, 2, 1, 1, 3, 2, 4]
def baseStart_670390 : Nat := 118140960795 + 670390 * 2 ^ 59
def prefixEnd_670390 : Nat := 4983230072969 + 3 ^ 40 * 670390 * 2
def baseEnd_670390 : Nat := 114744098655912443247313

theorem tailTrace_670390 : CollatzResearch.WordTrace tailWord_670390 prefixEnd_670390 114744098655912443247313 := by
  unfold tailWord_670390
  simp only [CollatzResearch.WordTrace]
  refine ⟨1528195752581187396363539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16300754694199332227877749 1528195752581187396363539)
  ·
    refine ⟨2292293628871781094545309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1528195752581187396363539 2292293628871781094545309)
    ·
      refine ⟨859610110826917910454491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2292293628871781094545309 859610110826917910454491)
      ·
        refine ⟨1289415166240376865681737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 859610110826917910454491 1289415166240376865681737)
        ·
          refine ⟨967061374680282649261303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1289415166240376865681737 967061374680282649261303)
          ·
            refine ⟨1450592062020423973891955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 967061374680282649261303 1450592062020423973891955)
            ·
              refine ⟨2175888093030635960837933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1450592062020423973891955 2175888093030635960837933)
              ·
                refine ⟨815958034886488485314225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2175888093030635960837933 815958034886488485314225)
                ·
                  refine ⟨611968526164866363985669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 815958034886488485314225 611968526164866363985669)
                  ·
                    refine ⟨114744098655912443247313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 611968526164866363985669 114744098655912443247313)
                    ·
                      rfl

theorem cell23_670390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_670390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670390 prefixEnd_670390 := by exact prefixLift 670390
  have htrace : WordTrace (prefixWord ++ tailWord_670390) baseStart_670390 baseEnd_670390 := by
    simpa [prefixWord, tailWord_670390, baseEnd_670390] using wordTrace_append hprefix tailTrace_670390
  have hstable : (prefixWord ++ tailWord_670390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670390).length < 2 ^ (prefixWord ++ tailWord_670390).sum := by decide
  have hdescent : baseEnd_670390 < baseStart_670390 := by decide
  rcases family_descends (prefixWord ++ tailWord_670390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670432 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 6]
def baseStart_670432 : Nat := 118140960795 + 670432 * 2 ^ 59
def prefixEnd_670432 : Nat := 4983230072969 + 3 ^ 40 * 670432 * 2
def baseEnd_670432 : Nat := 344253862155226165416745

theorem tailTrace_670432 : CollatzResearch.WordTrace tailWord_670432 prefixEnd_670432 344253862155226165416745 := by
  unfold tailWord_670432
  simp only [CollatzResearch.WordTrace]
  refine ⟨12226331953573419757422775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16301775938097893009897033 12226331953573419757422775)
  ·
    refine ⟨18339497930360129636134163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12226331953573419757422775 18339497930360129636134163)
    ·
      refine ⟨27509246895540194454201245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18339497930360129636134163 27509246895540194454201245)
      ·
        refine ⟨10315967585827572920325467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27509246895540194454201245 10315967585827572920325467)
        ·
          refine ⟨15473951378741359380488201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10315967585827572920325467 15473951378741359380488201)
          ·
            refine ⟨11605463534056019535366151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15473951378741359380488201 11605463534056019535366151)
            ·
              refine ⟨17408195301084029303049227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11605463534056019535366151 17408195301084029303049227)
              ·
                refine ⟨26112292951626043954573841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17408195301084029303049227 26112292951626043954573841)
                ·
                  refine ⟨19584219713719532965930381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26112292951626043954573841 19584219713719532965930381)
                  ·
                    refine ⟨7344082392644824862223893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19584219713719532965930381 7344082392644824862223893)
                    ·
                      refine ⟨344253862155226165416745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7344082392644824862223893 344253862155226165416745)
                      ·
                        rfl

theorem cell23_670432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_670432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670432 prefixEnd_670432 := by exact prefixLift 670432
  have htrace : WordTrace (prefixWord ++ tailWord_670432) baseStart_670432 baseEnd_670432 := by
    simpa [prefixWord, tailWord_670432, baseEnd_670432] using wordTrace_append hprefix tailTrace_670432
  have hstable : (prefixWord ++ tailWord_670432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670432).length < 2 ^ (prefixWord ++ tailWord_670432).sum := by decide
  have hdescent : baseEnd_670432 < baseStart_670432 := by decide
  rcases family_descends (prefixWord ++ tailWord_670432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670449 : List Nat := [1, 2, 2, 2, 2, 2, 3, 1, 2, 2, 4]
def baseStart_670449 : Nat := 118140960795 + 670449 * 2 ^ 59
def prefixEnd_670449 : Nat := 4983230072969 + 3 ^ 40 * 670449 * 2
def baseEnd_670449 : Nat := 344262591326352598904167

theorem tailTrace_670449 : CollatzResearch.WordTrace tailWord_670449 prefixEnd_670449 344262591326352598904167 := by
  unfold tailWord_670449
  simp only [CollatzResearch.WordTrace]
  refine ⟨24453283948085251418214401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16302189298723500945476267 24453283948085251418214401)
  ·
    refine ⟨18339962961063938563660801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24453283948085251418214401 18339962961063938563660801)
    ·
      refine ⟨13754972220797953922745601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18339962961063938563660801 13754972220797953922745601)
      ·
        refine ⟨10316229165598465442059201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13754972220797953922745601 10316229165598465442059201)
        ·
          refine ⟨7737171874198849081544401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10316229165598465442059201 7737171874198849081544401)
          ·
            refine ⟨5802878905649136811158301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7737171874198849081544401 5802878905649136811158301)
            ·
              refine ⟨2176079589618426304184363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5802878905649136811158301 2176079589618426304184363)
              ·
                refine ⟨3264119384427639456276545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2176079589618426304184363 3264119384427639456276545)
                ·
                  refine ⟨2448089538320729592207409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3264119384427639456276545 2448089538320729592207409)
                  ·
                    refine ⟨1836067153740547194155557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2448089538320729592207409 1836067153740547194155557)
                    ·
                      refine ⟨344262591326352598904167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1836067153740547194155557 344262591326352598904167)
                      ·
                        rfl

theorem cell23_670449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_670449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670449 prefixEnd_670449 := by exact prefixLift 670449
  have htrace : WordTrace (prefixWord ++ tailWord_670449) baseStart_670449 baseEnd_670449 := by
    simpa [prefixWord, tailWord_670449, baseEnd_670449] using wordTrace_append hprefix tailTrace_670449
  have hstable : (prefixWord ++ tailWord_670449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670449).length < 2 ^ (prefixWord ++ tailWord_670449).sum := by decide
  have hdescent : baseEnd_670449 < baseStart_670449 := by decide
  rcases family_descends (prefixWord ++ tailWord_670449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670487 : List Nat := [1, 1, 3, 4, 3, 2, 1, 2, 2, 2, 2]
def baseStart_670487 : Nat := 118140960795 + 670487 * 2 ^ 59
def prefixEnd_670487 : Nat := 4983230072969 + 3 ^ 40 * 670487 * 2
def baseEnd_670487 : Nat := 344282103591223450228993

theorem tailTrace_670487 : CollatzResearch.WordTrace tailWord_670487 prefixEnd_670487 344282103591223450228993 := by
  unfold tailWord_670487
  simp only [CollatzResearch.WordTrace]
  refine ⟨24454669921947583908097715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16303113281298389272065143 24454669921947583908097715)
  ·
    refine ⟨36682004882921375862146573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24454669921947583908097715 36682004882921375862146573)
    ·
      refine ⟨13755751831095515948304965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36682004882921375862146573 13755751831095515948304965)
      ·
        refine ⟨2579203468330409240307181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13755751831095515948304965 2579203468330409240307181)
        ·
          refine ⟨967201300623903465115193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2579203468330409240307181 967201300623903465115193)
          ·
            refine ⟨725400975467927598836395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 967201300623903465115193 725400975467927598836395)
            ·
              refine ⟨1088101463201891398254593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 725400975467927598836395 1088101463201891398254593)
              ·
                refine ⟨816076097401418548690945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1088101463201891398254593 816076097401418548690945)
                ·
                  refine ⟨612057073051063911518209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 816076097401418548690945 612057073051063911518209)
                  ·
                    refine ⟨459042804788297933638657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 612057073051063911518209 459042804788297933638657)
                    ·
                      refine ⟨344282103591223450228993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 459042804788297933638657 344282103591223450228993)
                      ·
                        rfl

theorem cell23_670487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_670487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670487 prefixEnd_670487 := by exact prefixLift 670487
  have htrace : WordTrace (prefixWord ++ tailWord_670487) baseStart_670487 baseEnd_670487 := by
    simpa [prefixWord, tailWord_670487, baseEnd_670487] using wordTrace_append hprefix tailTrace_670487
  have hstable : (prefixWord ++ tailWord_670487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670487).length < 2 ^ (prefixWord ++ tailWord_670487).sum := by decide
  have hdescent : baseEnd_670487 < baseStart_670487 := by decide
  rcases family_descends (prefixWord ++ tailWord_670487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670493 : List Nat := [1, 4, 2, 4, 1, 1, 2, 1, 7]
def baseStart_670493 : Nat := 118140960795 + 670493 * 2 ^ 59
def prefixEnd_670493 : Nat := 4983230072969 + 3 ^ 40 * 670493 * 2
def baseEnd_670493 : Nat := 38253909386127825194885

theorem tailTrace_670493 : CollatzResearch.WordTrace tailWord_670493 prefixEnd_670493 38253909386127825194885 := by
  unfold tailWord_670493
  simp only [CollatzResearch.WordTrace]
  refine ⟨24454888759925846932816133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16303259173283897955210755 24454888759925846932816133)
  ·
    refine ⟨4585291642486096299903025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24454888759925846932816133 4585291642486096299903025)
    ·
      refine ⟨3438968731864572224927269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4585291642486096299903025 3438968731864572224927269)
      ·
        refine ⟨644806637224607292173863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3438968731864572224927269 644806637224607292173863)
        ·
          refine ⟨967209955836910938260795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 644806637224607292173863 967209955836910938260795)
          ·
            refine ⟨1450814933755366407391193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 967209955836910938260795 1450814933755366407391193)
            ·
              refine ⟨1088111200316524805543395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1450814933755366407391193 1088111200316524805543395)
              ·
                refine ⟨1632166800474787208315093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1088111200316524805543395 1632166800474787208315093)
                ·
                  refine ⟨38253909386127825194885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1632166800474787208315093 38253909386127825194885)
                  ·
                    rfl

theorem cell23_670493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 7].length) (baseStart_670493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670493 prefixEnd_670493 := by exact prefixLift 670493
  have htrace : WordTrace (prefixWord ++ tailWord_670493) baseStart_670493 baseEnd_670493 := by
    simpa [prefixWord, tailWord_670493, baseEnd_670493] using wordTrace_append hprefix tailTrace_670493
  have hstable : (prefixWord ++ tailWord_670493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670493).length < 2 ^ (prefixWord ++ tailWord_670493).sum := by decide
  have hdescent : baseEnd_670493 < baseStart_670493 := by decide
  rcases family_descends (prefixWord ++ tailWord_670493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670549 : List Nat := [1, 3, 2, 2, 2, 1, 1, 3, 8]
def baseStart_670549 : Nat := 118140960795 + 670549 * 2 ^ 59
def prefixEnd_670549 : Nat := 4983230072969 + 3 ^ 40 * 670549 * 2
def baseEnd_670549 : Nat := 38257104376866911961523

theorem tailTrace_670549 : CollatzResearch.WordTrace tailWord_670549 prefixEnd_670549 38257104376866911961523 := by
  unfold tailWord_670549
  simp only [CollatzResearch.WordTrace]
  refine ⟨24456931247722968496854701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16304620831815312331236467 24456931247722968496854701)
  ·
    refine ⟨9171349217896113186320513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24456931247722968496854701 9171349217896113186320513)
    ·
      refine ⟨6878511913422084889740385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9171349217896113186320513 6878511913422084889740385)
      ·
        refine ⟨5158883935066563667305289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6878511913422084889740385 5158883935066563667305289)
        ·
          refine ⟨3869162951299922750478967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5158883935066563667305289 3869162951299922750478967)
          ·
            refine ⟨5803744426949884125718451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3869162951299922750478967 5803744426949884125718451)
            ·
              refine ⟨8705616640424826188577677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5803744426949884125718451 8705616640424826188577677)
              ·
                refine ⟨3264606240159309820716629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8705616640424826188577677 3264606240159309820716629)
                ·
                  refine ⟨38257104376866911961523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3264606240159309820716629 38257104376866911961523)
                  ·
                    rfl

theorem cell23_670549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 8].length) (baseStart_670549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670549 prefixEnd_670549 := by exact prefixLift 670549
  have htrace : WordTrace (prefixWord ++ tailWord_670549) baseStart_670549 baseEnd_670549 := by
    simpa [prefixWord, tailWord_670549, baseEnd_670549] using wordTrace_append hprefix tailTrace_670549
  have hstable : (prefixWord ++ tailWord_670549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670549).length < 2 ^ (prefixWord ++ tailWord_670549).sum := by decide
  have hdescent : baseEnd_670549 < baseStart_670549 := by decide
  rcases family_descends (prefixWord ++ tailWord_670549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670553 : List Nat := [1, 2, 1, 2, 2, 6, 1, 1, 3, 4]
def baseStart_670553 : Nat := 118140960795 + 670553 * 2 ^ 59
def prefixEnd_670553 : Nat := 4983230072969 + 3 ^ 40 * 670553 * 2
def baseEnd_670553 : Nat := 114771997771473397334563

theorem tailTrace_670553 : CollatzResearch.WordTrace tailWord_670553 prefixEnd_670553 114771997771473397334563 := by
  unfold tailWord_670553
  simp only [CollatzResearch.WordTrace]
  refine ⟨24457077139708477180000313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16304718093138984786666875 24457077139708477180000313)
  ·
    refine ⟨18342807854781357885000235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24457077139708477180000313 18342807854781357885000235)
    ·
      refine ⟨27514211782172036827500353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18342807854781357885000235 27514211782172036827500353)
      ·
        refine ⟨20635658836629027620625265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27514211782172036827500353 20635658836629027620625265)
        ·
          refine ⟨15476744127471770715468949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20635658836629027620625265 15476744127471770715468949)
          ·
            refine ⟨725472380975239252287607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15476744127471770715468949 725472380975239252287607)
            ·
              refine ⟨1088208571462858878431411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 725472380975239252287607 1088208571462858878431411)
              ·
                refine ⟨1632312857194288317647117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1088208571462858878431411 1632312857194288317647117)
                ·
                  refine ⟨612117321447858119117669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1632312857194288317647117 612117321447858119117669)
                  ·
                    refine ⟨114771997771473397334563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 612117321447858119117669 114771997771473397334563)
                    ·
                      rfl

theorem cell23_670553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 3, 4].length) (baseStart_670553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670553 prefixEnd_670553 := by exact prefixLift 670553
  have htrace : WordTrace (prefixWord ++ tailWord_670553) baseStart_670553 baseEnd_670553 := by
    simpa [prefixWord, tailWord_670553, baseEnd_670553] using wordTrace_append hprefix tailTrace_670553
  have hstable : (prefixWord ++ tailWord_670553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670553).length < 2 ^ (prefixWord ++ tailWord_670553).sum := by decide
  have hdescent : baseEnd_670553 < baseStart_670553 := by decide
  rcases family_descends (prefixWord ++ tailWord_670553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670603 : List Nat := [1, 1, 1, 1, 4, 2, 4, 2, 2, 3, 2]
def baseStart_670603 : Nat := 118140960795 + 670603 * 2 ^ 59
def prefixEnd_670603 : Nat := 4983230072969 + 3 ^ 40 * 670603 * 2
def baseEnd_670603 : Nat := 344341667347144996378459

theorem tailTrace_670603 : CollatzResearch.WordTrace tailWord_670603 prefixEnd_670603 344341667347144996378459 := by
  unfold tailWord_670603
  simp only [CollatzResearch.WordTrace]
  refine ⟨24458900789527335719320463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16305933859684890479546975 24458900789527335719320463)
  ·
    refine ⟨36688351184291003578980695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24458900789527335719320463 36688351184291003578980695)
    ·
      refine ⟨55032526776436505368471043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36688351184291003578980695 55032526776436505368471043)
      ·
        refine ⟨82548790164654758052706565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55032526776436505368471043 82548790164654758052706565)
        ·
          refine ⟨15477898155872767134882481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82548790164654758052706565 15477898155872767134882481)
          ·
            refine ⟨11608423616904575351161861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15477898155872767134882481 11608423616904575351161861)
            ·
              refine ⟨2176579428169607878342849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11608423616904575351161861 2176579428169607878342849)
              ·
                refine ⟨1632434571127205908757137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2176579428169607878342849 1632434571127205908757137)
                ·
                  refine ⟨1224325928345404431567853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1632434571127205908757137 1224325928345404431567853)
                  ·
                    refine ⟨459122223129526661837945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1224325928345404431567853 459122223129526661837945)
                    ·
                      refine ⟨344341667347144996378459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 459122223129526661837945 344341667347144996378459)
                      ·
                        rfl

theorem cell23_670603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 3, 2].length) (baseStart_670603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670603 prefixEnd_670603 := by exact prefixLift 670603
  have htrace : WordTrace (prefixWord ++ tailWord_670603) baseStart_670603 baseEnd_670603 := by
    simpa [prefixWord, tailWord_670603, baseEnd_670603] using wordTrace_append hprefix tailTrace_670603
  have hstable : (prefixWord ++ tailWord_670603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670603).length < 2 ^ (prefixWord ++ tailWord_670603).sum := by decide
  have hdescent : baseEnd_670603 < baseStart_670603 := by decide
  rcases family_descends (prefixWord ++ tailWord_670603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670609 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 5, 6]
def baseStart_670609 : Nat := 118140960795 + 670609 * 2 ^ 59
def prefixEnd_670609 : Nat := 4983230072969 + 3 ^ 40 * 670609 * 2
def baseEnd_670609 : Nat := 114781582743690657634477

theorem tailTrace_670609 : CollatzResearch.WordTrace tailWord_670609 prefixEnd_670609 114781582743690657634477 := by
  unfold tailWord_670609
  simp only [CollatzResearch.WordTrace]
  refine ⟨24459119627505598744038881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16306079751670399162692587 24459119627505598744038881)
  ·
    refine ⟨18344339720629199058029161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24459119627505598744038881 18344339720629199058029161)
    ·
      refine ⟨13758254790471899293521871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18344339720629199058029161 13758254790471899293521871)
      ·
        refine ⟨20637382185707848940282807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13758254790471899293521871 20637382185707848940282807)
        ·
          refine ⟨30956073278561773410424211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20637382185707848940282807 30956073278561773410424211)
          ·
            refine ⟨46434109917842660115636317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30956073278561773410424211 46434109917842660115636317)
            ·
              refine ⟨17412791219190997543363619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46434109917842660115636317 17412791219190997543363619)
              ·
                refine ⟨26119186828786496315045429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17412791219190997543363619 26119186828786496315045429)
                ·
                  refine ⟨2448673765198734029535509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26119186828786496315045429 2448673765198734029535509)
                  ·
                    refine ⟨114781582743690657634477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2448673765198734029535509 114781582743690657634477)
                    ·
                      rfl

theorem cell23_670609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 6].length) (baseStart_670609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670609 prefixEnd_670609 := by exact prefixLift 670609
  have htrace : WordTrace (prefixWord ++ tailWord_670609) baseStart_670609 baseEnd_670609 := by
    simpa [prefixWord, tailWord_670609, baseEnd_670609] using wordTrace_append hprefix tailTrace_670609
  have hstable : (prefixWord ++ tailWord_670609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670609).length < 2 ^ (prefixWord ++ tailWord_670609).sum := by decide
  have hdescent : baseEnd_670609 < baseStart_670609 := by decide
  rcases family_descends (prefixWord ++ tailWord_670609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670637 : List Nat := [1, 5, 2, 3, 1, 1, 1, 1, 1, 5, 2]
def baseStart_670637 : Nat := 118140960795 + 670637 * 2 ^ 59
def prefixEnd_670637 : Nat := 4983230072969 + 3 ^ 40 * 670637 * 2
def baseEnd_670637 : Nat := 344359125689397863353303

theorem tailTrace_670637 : CollatzResearch.WordTrace tailWord_670637 prefixEnd_670637 344359125689397863353303 := by
  unfold tailWord_670637
  simp only [CollatzResearch.WordTrace]
  refine ⟨24460140871404159526058165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16306760580936106350705443 24460140871404159526058165)
  ·
    refine ⟨2293138206694139955567953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24460140871404159526058165 2293138206694139955567953)
    ·
      refine ⟨1719853655020604966675965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2293138206694139955567953 1719853655020604966675965)
      ·
        refine ⟨644945120632726862503487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1719853655020604966675965 644945120632726862503487)
        ·
          refine ⟨967417680949090293755231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 644945120632726862503487 967417680949090293755231)
          ·
            refine ⟨1451126521423635440632847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 967417680949090293755231 1451126521423635440632847)
            ·
              refine ⟨2176689782135453160949271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1451126521423635440632847 2176689782135453160949271)
              ·
                refine ⟨3265034673203179741423907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2176689782135453160949271 3265034673203179741423907)
                ·
                  refine ⟨4897552009804769612135861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3265034673203179741423907 4897552009804769612135861)
                  ·
                    refine ⟨459145500919197151137737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4897552009804769612135861 459145500919197151137737)
                    ·
                      refine ⟨344359125689397863353303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 459145500919197151137737 344359125689397863353303)
                      ·
                        rfl

theorem cell23_670637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_670637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670637 prefixEnd_670637 := by exact prefixLift 670637
  have htrace : WordTrace (prefixWord ++ tailWord_670637) baseStart_670637 baseEnd_670637 := by
    simpa [prefixWord, tailWord_670637, baseEnd_670637] using wordTrace_append hprefix tailTrace_670637
  have hstable : (prefixWord ++ tailWord_670637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670637).length < 2 ^ (prefixWord ++ tailWord_670637).sum := by decide
  have hdescent : baseEnd_670637 < baseStart_670637 := by decide
  rcases family_descends (prefixWord ++ tailWord_670637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670644 : List Nat := [2, 5, 2, 1, 1, 1, 1, 5, 1, 1, 3]
def baseStart_670644 : Nat := 118140960795 + 670644 * 2 ^ 59
def prefixEnd_670644 : Nat := 4983230072969 + 3 ^ 40 * 670644 * 2
def baseEnd_670644 : Nat := 344362720053979335965771

theorem tailTrace_670644 : CollatzResearch.WordTrace tailWord_670644 prefixEnd_670644 344362720053979335965771 := by
  unfold tailWord_670644
  simp only [CollatzResearch.WordTrace]
  refine ⟨12230198091189399860781493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16306930788252533147708657 12230198091189399860781493)
  ·
    refine ⟨1146581071049006236948265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12230198091189399860781493 1146581071049006236948265)
    ·
      refine ⟨859935803286754677711199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1146581071049006236948265 859935803286754677711199)
      ·
        refine ⟨1289903704930132016566799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 859935803286754677711199 1289903704930132016566799)
        ·
          refine ⟨1934855557395198024850199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1289903704930132016566799 1934855557395198024850199)
          ·
            refine ⟨2902283336092797037275299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1934855557395198024850199 2902283336092797037275299)
            ·
              refine ⟨4353425004139195555912949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2902283336092797037275299 4353425004139195555912949)
              ·
                refine ⟨408133594138049583366839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4353425004139195555912949 408133594138049583366839)
                ·
                  refine ⟨612200391207074375050259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 408133594138049583366839 612200391207074375050259)
                  ·
                    refine ⟨918300586810611562575389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 612200391207074375050259 918300586810611562575389)
                    ·
                      refine ⟨344362720053979335965771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 918300586810611562575389 344362720053979335965771)
                      ·
                        rfl

theorem cell23_670644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_670644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670644 prefixEnd_670644 := by exact prefixLift 670644
  have htrace : WordTrace (prefixWord ++ tailWord_670644) baseStart_670644 baseEnd_670644 := by
    simpa [prefixWord, tailWord_670644, baseEnd_670644] using wordTrace_append hprefix tailTrace_670644
  have hstable : (prefixWord ++ tailWord_670644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670644).length < 2 ^ (prefixWord ++ tailWord_670644).sum := by decide
  have hdescent : baseEnd_670644 < baseStart_670644 := by decide
  rcases family_descends (prefixWord ++ tailWord_670644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670667 : List Nat := [1, 1, 1, 1, 3, 5, 2, 4, 1, 2, 2]
def baseStart_670667 : Nat := 118140960795 + 670667 * 2 ^ 59
def prefixEnd_670667 : Nat := 4983230072969 + 3 ^ 40 * 670667 * 2
def baseEnd_670667 : Nat := 344374530109032745978165

theorem tailTrace_670667 : CollatzResearch.WordTrace tailWord_670667 prefixEnd_670667 344374530109032745978165 := by
  unfold tailWord_670667
  simp only [CollatzResearch.WordTrace]
  refine ⟨24461235061295474649650255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16307490040863649766433503 24461235061295474649650255)
  ·
    refine ⟨36691852591943211974475383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24461235061295474649650255 36691852591943211974475383)
    ·
      refine ⟨55037778887914817961713075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36691852591943211974475383 55037778887914817961713075)
      ·
        refine ⟨82556668331872226942569613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55037778887914817961713075 82556668331872226942569613)
        ·
          refine ⟨30958750624452085103463605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82556668331872226942569613 30958750624452085103463605)
          ·
            refine ⟨2902382871042382978449713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30958750624452085103463605 2902382871042382978449713)
            ·
              refine ⟨2176787153281787233837285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2902382871042382978449713 2176787153281787233837285)
              ·
                refine ⟨408147591240335106344491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2176787153281787233837285 408147591240335106344491)
                ·
                  refine ⟨612221386860502659516737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 408147591240335106344491 612221386860502659516737)
                  ·
                    refine ⟨459166040145376994637553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 612221386860502659516737 459166040145376994637553)
                    ·
                      refine ⟨344374530109032745978165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 459166040145376994637553 344374530109032745978165)
                      ·
                        rfl

theorem cell23_670667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 4, 1, 2, 2].length) (baseStart_670667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670667 prefixEnd_670667 := by exact prefixLift 670667
  have htrace : WordTrace (prefixWord ++ tailWord_670667) baseStart_670667 baseEnd_670667 := by
    simpa [prefixWord, tailWord_670667, baseEnd_670667] using wordTrace_append hprefix tailTrace_670667
  have hstable : (prefixWord ++ tailWord_670667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670667).length < 2 ^ (prefixWord ++ tailWord_670667).sum := by decide
  have hdescent : baseEnd_670667 < baseStart_670667 := by decide
  rcases family_descends (prefixWord ++ tailWord_670667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670677 : List Nat := [1, 3, 2, 3, 3, 1, 3, 1, 2, 4]
def baseStart_670677 : Nat := 118140960795 + 670677 * 2 ^ 59
def prefixEnd_670677 : Nat := 4983230072969 + 3 ^ 40 * 670677 * 2
def baseEnd_670677 : Nat := 114793221638525902284373

theorem tailTrace_670677 : CollatzResearch.WordTrace tailWord_670677 prefixEnd_670677 114793221638525902284373 := by
  unfold tailWord_670677
  simp only [CollatzResearch.WordTrace]
  refine ⟨24461599791259246357514285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16307733194172830905009523 24461599791259246357514285)
  ·
    refine ⟨9173099921722217384067857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24461599791259246357514285 9173099921722217384067857)
    ·
      refine ⟨6879824941291663038050893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9173099921722217384067857 6879824941291663038050893)
      ·
        refine ⟨2579934352984373639269085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6879824941291663038050893 2579934352984373639269085)
        ·
          refine ⟨967475382369140114725907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2579934352984373639269085 967475382369140114725907)
          ·
            refine ⟨1451213073553710172088861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 967475382369140114725907 1451213073553710172088861)
            ·
              refine ⟨544204902582641314533323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1451213073553710172088861 544204902582641314533323)
              ·
                refine ⟨816307353873961971799985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 544204902582641314533323 816307353873961971799985)
                ·
                  refine ⟨612230515405471478849989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 816307353873961971799985 612230515405471478849989)
                  ·
                    refine ⟨114793221638525902284373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 612230515405471478849989 114793221638525902284373)
                    ·
                      rfl

theorem cell23_670677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 2, 4].length) (baseStart_670677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670677 prefixEnd_670677 := by exact prefixLift 670677
  have htrace : WordTrace (prefixWord ++ tailWord_670677) baseStart_670677 baseEnd_670677 := by
    simpa [prefixWord, tailWord_670677, baseEnd_670677] using wordTrace_append hprefix tailTrace_670677
  have hstable : (prefixWord ++ tailWord_670677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670677).length < 2 ^ (prefixWord ++ tailWord_670677).sum := by decide
  have hdescent : baseEnd_670677 < baseStart_670677 := by decide
  rcases family_descends (prefixWord ++ tailWord_670677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670690 : List Nat := [3, 3, 3, 1, 1, 1, 4, 7]
def baseStart_670690 : Nat := 118140960795 + 670690 * 2 ^ 59
def prefixEnd_670690 : Nat := 4983230072969 + 3 ^ 40 * 670690 * 2
def baseEnd_670690 : Nat := 12755049635706894666317

theorem tailTrace_670690 : CollatzResearch.WordTrace tailWord_670690 prefixEnd_670690 12755049635706894666317 := by
  unfold tailWord_670690
  simp only [CollatzResearch.WordTrace]
  refine ⟨6115518485053037394434381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16308049293474766385158349 6115518485053037394434381)
  ·
    refine ⟨2293319431894889022912893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6115518485053037394434381 2293319431894889022912893)
    ·
      refine ⟨859994786960583383592335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2293319431894889022912893 859994786960583383592335)
      ·
        refine ⟨1289992180440875075388503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 859994786960583383592335 1289992180440875075388503)
        ·
          refine ⟨1934988270661312613082755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1289992180440875075388503 1934988270661312613082755)
          ·
            refine ⟨2902482405991968919624133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1934988270661312613082755 2902482405991968919624133)
            ·
              refine ⟨544215451123494172429525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2902482405991968919624133 544215451123494172429525)
              ·
                refine ⟨12755049635706894666317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 544215451123494172429525 12755049635706894666317)
                ·
                  rfl

theorem cell23_670690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 7].length) (baseStart_670690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670690 prefixEnd_670690 := by exact prefixLift 670690
  have htrace : WordTrace (prefixWord ++ tailWord_670690) baseStart_670690 baseEnd_670690 := by
    simpa [prefixWord, tailWord_670690, baseEnd_670690] using wordTrace_append hprefix tailTrace_670690
  have hstable : (prefixWord ++ tailWord_670690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670690).length < 2 ^ (prefixWord ++ tailWord_670690).sum := by decide
  have hdescent : baseEnd_670690 < baseStart_670690 := by decide
  rcases family_descends (prefixWord ++ tailWord_670690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670696 : List Nat := [2, 1, 4, 1, 1, 1, 3, 1, 2, 2, 5]
def baseStart_670696 : Nat := 118140960795 + 670696 * 2 ^ 59
def prefixEnd_670696 : Nat := 4983230072969 + 3 ^ 40 * 670696 * 2
def baseEnd_670696 : Nat := 344389421048013132515531

theorem tailTrace_670696 : CollatzResearch.WordTrace tailWord_670696 prefixEnd_670696 344389421048013132515531 := by
  unfold tailWord_670696
  simp only [CollatzResearch.WordTrace]
  refine ⟨12231146389095206301227971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16308195185460275068303961 12231146389095206301227971)
  ·
    refine ⟨18346719583642809451841957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12231146389095206301227971 18346719583642809451841957)
    ·
      refine ⟨3440009921933026772220367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18346719583642809451841957 3440009921933026772220367)
      ·
        refine ⟨5160014882899540158330551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3440009921933026772220367 5160014882899540158330551)
        ·
          refine ⟨7740022324349310237495827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5160014882899540158330551 7740022324349310237495827)
          ·
            refine ⟨11610033486523965356243741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7740022324349310237495827 11610033486523965356243741)
            ·
              refine ⟨4353762557446487008591403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11610033486523965356243741 4353762557446487008591403)
              ·
                refine ⟨6530643836169730512887105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4353762557446487008591403 6530643836169730512887105)
                ·
                  refine ⟨4897982877127297884665329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6530643836169730512887105 4897982877127297884665329)
                  ·
                    refine ⟨3673487157845473413498997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4897982877127297884665329 3673487157845473413498997)
                    ·
                      refine ⟨344389421048013132515531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3673487157845473413498997 344389421048013132515531)
                      ·
                        rfl

theorem cell23_670696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_670696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670696 prefixEnd_670696 := by exact prefixLift 670696
  have htrace : WordTrace (prefixWord ++ tailWord_670696) baseStart_670696 baseEnd_670696 := by
    simpa [prefixWord, tailWord_670696, baseEnd_670696] using wordTrace_append hprefix tailTrace_670696
  have hstable : (prefixWord ++ tailWord_670696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670696).length < 2 ^ (prefixWord ++ tailWord_670696).sum := by decide
  have hdescent : baseEnd_670696 < baseStart_670696 := by decide
  rcases family_descends (prefixWord ++ tailWord_670696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670718 : List Nat := [4, 2, 2, 2, 2, 1, 3, 2, 1, 2, 2]
def baseStart_670718 : Nat := 118140960795 + 670718 * 2 ^ 59
def prefixEnd_670718 : Nat := 4983230072969 + 3 ^ 40 * 670718 * 2
def baseEnd_670718 : Nat := 344400717622412046440431

theorem tailTrace_670718 : CollatzResearch.WordTrace tailWord_670718 prefixEnd_670718 344400717622412046440431 := by
  unfold tailWord_670718
  simp only [CollatzResearch.WordTrace]
  refine ⟨3057886898013838794969601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16308730122740473573171205 3057886898013838794969601)
  ·
    refine ⟨2293415173510379096227201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3057886898013838794969601 2293415173510379096227201)
    ·
      refine ⟨1720061380132784322170401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2293415173510379096227201 1720061380132784322170401)
      ·
        refine ⟨1290046035099588241627801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1720061380132784322170401 1290046035099588241627801)
        ·
          refine ⟨967534526324691181220851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1290046035099588241627801 967534526324691181220851)
          ·
            refine ⟨1451301789487036771831277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 967534526324691181220851 1451301789487036771831277)
            ·
              refine ⟨544238171057638789436729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1451301789487036771831277 544238171057638789436729)
              ·
                refine ⟨408178628293229092077547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 544238171057638789436729 408178628293229092077547)
                ·
                  refine ⟨612267942439843638116321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 408178628293229092077547 612267942439843638116321)
                  ·
                    refine ⟨459200956829882728587241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 612267942439843638116321 459200956829882728587241)
                    ·
                      refine ⟨344400717622412046440431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 459200956829882728587241 344400717622412046440431)
                      ·
                        rfl

theorem cell23_670718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_670718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670718 prefixEnd_670718 := by exact prefixLift 670718
  have htrace : WordTrace (prefixWord ++ tailWord_670718) baseStart_670718 baseEnd_670718 := by
    simpa [prefixWord, tailWord_670718, baseEnd_670718] using wordTrace_append hprefix tailTrace_670718
  have hstable : (prefixWord ++ tailWord_670718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670718).length < 2 ^ (prefixWord ++ tailWord_670718).sum := by decide
  have hdescent : baseEnd_670718 < baseStart_670718 := by decide
  rcases family_descends (prefixWord ++ tailWord_670718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670734 : List Nat := [4, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3]
def baseStart_670734 : Nat := 118140960795 + 670734 * 2 ^ 59
def prefixEnd_670734 : Nat := 4983230072969 + 3 ^ 40 * 670734 * 2
def baseEnd_670734 : Nat := 344408933312883983840357

theorem tailTrace_670734 : CollatzResearch.WordTrace tailWord_670734 prefixEnd_670734 344408933312883983840357 := by
  unfold tailWord_670734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3057959844006593136542407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16309119168035163394892837 3057959844006593136542407)
  ·
    refine ⟨4586939766009889704813611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3057959844006593136542407 4586939766009889704813611)
    ·
      refine ⟨6880409649014834557220417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4586939766009889704813611 6880409649014834557220417)
      ·
        refine ⟨5160307236761125917915313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6880409649014834557220417 5160307236761125917915313)
        ·
          refine ⟨3870230427570844438436485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5160307236761125917915313 3870230427570844438436485)
          ·
            refine ⟨725668205169533332206841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3870230427570844438436485 725668205169533332206841)
            ·
              refine ⟨544251153877149999155131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 725668205169533332206841 544251153877149999155131)
              ·
                refine ⟨816376730815724998732697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 544251153877149999155131 816376730815724998732697)
                ·
                  refine ⟨612282548111793749049523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 816376730815724998732697 612282548111793749049523)
                  ·
                    refine ⟨918423822167690623574285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 612282548111793749049523 918423822167690623574285)
                    ·
                      refine ⟨344408933312883983840357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 918423822167690623574285 344408933312883983840357)
                      ·
                        rfl

theorem cell23_670734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_670734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670734 prefixEnd_670734 := by exact prefixLift 670734
  have htrace : WordTrace (prefixWord ++ tailWord_670734) baseStart_670734 baseEnd_670734 := by
    simpa [prefixWord, tailWord_670734, baseEnd_670734] using wordTrace_append hprefix tailTrace_670734
  have hstable : (prefixWord ++ tailWord_670734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670734).length < 2 ^ (prefixWord ++ tailWord_670734).sum := by decide
  have hdescent : baseEnd_670734 < baseStart_670734 := by decide
  rcases family_descends (prefixWord ++ tailWord_670734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670738 : List Nat := [3, 2, 5, 1, 2, 1, 1, 2, 1, 2, 3]
def baseStart_670738 : Nat := 118140960795 + 670738 * 2 ^ 59
def prefixEnd_670738 : Nat := 4983230072969 + 3 ^ 40 * 670738 * 2
def baseEnd_670738 : Nat := 344410987235501968190339

theorem tailTrace_670738 : CollatzResearch.WordTrace tailWord_670738 prefixEnd_670738 344410987235501968190339 := by
  unfold tailWord_670738
  simp only [CollatzResearch.WordTrace]
  refine ⟨6115956161009563443871217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16309216429358835850323245 6115956161009563443871217)
  ·
    refine ⟨4586967120757172582903413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6115956161009563443871217 4586967120757172582903413)
    ·
      refine ⟨430028167570984929647195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4586967120757172582903413 430028167570984929647195)
      ·
        refine ⟨645042251356477394470793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 430028167570984929647195 645042251356477394470793)
        ·
          refine ⟨483781688517358045853095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 645042251356477394470793 483781688517358045853095)
          ·
            refine ⟨725672532776037068779643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 483781688517358045853095 725672532776037068779643)
            ·
              refine ⟨1088508799164055603169465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 725672532776037068779643 1088508799164055603169465)
              ·
                refine ⟨816381599373041702377099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1088508799164055603169465 816381599373041702377099)
                ·
                  refine ⟨1224572399059562553565649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 816381599373041702377099 1224572399059562553565649)
                  ·
                    refine ⟨918429299294671915174237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1224572399059562553565649 918429299294671915174237)
                    ·
                      refine ⟨344410987235501968190339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 918429299294671915174237 344410987235501968190339)
                      ·
                        rfl

theorem cell23_670738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_670738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670738 prefixEnd_670738 := by exact prefixLift 670738
  have htrace : WordTrace (prefixWord ++ tailWord_670738) baseStart_670738 baseEnd_670738 := by
    simpa [prefixWord, tailWord_670738, baseEnd_670738] using wordTrace_append hprefix tailTrace_670738
  have hstable : (prefixWord ++ tailWord_670738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670738).length < 2 ^ (prefixWord ++ tailWord_670738).sum := by decide
  have hdescent : baseEnd_670738 < baseStart_670738 := by decide
  rcases family_descends (prefixWord ++ tailWord_670738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670743 : List Nat := [1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 5]
def baseStart_670743 : Nat := 118140960795 + 670743 * 2 ^ 59
def prefixEnd_670743 : Nat := 4983230072969 + 3 ^ 40 * 670743 * 2
def baseEnd_670743 : Nat := 344413554638774448627815

theorem tailTrace_670743 : CollatzResearch.WordTrace tailWord_670743 prefixEnd_670743 344413554638774448627815 := by
  unfold tailWord_670743
  simp only [CollatzResearch.WordTrace]
  refine ⟨24464007009020139629416883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16309338006013426419611255 24464007009020139629416883)
  ·
    refine ⟨36696010513530209444125325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24464007009020139629416883 36696010513530209444125325)
    ·
      refine ⟨13761003942573828541546997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36696010513530209444125325 13761003942573828541546997)
      ·
        refine ⟨1290094119616296425770031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13761003942573828541546997 1290094119616296425770031)
        ·
          refine ⟨1935141179424444638655047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1290094119616296425770031 1935141179424444638655047)
          ·
            refine ⟨2902711769136666957982571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1935141179424444638655047 2902711769136666957982571)
            ·
              refine ⟨4354067653705000436973857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2902711769136666957982571 4354067653705000436973857)
              ·
                refine ⟨3265550740278750327730393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4354067653705000436973857 3265550740278750327730393)
                ·
                  refine ⟨2449163055209062745797795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3265550740278750327730393 2449163055209062745797795)
                  ·
                    refine ⟨3673744582813594118696693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2449163055209062745797795 3673744582813594118696693)
                    ·
                      refine ⟨344413554638774448627815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3673744582813594118696693 344413554638774448627815)
                      ·
                        rfl

theorem cell23_670743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_670743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670743 prefixEnd_670743 := by exact prefixLift 670743
  have htrace : WordTrace (prefixWord ++ tailWord_670743) baseStart_670743 baseEnd_670743 := by
    simpa [prefixWord, tailWord_670743, baseEnd_670743] using wordTrace_append hprefix tailTrace_670743
  have hstable : (prefixWord ++ tailWord_670743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670743).length < 2 ^ (prefixWord ++ tailWord_670743).sum := by decide
  have hdescent : baseEnd_670743 < baseStart_670743 := by decide
  rcases family_descends (prefixWord ++ tailWord_670743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670746 : List Nat := [3, 1, 1, 3, 1, 2, 2, 1, 9]
def baseStart_670746 : Nat := 118140960795 + 670746 * 2 ^ 59
def prefixEnd_670746 : Nat := 4983230072969 + 3 ^ 40 * 670746 * 2
def baseEnd_670746 : Nat := 38268343897859770765589

theorem tailTrace_670746 : CollatzResearch.WordTrace tailWord_670746 prefixEnd_670746 38268343897859770765589 := by
  unfold tailWord_670746
  simp only [CollatzResearch.WordTrace]
  refine ⟨6116029107002317785444023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16309410952006180761184061 6116029107002317785444023)
  ·
    refine ⟨9174043660503476678166035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6116029107002317785444023 9174043660503476678166035)
    ·
      refine ⟨13761065490755215017249053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9174043660503476678166035 13761065490755215017249053)
      ·
        refine ⟨5160399559033205631468395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13761065490755215017249053 5160399559033205631468395)
        ·
          refine ⟨7740599338549808447202593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5160399559033205631468395 7740599338549808447202593)
          ·
            refine ⟨5805449503912356335401945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7740599338549808447202593 5805449503912356335401945)
            ·
              refine ⟨4354087127934267251551459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5805449503912356335401945 4354087127934267251551459)
              ·
                refine ⟨6531130691901400877327189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4354087127934267251551459 6531130691901400877327189)
                ·
                  refine ⟨38268343897859770765589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6531130691901400877327189 38268343897859770765589)
                  ·
                    rfl

theorem cell23_670746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 9].length) (baseStart_670746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670746 prefixEnd_670746 := by exact prefixLift 670746
  have htrace : WordTrace (prefixWord ++ tailWord_670746) baseStart_670746 baseEnd_670746 := by
    simpa [prefixWord, tailWord_670746, baseEnd_670746] using wordTrace_append hprefix tailTrace_670746
  have hstable : (prefixWord ++ tailWord_670746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670746).length < 2 ^ (prefixWord ++ tailWord_670746).sum := by decide
  have hdescent : baseEnd_670746 < baseStart_670746 := by decide
  rcases family_descends (prefixWord ++ tailWord_670746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670763 : List Nat := [1, 1, 1, 1, 2, 1, 6, 5, 5]
def baseStart_670763 : Nat := 118140960795 + 670763 * 2 ^ 59
def prefixEnd_670763 : Nat := 4983230072969 + 3 ^ 40 * 670763 * 2
def baseEnd_670763 : Nat := 38269313805762707819747

theorem tailTrace_670763 : CollatzResearch.WordTrace tailWord_670763 prefixEnd_670763 38269313805762707819747 := by
  unfold tailWord_670763
  simp only [CollatzResearch.WordTrace]
  refine ⟨24464736468947683045144943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16309824312631788696763295 24464736468947683045144943)
  ·
    refine ⟨36697104703421524567717415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24464736468947683045144943 36697104703421524567717415)
    ·
      refine ⟨55045657055132286851576123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36697104703421524567717415 55045657055132286851576123)
      ·
        refine ⟨82568485582698430277364185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55045657055132286851576123 82568485582698430277364185)
        ·
          refine ⟨61926364187023822708023139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82568485582698430277364185 61926364187023822708023139)
          ·
            refine ⟨92889546280535734062034709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61926364187023822708023139 92889546280535734062034709)
            ·
              refine ⟨4354197481900112534157877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 92889546280535734062034709 4354197481900112534157877)
              ·
                refine ⟨408206013928135550077301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4354197481900112534157877 408206013928135550077301)
                ·
                  refine ⟨38269313805762707819747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 408206013928135550077301 38269313805762707819747)
                  ·
                    rfl

theorem cell23_670763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 5, 5].length) (baseStart_670763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670763 prefixEnd_670763 := by exact prefixLift 670763
  have htrace : WordTrace (prefixWord ++ tailWord_670763) baseStart_670763 baseEnd_670763 := by
    simpa [prefixWord, tailWord_670763, baseEnd_670763] using wordTrace_append hprefix tailTrace_670763
  have hstable : (prefixWord ++ tailWord_670763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670763).length < 2 ^ (prefixWord ++ tailWord_670763).sum := by decide
  have hdescent : baseEnd_670763 < baseStart_670763 := by decide
  rcases family_descends (prefixWord ++ tailWord_670763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670773 : List Nat := [1, 3, 3, 1, 1, 1, 1, 4, 2, 3, 3]
def baseStart_670773 : Nat := 118140960795 + 670773 * 2 ^ 59
def prefixEnd_670773 : Nat := 4983230072969 + 3 ^ 40 * 670773 * 2
def baseEnd_670773 : Nat := 344428959058409331252677

theorem tailTrace_670773 : CollatzResearch.WordTrace tailWord_670773 prefixEnd_670773 344428959058409331252677 := by
  unfold tailWord_670773
  simp only [CollatzResearch.WordTrace]
  refine ⟨24465101198911454753008973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16310067465940969835339315 24465101198911454753008973)
  ·
    refine ⟨9174412949591795532378365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24465101198911454753008973 9174412949591795532378365)
    ·
      refine ⟨3440404856096923324641887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9174412949591795532378365 3440404856096923324641887)
      ·
        refine ⟨5160607284145384986962831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3440404856096923324641887 5160607284145384986962831)
        ·
          refine ⟨7740910926218077480444247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5160607284145384986962831 7740910926218077480444247)
          ·
            refine ⟨11611366389327116220666371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7740910926218077480444247 11611366389327116220666371)
            ·
              refine ⟨17417049583990674330999557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11611366389327116220666371 17417049583990674330999557)
              ·
                refine ⟨3265696796998251437062417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17417049583990674330999557 3265696796998251437062417)
                ·
                  refine ⟨2449272597748688577796813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3265696796998251437062417 2449272597748688577796813)
                  ·
                    refine ⟨918477224155758216673805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2449272597748688577796813 918477224155758216673805)
                    ·
                      refine ⟨344428959058409331252677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 918477224155758216673805 344428959058409331252677)
                      ·
                        rfl

theorem cell23_670773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_670773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670773 prefixEnd_670773 := by exact prefixLift 670773
  have htrace : WordTrace (prefixWord ++ tailWord_670773) baseStart_670773 baseEnd_670773 := by
    simpa [prefixWord, tailWord_670773, baseEnd_670773] using wordTrace_append hprefix tailTrace_670773
  have hstable : (prefixWord ++ tailWord_670773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670773).length < 2 ^ (prefixWord ++ tailWord_670773).sum := by decide
  have hdescent : baseEnd_670773 < baseStart_670773 := by decide
  rcases family_descends (prefixWord ++ tailWord_670773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670774 : List Nat := [5, 1, 2, 1, 1, 2, 1, 4, 2, 2, 2]
def baseStart_670774 : Nat := 118140960795 + 670774 * 2 ^ 59
def prefixEnd_670774 : Nat := 4983230072969 + 3 ^ 40 * 670774 * 2
def baseEnd_670774 : Nat := 344429472539063827340173

theorem tailTrace_670774 : CollatzResearch.WordTrace tailWord_670774 prefixEnd_670774 344429472539063827340173 := by
  unfold tailWord_670774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1529071104494239495237211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16310091781271887949196917 1529071104494239495237211)
  ·
    refine ⟨2293606656741359242855817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1529071104494239495237211 2293606656741359242855817)
    ·
      refine ⟨1720204992556019432141863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2293606656741359242855817 1720204992556019432141863)
      ·
        refine ⟨2580307488834029148212795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1720204992556019432141863 2580307488834029148212795)
        ·
          refine ⟨3870461233251043722319193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2580307488834029148212795 3870461233251043722319193)
          ·
            refine ⟨2902845924938282791739395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3870461233251043722319193 2902845924938282791739395)
            ·
              refine ⟨4354268887407424187609093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2902845924938282791739395 4354268887407424187609093)
              ·
                refine ⟨816425416388892035176705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4354268887407424187609093 816425416388892035176705)
                ·
                  refine ⟨612319062291669026382529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 816425416388892035176705 612319062291669026382529)
                  ·
                    refine ⟨459239296718751769786897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 612319062291669026382529 459239296718751769786897)
                    ·
                      refine ⟨344429472539063827340173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 459239296718751769786897 344429472539063827340173)
                      ·
                        rfl

theorem cell23_670774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_670774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670774 prefixEnd_670774 := by exact prefixLift 670774
  have htrace : WordTrace (prefixWord ++ tailWord_670774) baseStart_670774 baseEnd_670774 := by
    simpa [prefixWord, tailWord_670774, baseEnd_670774] using wordTrace_append hprefix tailTrace_670774
  have hstable : (prefixWord ++ tailWord_670774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670774).length < 2 ^ (prefixWord ++ tailWord_670774).sum := by decide
  have hdescent : baseEnd_670774 < baseStart_670774 := by decide
  rcases family_descends (prefixWord ++ tailWord_670774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670780 : List Nat := [2, 2, 2, 2, 2, 3, 1, 4, 5]
def baseStart_670780 : Nat := 118140960795 + 670780 * 2 ^ 59
def prefixEnd_670780 : Nat := 4983230072969 + 3 ^ 40 * 670780 * 2
def baseEnd_670780 : Nat := 38270283713665644873905

theorem tailTrace_670780 : CollatzResearch.WordTrace tailWord_670780 prefixEnd_670780 38270283713665644873905 := by
  unfold tailWord_670780
  simp only [CollatzResearch.WordTrace]
  refine ⟨12232678254943047474256897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16310237673257396632342529 12232678254943047474256897)
  ·
    refine ⟨9174508691207285605692673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12232678254943047474256897 9174508691207285605692673)
    ·
      refine ⟨6880881518405464204269505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9174508691207285605692673 6880881518405464204269505)
      ·
        refine ⟨5160661138804098153202129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6880881518405464204269505 5160661138804098153202129)
        ·
          refine ⟨3870495854103073614901597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5160661138804098153202129 3870495854103073614901597)
          ·
            refine ⟨1451435945288652605588099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3870495854103073614901597 1451435945288652605588099)
            ·
              refine ⟨2177153917932978908382149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1451435945288652605588099 2177153917932978908382149)
              ·
                refine ⟨408216359612433545321653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2177153917932978908382149 408216359612433545321653)
                ·
                  refine ⟨38270283713665644873905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 408216359612433545321653 38270283713665644873905)
                  ·
                    rfl

theorem cell23_670780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 4, 5].length) (baseStart_670780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670780 prefixEnd_670780 := by exact prefixLift 670780
  have htrace : WordTrace (prefixWord ++ tailWord_670780) baseStart_670780 baseEnd_670780 := by
    simpa [prefixWord, tailWord_670780, baseEnd_670780] using wordTrace_append hprefix tailTrace_670780
  have hstable : (prefixWord ++ tailWord_670780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670780).length < 2 ^ (prefixWord ++ tailWord_670780).sum := by decide
  have hdescent : baseEnd_670780 < baseStart_670780 := by decide
  rcases family_descends (prefixWord ++ tailWord_670780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670814 : List Nat := [4, 4, 1, 1, 1, 1, 1, 5, 5]
def baseStart_670814 : Nat := 118140960795 + 670814 * 2 ^ 59
def prefixEnd_670814 : Nat := 4983230072969 + 3 ^ 40 * 670814 * 2
def baseEnd_670814 : Nat := 38272223529471518982221

theorem tailTrace_670814 : CollatzResearch.WordTrace tailWord_670814 prefixEnd_670814 38272223529471518982221 := by
  unfold tailWord_670814
  simp only [CollatzResearch.WordTrace]
  refine ⟨3058324573970364844406437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16311064394508612503500997 3058324573970364844406437)
  ·
    refine ⟨573435857619443408326207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3058324573970364844406437 573435857619443408326207)
    ·
      refine ⟨860153786429165112489311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 573435857619443408326207 860153786429165112489311)
      ·
        refine ⟨1290230679643747668733967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 860153786429165112489311 1290230679643747668733967)
        ·
          refine ⟨1935346019465621503100951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1290230679643747668733967 1935346019465621503100951)
          ·
            refine ⟨2903019029198432254651427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1935346019465621503100951 2903019029198432254651427)
            ·
              refine ⟨4354528543797648381977141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2903019029198432254651427 4354528543797648381977141)
              ·
                refine ⟨408237050981029535810357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4354528543797648381977141 408237050981029535810357)
                ·
                  refine ⟨38272223529471518982221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 408237050981029535810357 38272223529471518982221)
                  ·
                    rfl

theorem cell23_670814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_670814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670814 prefixEnd_670814 := by exact prefixLift 670814
  have htrace : WordTrace (prefixWord ++ tailWord_670814) baseStart_670814 baseEnd_670814 := by
    simpa [prefixWord, tailWord_670814, baseEnd_670814] using wordTrace_append hprefix tailTrace_670814
  have hstable : (prefixWord ++ tailWord_670814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670814).length < 2 ^ (prefixWord ++ tailWord_670814).sum := by decide
  have hdescent : baseEnd_670814 < baseStart_670814 := by decide
  rcases family_descends (prefixWord ++ tailWord_670814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670874 : List Nat := [3, 1, 1, 5, 1, 1, 3, 3, 1, 4]
def baseStart_670874 : Nat := 118140960795 + 670874 * 2 ^ 59
def prefixEnd_670874 : Nat := 4983230072969 + 3 ^ 40 * 670874 * 2
def baseEnd_670874 : Nat := 114826940201504478696571

theorem tailTrace_670874 : CollatzResearch.WordTrace tailWord_670874 prefixEnd_670874 114826940201504478696571 := by
  unfold tailWord_670874
  simp only [CollatzResearch.WordTrace]
  refine ⟨6117196242886387250608919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16312523314363699334957117 6117196242886387250608919)
  ·
    refine ⟨9175794364329580875913379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6117196242886387250608919 9175794364329580875913379)
    ·
      refine ⟨13763691546494371313870069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9175794364329580875913379 13763691546494371313870069)
      ·
        refine ⟨1290346082483847310675319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13763691546494371313870069 1290346082483847310675319)
        ·
          refine ⟨1935519123725770966012979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1290346082483847310675319 1935519123725770966012979)
          ·
            refine ⟨2903278685588656449019469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1935519123725770966012979 2903278685588656449019469)
            ·
              refine ⟨1088729507095746168382301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2903278685588656449019469 1088729507095746168382301)
              ·
                refine ⟨408273565160904813143363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1088729507095746168382301 408273565160904813143363)
                ·
                  refine ⟨612410347741357219715045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 408273565160904813143363 612410347741357219715045)
                  ·
                    refine ⟨114826940201504478696571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 612410347741357219715045 114826940201504478696571)
                    ·
                      rfl

theorem cell23_670874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 3, 1, 4].length) (baseStart_670874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670874 prefixEnd_670874 := by exact prefixLift 670874
  have htrace : WordTrace (prefixWord ++ tailWord_670874) baseStart_670874 baseEnd_670874 := by
    simpa [prefixWord, tailWord_670874, baseEnd_670874] using wordTrace_append hprefix tailTrace_670874
  have hstable : (prefixWord ++ tailWord_670874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670874).length < 2 ^ (prefixWord ++ tailWord_670874).sum := by decide
  have hdescent : baseEnd_670874 < baseStart_670874 := by decide
  rcases family_descends (prefixWord ++ tailWord_670874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670918 : List Nat := [6, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3]
def baseStart_670918 : Nat := 118140960795 + 670918 * 2 ^ 59
def prefixEnd_670918 : Nat := 4983230072969 + 3 ^ 40 * 670918 * 2
def baseEnd_670918 : Nat := 344503413753311263939511

theorem tailTrace_670918 : CollatzResearch.WordTrace tailWord_670918 prefixEnd_670918 344503413753311263939511 := by
  unfold tailWord_670918
  simp only [CollatzResearch.WordTrace]
  refine ⟨764699680730817016157419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16313593188924096344691605 764699680730817016157419)
  ·
    refine ⟨1147049521096225524236129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 764699680730817016157419 1147049521096225524236129)
    ·
      refine ⟨860287140822169143177097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1147049521096225524236129 860287140822169143177097)
      ·
        refine ⟨645215355616626857382823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 860287140822169143177097 645215355616626857382823)
        ·
          refine ⟨967823033424940286074235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 645215355616626857382823 967823033424940286074235)
          ·
            refine ⟨1451734550137410429111353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 967823033424940286074235 1451734550137410429111353)
            ·
              refine ⟨1088800912603057821833515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1451734550137410429111353 1088800912603057821833515)
              ·
                refine ⟨1633201368904586732750273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1088800912603057821833515 1633201368904586732750273)
                ·
                  refine ⟨1224901026678440049562705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1633201368904586732750273 1224901026678440049562705)
                  ·
                    refine ⟨918675770008830037172029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1224901026678440049562705 918675770008830037172029)
                    ·
                      refine ⟨344503413753311263939511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 918675770008830037172029 344503413753311263939511)
                      ·
                        rfl

theorem cell23_670918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_670918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670918 prefixEnd_670918 := by exact prefixLift 670918
  have htrace : WordTrace (prefixWord ++ tailWord_670918) baseStart_670918 baseEnd_670918 := by
    simpa [prefixWord, tailWord_670918, baseEnd_670918] using wordTrace_append hprefix tailTrace_670918
  have hstable : (prefixWord ++ tailWord_670918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670918).length < 2 ^ (prefixWord ++ tailWord_670918).sum := by decide
  have hdescent : baseEnd_670918 < baseStart_670918 := by decide
  rcases family_descends (prefixWord ++ tailWord_670918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670920 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 2, 6, 2]
def baseStart_670920 : Nat := 118140960795 + 670920 * 2 ^ 59
def prefixEnd_670920 : Nat := 4983230072969 + 3 ^ 40 * 670920 * 2
def baseEnd_670920 : Nat := 344504440714620256114501

theorem tailTrace_670920 : CollatzResearch.WordTrace tailWord_670920 prefixEnd_670920 344504440714620256114501 := by
  unfold tailWord_670920
  simp only [CollatzResearch.WordTrace]
  refine ⟨12235231364689449429305107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16313641819585932572406809 12235231364689449429305107)
  ·
    refine ⟨18352847047034174143957661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12235231364689449429305107 18352847047034174143957661)
    ·
      refine ⟨6882317642637815303984123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18352847047034174143957661 6882317642637815303984123)
      ·
        refine ⟨10323476463956722955976185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6882317642637815303984123 10323476463956722955976185)
        ·
          refine ⟨7742607347967542216982139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10323476463956722955976185 7742607347967542216982139)
          ·
            refine ⟨11613911021951313325473209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7742607347967542216982139 11613911021951313325473209)
            ·
              refine ⟨8710433266463484994104907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11613911021951313325473209 8710433266463484994104907)
              ·
                refine ⟨13065649899695227491157361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8710433266463484994104907 13065649899695227491157361)
                ·
                  refine ⟨9799237424771420618368021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13065649899695227491157361 9799237424771420618368021)
                  ·
                    refine ⟨459339254286160341486001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9799237424771420618368021 459339254286160341486001)
                    ·
                      refine ⟨344504440714620256114501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 459339254286160341486001 344504440714620256114501)
                      ·
                        rfl

theorem cell23_670920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 2, 6, 2].length) (baseStart_670920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670920 prefixEnd_670920 := by exact prefixLift 670920
  have htrace : WordTrace (prefixWord ++ tailWord_670920) baseStart_670920 baseEnd_670920 := by
    simpa [prefixWord, tailWord_670920, baseEnd_670920] using wordTrace_append hprefix tailTrace_670920
  have hstable : (prefixWord ++ tailWord_670920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670920).length < 2 ^ (prefixWord ++ tailWord_670920).sum := by decide
  have hdescent : baseEnd_670920 < baseStart_670920 := by decide
  rcases family_descends (prefixWord ++ tailWord_670920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670930 : List Nat := [3, 2, 2, 2, 1, 1, 3, 2, 1, 6]
def baseStart_670930 : Nat := 118140960795 + 670930 * 2 ^ 59
def prefixEnd_670930 : Nat := 4983230072969 + 3 ^ 40 * 670930 * 2
def baseEnd_670930 : Nat := 114836525173721738996485

theorem tailTrace_670930 : CollatzResearch.WordTrace tailWord_670930 prefixEnd_670930 114836525173721738996485 := by
  unfold tailWord_670930
  simp only [CollatzResearch.WordTrace]
  refine ⟨6117706864835667641618561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16313884972895113710982829 6117706864835667641618561)
  ·
    refine ⟨4588280148626750731213921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6117706864835667641618561 4588280148626750731213921)
    ·
      refine ⟨3441210111470063048410441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4588280148626750731213921 3441210111470063048410441)
      ·
        refine ⟨2580907583602547286307831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3441210111470063048410441 2580907583602547286307831)
        ·
          refine ⟨3871361375403820929461747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2580907583602547286307831 3871361375403820929461747)
          ·
            refine ⟨5807042063105731394192621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3871361375403820929461747 5807042063105731394192621)
            ·
              refine ⟨2177640773664649272822233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5807042063105731394192621 2177640773664649272822233)
              ·
                refine ⟨1633230580248486954616675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2177640773664649272822233 1633230580248486954616675)
                ·
                  refine ⟨2449845870372730431925013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1633230580248486954616675 2449845870372730431925013)
                  ·
                    refine ⟨114836525173721738996485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2449845870372730431925013 114836525173721738996485)
                    ·
                      rfl

theorem cell23_670930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_670930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670930 prefixEnd_670930 := by exact prefixLift 670930
  have htrace : WordTrace (prefixWord ++ tailWord_670930) baseStart_670930 baseEnd_670930 := by
    simpa [prefixWord, tailWord_670930, baseEnd_670930] using wordTrace_append hprefix tailTrace_670930
  have hstable : (prefixWord ++ tailWord_670930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670930).length < 2 ^ (prefixWord ++ tailWord_670930).sum := by decide
  have hdescent : baseEnd_670930 < baseStart_670930 := by decide
  rcases family_descends (prefixWord ++ tailWord_670930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670957 : List Nat := [1, 5, 1, 2, 2, 1, 1, 2, 3, 2, 3]
def baseStart_670957 : Nat := 118140960795 + 670957 * 2 ^ 59
def prefixEnd_670957 : Nat := 4983230072969 + 3 ^ 40 * 670957 * 2
def baseEnd_670957 : Nat := 344523439498836611351831

theorem tailTrace_670957 : CollatzResearch.WordTrace tailWord_670957 prefixEnd_670957 344523439498836611351831 := by
  unfold tailWord_670957
  simp only [CollatzResearch.WordTrace]
  refine ⟨24471812230244854177707125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16314541486829902785138083 24471812230244854177707125)
  ·
    refine ⟨2294232396585455079160043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24471812230244854177707125 2294232396585455079160043)
    ·
      refine ⟨3441348594878182618740065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2294232396585455079160043 3441348594878182618740065)
      ·
        refine ⟨2581011446158636964055049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3441348594878182618740065 2581011446158636964055049)
        ·
          refine ⟨1935758584618977723041287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2581011446158636964055049 1935758584618977723041287)
          ·
            refine ⟨2903637876928466584561931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1935758584618977723041287 2903637876928466584561931)
            ·
              refine ⟨4355456815392699876842897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2903637876928466584561931 4355456815392699876842897)
              ·
                refine ⟨3266592611544524907632173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4355456815392699876842897 3266592611544524907632173)
                ·
                  refine ⟨1224972229329196840362065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3266592611544524907632173 1224972229329196840362065)
                  ·
                    refine ⟨918729171996897630271549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1224972229329196840362065 918729171996897630271549)
                    ·
                      refine ⟨344523439498836611351831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 918729171996897630271549 344523439498836611351831)
                      ·
                        rfl

theorem cell23_670957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_670957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_670957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_670957 prefixEnd_670957 := by exact prefixLift 670957
  have htrace : WordTrace (prefixWord ++ tailWord_670957) baseStart_670957 baseEnd_670957 := by
    simpa [prefixWord, tailWord_670957, baseEnd_670957] using wordTrace_append hprefix tailTrace_670957
  have hstable : (prefixWord ++ tailWord_670957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670957).length < 2 ^ (prefixWord ++ tailWord_670957).sum := by decide
  have hdescent : baseEnd_670957 < baseStart_670957 := by decide
  rcases family_descends (prefixWord ++ tailWord_670957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671004 : List Nat := [2, 2, 3, 1, 1, 1, 5, 2, 2, 1, 3]
def baseStart_671004 : Nat := 118140960795 + 671004 * 2 ^ 59
def prefixEnd_671004 : Nat := 4983230072969 + 3 ^ 40 * 671004 * 2
def baseEnd_671004 : Nat := 344547573089597927464115

theorem tailTrace_671004 : CollatzResearch.WordTrace tailWord_671004 prefixEnd_671004 344547573089597927464115 := by
  unfold tailWord_671004
  simp only [CollatzResearch.WordTrace]
  refine ⟨12236763230537290602334033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16315684307383054136445377 12236763230537290602334033)
  ·
    refine ⟨9177572422902967951750525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12236763230537290602334033 9177572422902967951750525)
    ·
      refine ⟨3441589658588612981906447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9177572422902967951750525 3441589658588612981906447)
      ·
        refine ⟨5162384487882919472859671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3441589658588612981906447 5162384487882919472859671)
        ·
          refine ⟨7743576731824379209289507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5162384487882919472859671 7743576731824379209289507)
          ·
            refine ⟨11615365097736568813934261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7743576731824379209289507 11615365097736568813934261)
            ·
              refine ⟨1088940477912803326306337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11615365097736568813934261 1088940477912803326306337)
              ·
                refine ⟨816705358434602494729753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1088940477912803326306337 816705358434602494729753)
                ·
                  refine ⟨612529018825951871047315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 816705358434602494729753 612529018825951871047315)
                  ·
                    refine ⟨918793528238927806570973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 612529018825951871047315 918793528238927806570973)
                    ·
                      refine ⟨344547573089597927464115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 918793528238927806570973 344547573089597927464115)
                      ·
                        rfl

theorem cell23_671004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_671004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671004 prefixEnd_671004 := by exact prefixLift 671004
  have htrace : WordTrace (prefixWord ++ tailWord_671004) baseStart_671004 baseEnd_671004 := by
    simpa [prefixWord, tailWord_671004, baseEnd_671004] using wordTrace_append hprefix tailTrace_671004
  have hstable : (prefixWord ++ tailWord_671004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671004).length < 2 ^ (prefixWord ++ tailWord_671004).sum := by decide
  have hdescent : baseEnd_671004 < baseStart_671004 := by decide
  rcases family_descends (prefixWord ++ tailWord_671004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671021 : List Nat := [1, 5, 3, 1, 1, 3, 1, 1, 1, 3, 3]
def baseStart_671021 : Nat := 118140960795 + 671021 * 2 ^ 59
def prefixEnd_671021 : Nat := 4983230072969 + 3 ^ 40 * 671021 * 2
def baseEnd_671021 : Nat := 344556302260724360951537

theorem tailTrace_671021 : CollatzResearch.WordTrace tailWord_671021 prefixEnd_671021 344556302260724360951537 := by
  unfold tailWord_671021
  simp only [CollatzResearch.WordTrace]
  refine ⟨24474146502012993108036917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16316097668008662072024611 24474146502012993108036917)
  ·
    refine ⟨2294451234563718103878461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24474146502012993108036917 2294451234563718103878461)
    ·
      refine ⟨860419212961394288954423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2294451234563718103878461 860419212961394288954423)
      ·
        refine ⟨1290628819442091433431635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 860419212961394288954423 1290628819442091433431635)
        ·
          refine ⟨1935943229163137150147453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1290628819442091433431635 1935943229163137150147453)
          ·
            refine ⟨725978710936176431305295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1935943229163137150147453 725978710936176431305295)
            ·
              refine ⟨1088968066404264646957943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 725978710936176431305295 1088968066404264646957943)
              ·
                refine ⟨1633452099606396970436915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1088968066404264646957943 1633452099606396970436915)
                ·
                  refine ⟨2450178149409595455655373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1633452099606396970436915 2450178149409595455655373)
                  ·
                    refine ⟨918816806028598295870765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2450178149409595455655373 918816806028598295870765)
                    ·
                      refine ⟨344556302260724360951537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 918816806028598295870765 344556302260724360951537)
                      ·
                        rfl

theorem cell23_671021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_671021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671021 prefixEnd_671021 := by exact prefixLift 671021
  have htrace : WordTrace (prefixWord ++ tailWord_671021) baseStart_671021 baseEnd_671021 := by
    simpa [prefixWord, tailWord_671021, baseEnd_671021] using wordTrace_append hprefix tailTrace_671021
  have hstable : (prefixWord ++ tailWord_671021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671021).length < 2 ^ (prefixWord ++ tailWord_671021).sum := by decide
  have hdescent : baseEnd_671021 < baseStart_671021 := by decide
  rcases family_descends (prefixWord ++ tailWord_671021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671060 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 1, 2, 7]
def baseStart_671060 : Nat := 118140960795 + 671060 * 2 ^ 59
def prefixEnd_671060 : Nat := 4983230072969 + 3 ^ 40 * 671060 * 2
def baseEnd_671060 : Nat := 344576328006249708363857

theorem tailTrace_671060 : CollatzResearch.WordTrace tailWord_671060 prefixEnd_671060 344576328006249708363857 := by
  unfold tailWord_671060
  simp only [CollatzResearch.WordTrace]
  refine ⟨12237784474435851384353317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16317045965914468512471089 12237784474435851384353317)
  ·
    refine ⟨2294584588956722134566247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12237784474435851384353317 2294584588956722134566247)
    ·
      refine ⟨3441876883435083201849371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2294584588956722134566247 3441876883435083201849371)
      ·
        refine ⟨5162815325152624802774057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3441876883435083201849371 5162815325152624802774057)
        ·
          refine ⟨3872111493864468602080543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5162815325152624802774057 3872111493864468602080543)
          ·
            refine ⟨5808167240796702903120815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3872111493864468602080543 5808167240796702903120815)
            ·
              refine ⟨8712250861195054354681223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5808167240796702903120815 8712250861195054354681223)
              ·
                refine ⟨13068376291792581532021835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8712250861195054354681223 13068376291792581532021835)
                ·
                  refine ⟨19602564437688872298032753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13068376291792581532021835 19602564437688872298032753)
                  ·
                    refine ⟨14701923328266654223524565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19602564437688872298032753 14701923328266654223524565)
                    ·
                      refine ⟨344576328006249708363857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 14701923328266654223524565 344576328006249708363857)
                      ·
                        rfl

theorem cell23_671060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_671060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671060 prefixEnd_671060 := by exact prefixLift 671060
  have htrace : WordTrace (prefixWord ++ tailWord_671060) baseStart_671060 baseEnd_671060 := by
    simpa [prefixWord, tailWord_671060, baseEnd_671060] using wordTrace_append hprefix tailTrace_671060
  have hstable : (prefixWord ++ tailWord_671060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671060).length < 2 ^ (prefixWord ++ tailWord_671060).sum := by decide
  have hdescent : baseEnd_671060 < baseStart_671060 := by decide
  rcases family_descends (prefixWord ++ tailWord_671060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671090 : List Nat := [3, 2, 1, 2, 1, 2, 1, 2, 1, 1, 7]
def baseStart_671090 : Nat := 118140960795 + 671090 * 2 ^ 59
def prefixEnd_671090 : Nat := 4983230072969 + 3 ^ 40 * 671090 * 2
def baseEnd_671090 : Nat := 344591732425884590988719

theorem tailTrace_671090 : CollatzResearch.WordTrace tailWord_671090 prefixEnd_671090 344591732425884590988719 := by
  unfold tailWord_671090
  simp only [CollatzResearch.WordTrace]
  refine ⟨6119165784690754473074681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16317775425842011928199149 6119165784690754473074681)
  ·
    refine ⟨4589374338518065854806011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6119165784690754473074681 4589374338518065854806011)
    ·
      refine ⟨6884061507777098782209017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4589374338518065854806011 6884061507777098782209017)
      ·
        refine ⟨5163046130832824086656763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6884061507777098782209017 5163046130832824086656763)
        ·
          refine ⟨7744569196249236129985145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5163046130832824086656763 7744569196249236129985145)
          ·
            refine ⟨5808426897186927097488859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7744569196249236129985145 5808426897186927097488859)
            ·
              refine ⟨8712640345780390646233289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5808426897186927097488859 8712640345780390646233289)
              ·
                refine ⟨6534480259335292984674967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8712640345780390646233289 6534480259335292984674967)
                ·
                  refine ⟨9801720389002939477012451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6534480259335292984674967 9801720389002939477012451)
                  ·
                    refine ⟨14702580583504409215518677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9801720389002939477012451 14702580583504409215518677)
                    ·
                      refine ⟨344591732425884590988719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 14702580583504409215518677 344591732425884590988719)
                      ·
                        rfl

theorem cell23_671090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_671090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671090 prefixEnd_671090 := by exact prefixLift 671090
  have htrace : WordTrace (prefixWord ++ tailWord_671090) baseStart_671090 baseEnd_671090 := by
    simpa [prefixWord, tailWord_671090, baseEnd_671090] using wordTrace_append hprefix tailTrace_671090
  have hstable : (prefixWord ++ tailWord_671090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671090).length < 2 ^ (prefixWord ++ tailWord_671090).sum := by decide
  have hdescent : baseEnd_671090 < baseStart_671090 := by decide
  rcases family_descends (prefixWord ++ tailWord_671090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671118 : List Nat := [4, 1, 1, 4, 2, 2, 2, 2, 5]
def baseStart_671118 : Nat := 118140960795 + 671118 * 2 ^ 59
def prefixEnd_671118 : Nat := 4983230072969 + 3 ^ 40 * 671118 * 2
def baseEnd_671118 : Nat := 38289567764912275715399

theorem tailTrace_671118 : CollatzResearch.WordTrace tailWord_671118 prefixEnd_671118 38289567764912275715399 := by
  unfold tailWord_671118
  simp only [CollatzResearch.WordTrace]
  refine ⟨3059710547832697334289751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16318456255107719116212005 3059710547832697334289751)
  ·
    refine ⟨4589565821749046001434627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3059710547832697334289751 4589565821749046001434627)
    ·
      refine ⟨6884348732623569002151941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4589565821749046001434627 6884348732623569002151941)
      ·
        refine ⟨1290815387366919187903489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6884348732623569002151941 1290815387366919187903489)
        ·
          refine ⟨968111540525189390927617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1290815387366919187903489 968111540525189390927617)
          ·
            refine ⟨726083655393892043195713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 968111540525189390927617 726083655393892043195713)
            ·
              refine ⟨544562741545419032396785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 726083655393892043195713 544562741545419032396785)
              ·
                refine ⟨408422056159064274297589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 544562741545419032396785 408422056159064274297589)
                ·
                  refine ⟨38289567764912275715399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 408422056159064274297589 38289567764912275715399)
                  ·
                    rfl

theorem cell23_671118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 2, 5].length) (baseStart_671118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671118 prefixEnd_671118 := by exact prefixLift 671118
  have htrace : WordTrace (prefixWord ++ tailWord_671118) baseStart_671118 baseEnd_671118 := by
    simpa [prefixWord, tailWord_671118, baseEnd_671118] using wordTrace_append hprefix tailTrace_671118
  have hstable : (prefixWord ++ tailWord_671118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671118).length < 2 ^ (prefixWord ++ tailWord_671118).sum := by decide
  have hdescent : baseEnd_671118 < baseStart_671118 := by decide
  rcases family_descends (prefixWord ++ tailWord_671118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671127 : List Nat := [1, 1, 3, 3, 1, 1, 1, 5, 3, 4]
def baseStart_671127 : Nat := 118140960795 + 671127 * 2 ^ 59
def prefixEnd_671127 : Nat := 4983230072969 + 3 ^ 40 * 671127 * 2
def baseEnd_671127 : Nat := 114870243736700315408683

theorem tailTrace_671127 : CollatzResearch.WordTrace tailWord_671127 prefixEnd_671127 114870243736700315408683 := by
  unfold tailWord_671127
  simp only [CollatzResearch.WordTrace]
  refine ⟨24478012639628973211395635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16318675093085982140930423 24478012639628973211395635)
  ·
    refine ⟨36717018959443459817093453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24478012639628973211395635 36717018959443459817093453)
    ·
      refine ⟨13768882109791297431410045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36717018959443459817093453 13768882109791297431410045)
      ·
        refine ⟨5163330791171736536778767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13768882109791297431410045 5163330791171736536778767)
        ·
          refine ⟨7744996186757604805168151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5163330791171736536778767 7744996186757604805168151)
          ·
            refine ⟨11617494280136407207752227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7744996186757604805168151 11617494280136407207752227)
            ·
              refine ⟨17426241420204610811628341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11617494280136407207752227 17426241420204610811628341)
              ·
                refine ⟨1633710133144182263590157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17426241420204610811628341 1633710133144182263590157)
                ·
                  refine ⟨612641299929068348846309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1633710133144182263590157 612641299929068348846309)
                  ·
                    refine ⟨114870243736700315408683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 612641299929068348846309 114870243736700315408683)
                    ·
                      rfl

theorem cell23_671127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 3, 4].length) (baseStart_671127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671127 prefixEnd_671127 := by exact prefixLift 671127
  have htrace : WordTrace (prefixWord ++ tailWord_671127) baseStart_671127 baseEnd_671127 := by
    simpa [prefixWord, tailWord_671127, baseEnd_671127] using wordTrace_append hprefix tailTrace_671127
  have hstable : (prefixWord ++ tailWord_671127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671127).length < 2 ^ (prefixWord ++ tailWord_671127).sum := by decide
  have hdescent : baseEnd_671127 < baseStart_671127 := by decide
  rcases family_descends (prefixWord ++ tailWord_671127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671140 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 10]
def baseStart_671140 : Nat := 118140960795 + 671140 * 2 ^ 59
def prefixEnd_671140 : Nat := 4983230072969 + 3 ^ 40 * 671140 * 2
def baseEnd_671140 : Nat := 38290822939845488373721

theorem tailTrace_671140 : CollatzResearch.WordTrace tailWord_671140 prefixEnd_671140 38290822939845488373721 := by
  unfold tailWord_671140
  simp only [CollatzResearch.WordTrace]
  refine ⟨12239243394290938215809437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16318991192387917621079249 12239243394290938215809437)
  ·
    refine ⟨4589716272859101830928539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12239243394290938215809437 4589716272859101830928539)
    ·
      refine ⟨6884574409288652746392809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4589716272859101830928539 6884574409288652746392809)
      ·
        refine ⟨5163430806966489559794607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6884574409288652746392809 5163430806966489559794607)
        ·
          refine ⟨7745146210449734339691911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5163430806966489559794607 7745146210449734339691911)
          ·
            refine ⟨11617719315674601509537867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7745146210449734339691911 11617719315674601509537867)
            ·
              refine ⟨17426578973511902264306801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11617719315674601509537867 17426578973511902264306801)
              ·
                refine ⟨13069934230133926698230101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17426578973511902264306801 13069934230133926698230101)
                ·
                  refine ⟨38290822939845488373721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 13069934230133926698230101 38290822939845488373721)
                  ·
                    rfl

theorem cell23_671140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 10].length) (baseStart_671140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671140 prefixEnd_671140 := by exact prefixLift 671140
  have htrace : WordTrace (prefixWord ++ tailWord_671140) baseStart_671140 baseEnd_671140 := by
    simpa [prefixWord, tailWord_671140, baseEnd_671140] using wordTrace_append hprefix tailTrace_671140
  have hstable : (prefixWord ++ tailWord_671140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671140).length < 2 ^ (prefixWord ++ tailWord_671140).sum := by decide
  have hdescent : baseEnd_671140 < baseStart_671140 := by decide
  rcases family_descends (prefixWord ++ tailWord_671140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671194 : List Nat := [3, 1, 1, 2, 3, 2, 1, 2, 1, 5, 2]
def baseStart_671194 : Nat := 118140960795 + 671194 * 2 ^ 59
def prefixEnd_671194 : Nat := 4983230072969 + 3 ^ 40 * 671194 * 2
def baseEnd_671194 : Nat := 344645134413952184088241

theorem tailTrace_671194 : CollatzResearch.WordTrace tailWord_671194 prefixEnd_671194 344645134413952184088241 := by
  unfold tailWord_671194
  simp only [CollatzResearch.WordTrace]
  refine ⟨6120114082596560913521159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16320304220257495769389757 6120114082596560913521159)
  ·
    refine ⟨9180171123894841370281739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6120114082596560913521159 9180171123894841370281739)
    ·
      refine ⟨13770256685842262055422609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9180171123894841370281739 13770256685842262055422609)
      ·
        refine ⟨10327692514381696541566957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13770256685842262055422609 10327692514381696541566957)
        ·
          refine ⟨3872884692893136203087609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10327692514381696541566957 3872884692893136203087609)
          ·
            refine ⟨2904663519669852152315707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3872884692893136203087609 2904663519669852152315707)
            ·
              refine ⟨4356995279504778228473561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2904663519669852152315707 4356995279504778228473561)
              ·
                refine ⟨3267746459628583671355171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4356995279504778228473561 3267746459628583671355171)
                ·
                  refine ⟨4901619689442875507032757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3267746459628583671355171 4901619689442875507032757)
                  ·
                    refine ⟨459526845885269578784321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4901619689442875507032757 459526845885269578784321)
                    ·
                      refine ⟨344645134413952184088241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 459526845885269578784321 344645134413952184088241)
                      ·
                        rfl

theorem cell23_671194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 1, 5, 2].length) (baseStart_671194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671194 prefixEnd_671194 := by exact prefixLift 671194
  have htrace : WordTrace (prefixWord ++ tailWord_671194) baseStart_671194 baseEnd_671194 := by
    simpa [prefixWord, tailWord_671194, baseEnd_671194] using wordTrace_append hprefix tailTrace_671194
  have hstable : (prefixWord ++ tailWord_671194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671194).length < 2 ^ (prefixWord ++ tailWord_671194).sum := by decide
  have hdescent : baseEnd_671194 < baseStart_671194 := by decide
  rcases family_descends (prefixWord ++ tailWord_671194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671221 : List Nat := [1, 3, 5, 1, 1, 1, 2, 3, 1, 5]
def baseStart_671221 : Nat := 118140960795 + 671221 * 2 ^ 59
def prefixEnd_671221 : Nat := 4983230072969 + 3 ^ 40 * 671221 * 2
def baseEnd_671221 : Nat := 114886332797207859483539

theorem tailTrace_671221 : CollatzResearch.WordTrace tailWord_671221 prefixEnd_671221 114886332797207859483539 := by
  unfold tailWord_671221
  simp only [CollatzResearch.WordTrace]
  refine ⟨24481441101288427265317517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16320960734192284843545011 24481441101288427265317517)
  ·
    refine ⟨9180540412983160224494069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24481441101288427265317517 9180540412983160224494069)
    ·
      refine ⟨860675663717171271046319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9180540412983160224494069 860675663717171271046319)
      ·
        refine ⟨1291013495575756906569479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 860675663717171271046319 1291013495575756906569479)
        ·
          refine ⟨1936520243363635359854219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1291013495575756906569479 1936520243363635359854219)
          ·
            refine ⟨2904780365045453039781329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1936520243363635359854219 2904780365045453039781329)
            ·
              refine ⟨2178585273784089779835997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2904780365045453039781329 2178585273784089779835997)
              ·
                refine ⟨816969477669033667438499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2178585273784089779835997 816969477669033667438499)
                ·
                  refine ⟨1225454216503550501157749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 816969477669033667438499 1225454216503550501157749)
                  ·
                    refine ⟨114886332797207859483539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1225454216503550501157749 114886332797207859483539)
                    ·
                      rfl

theorem cell23_671221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_671221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671221 prefixEnd_671221 := by exact prefixLift 671221
  have htrace : WordTrace (prefixWord ++ tailWord_671221) baseStart_671221 baseEnd_671221 := by
    simpa [prefixWord, tailWord_671221, baseEnd_671221] using wordTrace_append hprefix tailTrace_671221
  have hstable : (prefixWord ++ tailWord_671221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671221).length < 2 ^ (prefixWord ++ tailWord_671221).sum := by decide
  have hdescent : baseEnd_671221 < baseStart_671221 := by decide
  rcases family_descends (prefixWord ++ tailWord_671221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671224 : List Nat := [2, 1, 2, 1, 1, 5, 2, 3, 1, 1, 4]
def baseStart_671224 : Nat := 118140960795 + 671224 * 2 ^ 59
def prefixEnd_671224 : Nat := 4983230072969 + 3 ^ 40 * 671224 * 2
def baseEnd_671224 : Nat := 344660538833587066713103

theorem tailTrace_671224 : CollatzResearch.WordTrace tailWord_671224 prefixEnd_671224 344660538833587066713103 := by
  unfold tailWord_671224
  simp only [CollatzResearch.WordTrace]
  refine ⟨12240775260138779388838363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16321033680185039185117817 12240775260138779388838363)
  ·
    refine ⟨18361162890208169083257545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12240775260138779388838363 18361162890208169083257545)
    ·
      refine ⟨13770872167656126812443159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18361162890208169083257545 13770872167656126812443159)
      ·
        refine ⟨20656308251484190218664739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13770872167656126812443159 20656308251484190218664739)
        ·
          refine ⟨30984462377226285327997109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20656308251484190218664739 30984462377226285327997109)
          ·
            refine ⟨2904793347864964249499729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30984462377226285327997109 2904793347864964249499729)
            ·
              refine ⟨2178595010898723187124797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2904793347864964249499729 2178595010898723187124797)
              ·
                refine ⟨816973129087021195171799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2178595010898723187124797 816973129087021195171799)
                ·
                  refine ⟨1225459693630531792757699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 816973129087021195171799 1225459693630531792757699)
                  ·
                    refine ⟨1838189540445797689136549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1225459693630531792757699 1838189540445797689136549)
                    ·
                      refine ⟨344660538833587066713103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1838189540445797689136549 344660538833587066713103)
                      ·
                        rfl

theorem cell23_671224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 1, 1, 4].length) (baseStart_671224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671224 prefixEnd_671224 := by exact prefixLift 671224
  have htrace : WordTrace (prefixWord ++ tailWord_671224) baseStart_671224 baseEnd_671224 := by
    simpa [prefixWord, tailWord_671224, baseEnd_671224] using wordTrace_append hprefix tailTrace_671224
  have hstable : (prefixWord ++ tailWord_671224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671224).length < 2 ^ (prefixWord ++ tailWord_671224).sum := by decide
  have hdescent : baseEnd_671224 < baseStart_671224 := by decide
  rcases family_descends (prefixWord ++ tailWord_671224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671251 : List Nat := [1, 1, 1, 2, 1, 6, 4, 1, 2, 4]
def baseStart_671251 : Nat := 118140960795 + 671251 * 2 ^ 59
def prefixEnd_671251 : Nat := 4983230072969 + 3 ^ 40 * 671251 * 2
def baseEnd_671251 : Nat := 114891467603752820358493

theorem tailTrace_671251 : CollatzResearch.WordTrace tailWord_671251 prefixEnd_671251 114891467603752820358493 := by
  unfold tailWord_671251
  simp only [CollatzResearch.WordTrace]
  refine ⟨24482535291179742388909607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16321690194119828259273071 24482535291179742388909607)
  ·
    refine ⟨36723802936769613583364411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24482535291179742388909607 36723802936769613583364411)
    ·
      refine ⟨55085704405154420375046617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36723802936769613583364411 55085704405154420375046617)
      ·
        refine ⟨41314278303865815281284963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55085704405154420375046617 41314278303865815281284963)
        ·
          refine ⟨61971417455798722921927445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41314278303865815281284963 61971417455798722921927445)
          ·
            refine ⟨2904910193240565136965349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 61971417455798722921927445 2904910193240565136965349)
            ·
              refine ⟨544670661232605963181003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2904910193240565136965349 544670661232605963181003)
              ·
                refine ⟨817005991848908944771505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 544670661232605963181003 817005991848908944771505)
                ·
                  refine ⟨612754493886681708578629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 817005991848908944771505 612754493886681708578629)
                  ·
                    refine ⟨114891467603752820358493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 612754493886681708578629 114891467603752820358493)
                    ·
                      rfl

theorem cell23_671251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 2, 4].length) (baseStart_671251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671251 prefixEnd_671251 := by exact prefixLift 671251
  have htrace : WordTrace (prefixWord ++ tailWord_671251) baseStart_671251 baseEnd_671251 := by
    simpa [prefixWord, tailWord_671251, baseEnd_671251] using wordTrace_append hprefix tailTrace_671251
  have hstable : (prefixWord ++ tailWord_671251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671251).length < 2 ^ (prefixWord ++ tailWord_671251).sum := by decide
  have hdescent : baseEnd_671251 < baseStart_671251 := by decide
  rcases family_descends (prefixWord ++ tailWord_671251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671331 : List Nat := [1, 1, 1, 5, 1, 3, 2, 2, 1, 4, 2]
def baseStart_671331 : Nat := 118140960795 + 671331 * 2 ^ 59
def prefixEnd_671331 : Nat := 4983230072969 + 3 ^ 40 * 671331 * 2
def baseEnd_671331 : Nat := 344715481263618148075111

theorem tailTrace_671331 : CollatzResearch.WordTrace tailWord_671331 prefixEnd_671331 344715481263618148075111 := by
  unfold tailWord_671331
  simp only [CollatzResearch.WordTrace]
  refine ⟨24485453130889916051821847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16323635420593277367881231 24485453130889916051821847)
  ·
    refine ⟨36728179696334874077732771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24485453130889916051821847 36728179696334874077732771)
    ·
      refine ⟨55092269544502311116599157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36728179696334874077732771 55092269544502311116599157)
      ·
        refine ⟨5164900269797091667181171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55092269544502311116599157 5164900269797091667181171)
        ·
          refine ⟨7747350404695637500771757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5164900269797091667181171 7747350404695637500771757)
          ·
            refine ⟨2905256401760864062789409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7747350404695637500771757 2905256401760864062789409)
            ·
              refine ⟨2178942301320648047092057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2905256401760864062789409 2178942301320648047092057)
              ·
                refine ⟨1634206725990486035319043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2178942301320648047092057 1634206725990486035319043)
                ·
                  refine ⟨2451310088985729052978565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1634206725990486035319043 2451310088985729052978565)
                  ·
                    refine ⟨459620641684824197433481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2451310088985729052978565 459620641684824197433481)
                    ·
                      refine ⟨344715481263618148075111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 459620641684824197433481 344715481263618148075111)
                      ·
                        rfl

theorem cell23_671331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_671331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671331 prefixEnd_671331 := by exact prefixLift 671331
  have htrace : WordTrace (prefixWord ++ tailWord_671331) baseStart_671331 baseEnd_671331 := by
    simpa [prefixWord, tailWord_671331, baseEnd_671331] using wordTrace_append hprefix tailTrace_671331
  have hstable : (prefixWord ++ tailWord_671331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671331).length < 2 ^ (prefixWord ++ tailWord_671331).sum := by decide
  have hdescent : baseEnd_671331 < baseStart_671331 := by decide
  rcases family_descends (prefixWord ++ tailWord_671331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671342 : List Nat := [4, 1, 2, 2, 4, 1, 1, 2, 2, 1, 3]
def baseStart_671342 : Nat := 118140960795 + 671342 * 2 ^ 59
def prefixEnd_671342 : Nat := 4983230072969 + 3 ^ 40 * 671342 * 2
def baseEnd_671342 : Nat := 344721129550817605037561

theorem tailTrace_671342 : CollatzResearch.WordTrace tailWord_671342 prefixEnd_671342 344721129550817605037561 := by
  unfold tailWord_671342
  simp only [CollatzResearch.WordTrace]
  refine ⟨3060731791731258116309035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16323902889233376620314853 3060731791731258116309035)
  ·
    refine ⟨4591097687596887174463553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3060731791731258116309035 4591097687596887174463553)
    ·
      refine ⟨3443323265697665380847665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4591097687596887174463553 3443323265697665380847665)
      ·
        refine ⟨2582492449273249035635749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3443323265697665380847665 2582492449273249035635749)
        ·
          refine ⟨484217334238734194181703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2582492449273249035635749 484217334238734194181703)
          ·
            refine ⟨726326001358101291272555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484217334238734194181703 726326001358101291272555)
            ·
              refine ⟨1089489002037151936908833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 726326001358101291272555 1089489002037151936908833)
              ·
                refine ⟨817116751527863952681625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1089489002037151936908833 817116751527863952681625)
                ·
                  refine ⟨612837563645897964511219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 817116751527863952681625 612837563645897964511219)
                  ·
                    refine ⟨919256345468846946766829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 612837563645897964511219 919256345468846946766829)
                    ·
                      refine ⟨344721129550817605037561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 919256345468846946766829 344721129550817605037561)
                      ·
                        rfl

theorem cell23_671342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_671342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671342 prefixEnd_671342 := by exact prefixLift 671342
  have htrace : WordTrace (prefixWord ++ tailWord_671342) baseStart_671342 baseEnd_671342 := by
    simpa [prefixWord, tailWord_671342, baseEnd_671342] using wordTrace_append hprefix tailTrace_671342
  have hstable : (prefixWord ++ tailWord_671342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671342).length < 2 ^ (prefixWord ++ tailWord_671342).sum := by decide
  have hdescent : baseEnd_671342 < baseStart_671342 := by decide
  rcases family_descends (prefixWord ++ tailWord_671342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671344 : List Nat := [2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 4]
def baseStart_671344 : Nat := 118140960795 + 671344 * 2 ^ 59
def prefixEnd_671344 : Nat := 4983230072969 + 3 ^ 40 * 671344 * 2
def baseEnd_671344 : Nat := 344722156512126597212551

theorem tailTrace_671344 : CollatzResearch.WordTrace tailWord_671344 prefixEnd_671344 344722156512126597212551 := by
  unfold tailWord_671344
  simp only [CollatzResearch.WordTrace]
  refine ⟨12242963639921409636022543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16323951519895212848030057 12242963639921409636022543)
  ·
    refine ⟨18364445459882114454033815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12242963639921409636022543 18364445459882114454033815)
    ·
      refine ⟨27546668189823171681050723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18364445459882114454033815 27546668189823171681050723)
      ·
        refine ⟨41320002284734757521576085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27546668189823171681050723 41320002284734757521576085)
        ·
          refine ⟨1936875107096941758823879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41320002284734757521576085 1936875107096941758823879)
          ·
            refine ⟨2905312660645412638235819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1936875107096941758823879 2905312660645412638235819)
            ·
              refine ⟨4357968990968118957353729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2905312660645412638235819 4357968990968118957353729)
              ·
                refine ⟨3268476743226089218015297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4357968990968118957353729 3268476743226089218015297)
                ·
                  refine ⟨2451357557419566913511473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3268476743226089218015297 2451357557419566913511473)
                  ·
                    refine ⟨1838518168064675185133605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2451357557419566913511473 1838518168064675185133605)
                    ·
                      refine ⟨344722156512126597212551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1838518168064675185133605 344722156512126597212551)
                      ·
                        rfl

theorem cell23_671344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 4].length) (baseStart_671344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671344 prefixEnd_671344 := by exact prefixLift 671344
  have htrace : WordTrace (prefixWord ++ tailWord_671344) baseStart_671344 baseEnd_671344 := by
    simpa [prefixWord, tailWord_671344, baseEnd_671344] using wordTrace_append hprefix tailTrace_671344
  have hstable : (prefixWord ++ tailWord_671344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671344).length < 2 ^ (prefixWord ++ tailWord_671344).sum := by decide
  have hdescent : baseEnd_671344 < baseStart_671344 := by decide
  rcases family_descends (prefixWord ++ tailWord_671344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671365 : List Nat := [1, 3, 1, 1, 4, 1, 5, 1, 2, 2, 2]
def baseStart_671365 : Nat := 118140960795 + 671365 * 2 ^ 59
def prefixEnd_671365 : Nat := 4983230072969 + 3 ^ 40 * 671365 * 2
def baseEnd_671365 : Nat := 344732939605871015049955

theorem tailTrace_671365 : CollatzResearch.WordTrace tailWord_671365 prefixEnd_671365 344732939605871015049955 := by
  unfold tailWord_671365
  simp only [CollatzResearch.WordTrace]
  refine ⟨24486693212766739858559549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16324462141844493239039699 24486693212766739858559549)
  ·
    refine ⟨9182509954787527446959831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24486693212766739858559549 9182509954787527446959831)
    ·
      refine ⟨13773764932181291170439747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9182509954787527446959831 13773764932181291170439747)
      ·
        refine ⟨20660647398271936755659621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13773764932181291170439747 20660647398271936755659621)
        ·
          refine ⟨3873871387175988141686179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20660647398271936755659621 3873871387175988141686179)
          ·
            refine ⟨5810807080763982212529269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3873871387175988141686179 5810807080763982212529269)
            ·
              refine ⟨544763163821623332424619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5810807080763982212529269 544763163821623332424619)
              ·
                refine ⟨817144745732434998636929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 544763163821623332424619 817144745732434998636929)
                ·
                  refine ⟨612858559299326248977697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 817144745732434998636929 612858559299326248977697)
                  ·
                    refine ⟨459643919474494686733273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 612858559299326248977697 459643919474494686733273)
                    ·
                      refine ⟨344732939605871015049955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 459643919474494686733273 344732939605871015049955)
                      ·
                        rfl

theorem cell23_671365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 2, 2, 2].length) (baseStart_671365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671365 prefixEnd_671365 := by exact prefixLift 671365
  have htrace : WordTrace (prefixWord ++ tailWord_671365) baseStart_671365 baseEnd_671365 := by
    simpa [prefixWord, tailWord_671365, baseEnd_671365] using wordTrace_append hprefix tailTrace_671365
  have hstable : (prefixWord ++ tailWord_671365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671365).length < 2 ^ (prefixWord ++ tailWord_671365).sum := by decide
  have hdescent : baseEnd_671365 < baseStart_671365 := by decide
  rcases family_descends (prefixWord ++ tailWord_671365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671377 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 7]
def baseStart_671377 : Nat := 118140960795 + 671377 * 2 ^ 59
def prefixEnd_671377 : Nat := 4983230072969 + 3 ^ 40 * 671377 * 2
def baseEnd_671377 : Nat := 344739101373724968099899

theorem tailTrace_671377 : CollatzResearch.WordTrace tailWord_671377 prefixEnd_671377 344739101373724968099899 := by
  unfold tailWord_671377
  simp only [CollatzResearch.WordTrace]
  refine ⟨24487130888723265907996385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16324753925815510605330923 24487130888723265907996385)
  ·
    refine ⟨18365348166542449430997289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24487130888723265907996385 18365348166542449430997289)
    ·
      refine ⟨13774011124906837073247967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18365348166542449430997289 13774011124906837073247967)
      ·
        refine ⟨20661016687360255609871951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13774011124906837073247967 20661016687360255609871951)
        ·
          refine ⟨30991525031040383414807927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20661016687360255609871951 30991525031040383414807927)
          ·
            refine ⟨46487287546560575122211891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30991525031040383414807927 46487287546560575122211891)
            ·
              refine ⟨69730931319840862683317837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46487287546560575122211891 69730931319840862683317837)
              ·
                refine ⟨26149099244940323506244189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69730931319840862683317837 26149099244940323506244189)
                ·
                  refine ⟨9805912216852621314841571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26149099244940323506244189 9805912216852621314841571)
                  ·
                    refine ⟨14708868325278931972262357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9805912216852621314841571 14708868325278931972262357)
                    ·
                      refine ⟨344739101373724968099899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 14708868325278931972262357 344739101373724968099899)
                      ·
                        rfl

theorem cell23_671377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_671377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671377 prefixEnd_671377 := by exact prefixLift 671377
  have htrace : WordTrace (prefixWord ++ tailWord_671377) baseStart_671377 baseEnd_671377 := by
    simpa [prefixWord, tailWord_671377, baseEnd_671377] using wordTrace_append hprefix tailTrace_671377
  have hstable : (prefixWord ++ tailWord_671377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671377).length < 2 ^ (prefixWord ++ tailWord_671377).sum := by decide
  have hdescent : baseEnd_671377 < baseStart_671377 := by decide
  rcases family_descends (prefixWord ++ tailWord_671377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671384 : List Nat := [2, 1, 2, 4, 1, 2, 2, 1, 1, 7]
def baseStart_671384 : Nat := 118140960795 + 671384 * 2 ^ 59
def prefixEnd_671384 : Nat := 4983230072969 + 3 ^ 40 * 671384 * 2
def baseEnd_671384 : Nat := 114914231912768813570789

theorem tailTrace_671384 : CollatzResearch.WordTrace tailWord_671384 prefixEnd_671384 114914231912768813570789 := by
  unfold tailWord_671384
  simp only [CollatzResearch.WordTrace]
  refine ⟨12243693099848953051750603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16324924133131937402334137 12243693099848953051750603)
  ·
    refine ⟨18365539649773429577625905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12243693099848953051750603 18365539649773429577625905)
    ·
      refine ⟨13774154737330072183219429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18365539649773429577625905 13774154737330072183219429)
      ·
        refine ⟨2582654013249388534353643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13774154737330072183219429 2582654013249388534353643)
        ·
          refine ⟨3873981019874082801530465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2582654013249388534353643 3873981019874082801530465)
          ·
            refine ⟨2905485764905562101147849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3873981019874082801530465 2905485764905562101147849)
            ·
              refine ⟨2179114323679171575860887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2905485764905562101147849 2179114323679171575860887)
              ·
                refine ⟨3268671485518757363791331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2179114323679171575860887 3268671485518757363791331)
                ·
                  refine ⟨4903007228278136045686997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3268671485518757363791331 4903007228278136045686997)
                  ·
                    refine ⟨114914231912768813570789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4903007228278136045686997 114914231912768813570789)
                    ·
                      rfl

theorem cell23_671384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 1, 7].length) (baseStart_671384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671384 prefixEnd_671384 := by exact prefixLift 671384
  have htrace : WordTrace (prefixWord ++ tailWord_671384) baseStart_671384 baseEnd_671384 := by
    simpa [prefixWord, tailWord_671384, baseEnd_671384] using wordTrace_append hprefix tailTrace_671384
  have hstable : (prefixWord ++ tailWord_671384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671384).length < 2 ^ (prefixWord ++ tailWord_671384).sum := by decide
  have hdescent : baseEnd_671384 < baseStart_671384 := by decide
  rcases family_descends (prefixWord ++ tailWord_671384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671421 : List Nat := [1, 4, 1, 2, 1, 2, 2, 1, 1, 6, 2]
def baseStart_671421 : Nat := 118140960795 + 671421 * 2 ^ 59
def prefixEnd_671421 : Nat := 4983230072969 + 3 ^ 40 * 671421 * 2
def baseEnd_671421 : Nat := 344761694522522795949697

theorem tailTrace_671421 : CollatzResearch.WordTrace tailWord_671421 prefixEnd_671421 344761694522522795949697 := by
  unfold tailWord_671421
  simp only [CollatzResearch.WordTrace]
  refine ⟨24488735700563861422598117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16325823800375907615065411 24488735700563861422598117)
  ·
    refine ⟨4591637943855724016737147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24488735700563861422598117 4591637943855724016737147)
    ·
      refine ⟨6887456915783586025105721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4591637943855724016737147 6887456915783586025105721)
      ·
        refine ⟨5165592686837689518829291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6887456915783586025105721 5165592686837689518829291)
        ·
          refine ⟨7748389030256534278243937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5165592686837689518829291 7748389030256534278243937)
          ·
            refine ⟨5811291772692400708682953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7748389030256534278243937 5811291772692400708682953)
            ·
              refine ⟨4358468829519300531512215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5811291772692400708682953 4358468829519300531512215)
              ·
                refine ⟨6537703244278950797268323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4358468829519300531512215 6537703244278950797268323)
                ·
                  refine ⟨9806554866418426195902485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6537703244278950797268323 9806554866418426195902485)
                  ·
                    refine ⟨459682259363363727932929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9806554866418426195902485 459682259363363727932929)
                    ·
                      refine ⟨344761694522522795949697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 459682259363363727932929 344761694522522795949697)
                      ·
                        rfl

theorem cell23_671421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_671421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671421 prefixEnd_671421 := by exact prefixLift 671421
  have htrace : WordTrace (prefixWord ++ tailWord_671421) baseStart_671421 baseEnd_671421 := by
    simpa [prefixWord, tailWord_671421, baseEnd_671421] using wordTrace_append hprefix tailTrace_671421
  have hstable : (prefixWord ++ tailWord_671421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671421).length < 2 ^ (prefixWord ++ tailWord_671421).sum := by decide
  have hdescent : baseEnd_671421 < baseStart_671421 := by decide
  rcases family_descends (prefixWord ++ tailWord_671421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671441 : List Nat := [1, 2, 2, 1, 2, 4, 1, 3, 2, 2, 3]
def baseStart_671441 : Nat := 118140960795 + 671441 * 2 ^ 59
def prefixEnd_671441 : Nat := 4983230072969 + 3 ^ 40 * 671441 * 2
def baseEnd_671441 : Nat := 344771964135612717699605

theorem tailTrace_671441 : CollatzResearch.WordTrace tailWord_671441 prefixEnd_671441 344771964135612717699605 := by
  unfold tailWord_671441
  simp only [CollatzResearch.WordTrace]
  refine ⟨24489465160491404838326177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16326310106994269892217451 24489465160491404838326177)
  ·
    refine ⟨18367098870368553628744633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24489465160491404838326177 18367098870368553628744633)
    ·
      refine ⟨13775324152776415221558475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18367098870368553628744633 13775324152776415221558475)
      ·
        refine ⟨20662986229164622832337713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13775324152776415221558475 20662986229164622832337713)
        ·
          refine ⟨15497239671873467124253285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20662986229164622832337713 15497239671873467124253285)
          ·
            refine ⟨2905732438476275085797491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15497239671873467124253285 2905732438476275085797491)
            ·
              refine ⟨4358598657714412628696237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2905732438476275085797491 4358598657714412628696237)
              ·
                refine ⟨1634474496642904735761089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4358598657714412628696237 1634474496642904735761089)
                ·
                  refine ⟨1225855872482178551820817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1634474496642904735761089 1225855872482178551820817)
                  ·
                    refine ⟨919391904361633913865613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1225855872482178551820817 919391904361633913865613)
                    ·
                      refine ⟨344771964135612717699605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 919391904361633913865613 344771964135612717699605)
                      ·
                        rfl

theorem cell23_671441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 2, 3].length) (baseStart_671441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671441 prefixEnd_671441 := by exact prefixLift 671441
  have htrace : WordTrace (prefixWord ++ tailWord_671441) baseStart_671441 baseEnd_671441 := by
    simpa [prefixWord, tailWord_671441, baseEnd_671441] using wordTrace_append hprefix tailTrace_671441
  have hstable : (prefixWord ++ tailWord_671441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671441).length < 2 ^ (prefixWord ++ tailWord_671441).sum := by decide
  have hdescent : baseEnd_671441 < baseStart_671441 := by decide
  rcases family_descends (prefixWord ++ tailWord_671441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671448 : List Nat := [2, 1, 2, 2, 3, 1, 2, 5, 1, 4]
def baseStart_671448 : Nat := 118140960795 + 671448 * 2 ^ 59
def prefixEnd_671448 : Nat := 4983230072969 + 3 ^ 40 * 671448 * 2
def baseEnd_671448 : Nat := 114925186166731396770691

theorem tailTrace_671448 : CollatzResearch.WordTrace tailWord_671448 prefixEnd_671448 114925186166731396770691 := by
  unfold tailWord_671448
  simp only [CollatzResearch.WordTrace]
  refine ⟨12244860235733022516915499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16326480314310696689220665 12244860235733022516915499)
  ·
    refine ⟨18367290353599533775373249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12244860235733022516915499 18367290353599533775373249)
    ·
      refine ⟨13775467765199650331529937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18367290353599533775373249 13775467765199650331529937)
      ·
        refine ⟨10331600823899737748647453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13775467765199650331529937 10331600823899737748647453)
        ·
          refine ⟨3874350308962401655742795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10331600823899737748647453 3874350308962401655742795)
          ·
            refine ⟨5811525463443602483614193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3874350308962401655742795 5811525463443602483614193)
            ·
              refine ⟨4358644097582701862710645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5811525463443602483614193 4358644097582701862710645)
              ·
                refine ⟨408622884148378299629123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4358644097582701862710645 408622884148378299629123)
                ·
                  refine ⟨612934326222567449443685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 408622884148378299629123 612934326222567449443685)
                  ·
                    refine ⟨114925186166731396770691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 612934326222567449443685 114925186166731396770691)
                    ·
                      rfl

theorem cell23_671448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 5, 1, 4].length) (baseStart_671448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671448 prefixEnd_671448 := by exact prefixLift 671448
  have htrace : WordTrace (prefixWord ++ tailWord_671448) baseStart_671448 baseEnd_671448 := by
    simpa [prefixWord, tailWord_671448, baseEnd_671448] using wordTrace_append hprefix tailTrace_671448
  have hstable : (prefixWord ++ tailWord_671448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671448).length < 2 ^ (prefixWord ++ tailWord_671448).sum := by decide
  have hdescent : baseEnd_671448 < baseStart_671448 := by decide
  rcases family_descends (prefixWord ++ tailWord_671448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671461 : List Nat := [1, 3, 1, 4, 1, 1, 4, 2, 6]
def baseStart_671461 : Nat := 118140960795 + 671461 * 2 ^ 59
def prefixEnd_671461 : Nat := 4983230072969 + 3 ^ 40 * 671461 * 2
def baseEnd_671461 : Nat := 38309137083189182161057

theorem tailTrace_671461 : CollatzResearch.WordTrace tailWord_671461 prefixEnd_671461 38309137083189182161057 := by
  unfold tailWord_671461
  simp only [CollatzResearch.WordTrace]
  refine ⟨24490194620418948254054237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16326796413612632169369491 24490194620418948254054237)
  ·
    refine ⟨9183822982657105595270339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24490194620418948254054237 9183822982657105595270339)
    ·
      refine ⟨13775734473985658392905509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9183822982657105595270339 13775734473985658392905509)
      ·
        refine ⟨2582950213872310948669783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13775734473985658392905509 2582950213872310948669783)
        ·
          refine ⟨3874425320808466423004675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2582950213872310948669783 3874425320808466423004675)
          ·
            refine ⟨5811637981212699634507013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3874425320808466423004675 5811637981212699634507013)
            ·
              refine ⟨1089682121477381181470065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5811637981212699634507013 1089682121477381181470065)
              ·
                refine ⟨817261591108035886102549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1089682121477381181470065 817261591108035886102549)
                ·
                  refine ⟨38309137083189182161057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 817261591108035886102549 38309137083189182161057)
                  ·
                    rfl

theorem cell23_671461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 6].length) (baseStart_671461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671461 prefixEnd_671461 := by exact prefixLift 671461
  have htrace : WordTrace (prefixWord ++ tailWord_671461) baseStart_671461 baseEnd_671461 := by
    simpa [prefixWord, tailWord_671461, baseEnd_671461] using wordTrace_append hprefix tailTrace_671461
  have hstable : (prefixWord ++ tailWord_671461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671461).length < 2 ^ (prefixWord ++ tailWord_671461).sum := by decide
  have hdescent : baseEnd_671461 < baseStart_671461 := by decide
  rcases family_descends (prefixWord ++ tailWord_671461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671484 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 2, 1, 7]
def baseStart_671484 : Nat := 118140960795 + 671484 * 2 ^ 59
def prefixEnd_671484 : Nat := 4983230072969 + 3 ^ 40 * 671484 * 2
def baseEnd_671484 : Nat := 344794043803756049461907

theorem tailTrace_671484 : CollatzResearch.WordTrace tailWord_671484 prefixEnd_671484 344794043803756049461907 := by
  unfold tailWord_671484
  simp only [CollatzResearch.WordTrace]
  refine ⟨12245516749667811591070753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16327355666223748788094337 12245516749667811591070753)
  ·
    refine ⟨9184137562250858693303065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12245516749667811591070753 9184137562250858693303065)
    ·
      refine ⟨6888103171688144019977299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9184137562250858693303065 6888103171688144019977299)
      ·
        refine ⟨10332154757532216029965949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6888103171688144019977299 10332154757532216029965949)
        ·
          refine ⟨3874558034074581011237231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10332154757532216029965949 3874558034074581011237231)
          ·
            refine ⟨5811837051111871516855847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3874558034074581011237231 5811837051111871516855847)
            ·
              refine ⟨8717755576667807275283771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5811837051111871516855847 8717755576667807275283771)
              ·
                refine ⟨13076633365001710912925657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8717755576667807275283771 13076633365001710912925657)
                ·
                  refine ⟨9807475023751283184694243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13076633365001710912925657 9807475023751283184694243)
                  ·
                    refine ⟨14711212535626924777041365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9807475023751283184694243 14711212535626924777041365)
                    ·
                      refine ⟨344794043803756049461907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 14711212535626924777041365 344794043803756049461907)
                      ·
                        rfl

theorem cell23_671484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_671484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671484 prefixEnd_671484 := by exact prefixLift 671484
  have htrace : WordTrace (prefixWord ++ tailWord_671484) baseStart_671484 baseEnd_671484 := by
    simpa [prefixWord, tailWord_671484, baseEnd_671484] using wordTrace_append hprefix tailTrace_671484
  have hstable : (prefixWord ++ tailWord_671484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671484).length < 2 ^ (prefixWord ++ tailWord_671484).sum := by decide
  have hdescent : baseEnd_671484 < baseStart_671484 := by decide
  rcases family_descends (prefixWord ++ tailWord_671484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671498 : List Nat := [3, 1, 2, 2, 1, 4, 1, 1, 1, 5, 2]
def baseStart_671498 : Nat := 118140960795 + 671498 * 2 ^ 59
def prefixEnd_671498 : Nat := 4983230072969 + 3 ^ 40 * 671498 * 2
def baseEnd_671498 : Nat := 344801232532918994686843

theorem tailTrace_671498 : CollatzResearch.WordTrace tailWord_671498 prefixEnd_671498 344801232532918994686843 := by
  unfold tailWord_671498
  simp only [CollatzResearch.WordTrace]
  refine ⟨6122886030321225893287787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16327696080856602382100765 6122886030321225893287787)
  ·
    refine ⟨9184329045481838839931681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6122886030321225893287787 9184329045481838839931681)
    ·
      refine ⟨6888246784111379129948761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9184329045481838839931681 6888246784111379129948761)
      ·
        refine ⟨5166185088083534347461571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6888246784111379129948761 5166185088083534347461571)
        ·
          refine ⟨7749277632125301521192357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5166185088083534347461571 7749277632125301521192357)
          ·
            refine ⟨1452989556023494035223567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7749277632125301521192357 1452989556023494035223567)
            ·
              refine ⟨2179484334035241052835351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1452989556023494035223567 2179484334035241052835351)
              ·
                refine ⟨3269226501052861579253027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2179484334035241052835351 3269226501052861579253027)
                ·
                  refine ⟨4903839751579292368879541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3269226501052861579253027 4903839751579292368879541)
                  ·
                    refine ⟨459734976710558659582457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4903839751579292368879541 459734976710558659582457)
                    ·
                      refine ⟨344801232532918994686843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 459734976710558659582457 344801232532918994686843)
                      ·
                        rfl

theorem cell23_671498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_671498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671498 prefixEnd_671498 := by exact prefixLift 671498
  have htrace : WordTrace (prefixWord ++ tailWord_671498) baseStart_671498 baseEnd_671498 := by
    simpa [prefixWord, tailWord_671498, baseEnd_671498] using wordTrace_append hprefix tailTrace_671498
  have hstable : (prefixWord ++ tailWord_671498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671498).length < 2 ^ (prefixWord ++ tailWord_671498).sum := by decide
  have hdescent : baseEnd_671498 < baseStart_671498 := by decide
  rcases family_descends (prefixWord ++ tailWord_671498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671538 : List Nat := [3, 2, 1, 1, 3, 4, 1, 1, 1, 6]
def baseStart_671538 : Nat := 118140960795 + 671538 * 2 ^ 59
def prefixEnd_671538 : Nat := 4983230072969 + 3 ^ 40 * 671538 * 2
def baseEnd_671538 : Nat := 114940590586366279395553

theorem tailTrace_671538 : CollatzResearch.WordTrace tailWord_671538 prefixEnd_671538 114940590586366279395553 := by
  unfold tailWord_671538
  simp only [CollatzResearch.WordTrace]
  refine ⟨6123250760284997601151817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16328668694093326936404845 6123250760284997601151817)
  ·
    refine ⟨4592438070213748200863863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6123250760284997601151817 4592438070213748200863863)
    ·
      refine ⟨6888657105320622301295795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4592438070213748200863863 6888657105320622301295795)
      ·
        refine ⟨10332985657980933451943693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6888657105320622301295795 10332985657980933451943693)
        ·
          refine ⟨3874869621742850044478885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10332985657980933451943693 3874869621742850044478885)
          ·
            refine ⟨726538054076784383339791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3874869621742850044478885 726538054076784383339791)
            ·
              refine ⟨1089807081115176575009687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 726538054076784383339791 1089807081115176575009687)
              ·
                refine ⟨1634710621672764862514531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1089807081115176575009687 1634710621672764862514531)
                ·
                  refine ⟨2452065932509147293771797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1634710621672764862514531 2452065932509147293771797)
                  ·
                    refine ⟨114940590586366279395553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2452065932509147293771797 114940590586366279395553)
                    ·
                      rfl

theorem cell23_671538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_671538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671538 prefixEnd_671538 := by exact prefixLift 671538
  have htrace : WordTrace (prefixWord ++ tailWord_671538) baseStart_671538 baseEnd_671538 := by
    simpa [prefixWord, tailWord_671538, baseEnd_671538] using wordTrace_append hprefix tailTrace_671538
  have hstable : (prefixWord ++ tailWord_671538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671538).length < 2 ^ (prefixWord ++ tailWord_671538).sum := by decide
  have hdescent : baseEnd_671538 < baseStart_671538 := by decide
  rcases family_descends (prefixWord ++ tailWord_671538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671548 : List Nat := [2, 2, 2, 2, 1, 1, 3, 4, 1, 2, 3]
def baseStart_671548 : Nat := 118140960795 + 671548 * 2 ^ 59
def prefixEnd_671548 : Nat := 4983230072969 + 3 ^ 40 * 671548 * 2
def baseEnd_671548 : Nat := 344826906565643799061613

theorem tailTrace_671548 : CollatzResearch.WordTrace tailWord_671548 prefixEnd_671548 344826906565643799061613 := by
  unfold tailWord_671548
  simp only [CollatzResearch.WordTrace]
  refine ⟨12246683885551881056235649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16328911847402508074980865 12246683885551881056235649)
  ·
    refine ⟨9185012914163910792176737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12246683885551881056235649 9185012914163910792176737)
    ·
      refine ⟨6888759685622933094132553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9185012914163910792176737 6888759685622933094132553)
      ·
        refine ⟨5166569764217199820599415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6888759685622933094132553 5166569764217199820599415)
        ·
          refine ⟨7749854646325799730899123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5166569764217199820599415 7749854646325799730899123)
          ·
            refine ⟨11624781969488699596348685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7749854646325799730899123 11624781969488699596348685)
            ·
              refine ⟨4359293238558262348630757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11624781969488699596348685 4359293238558262348630757)
              ·
                refine ⟨817367482229674190368267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4359293238558262348630757 817367482229674190368267)
                ·
                  refine ⟨1226051223344511285552401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 817367482229674190368267 1226051223344511285552401)
                  ·
                    refine ⟨919538417508383464164301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1226051223344511285552401 919538417508383464164301)
                    ·
                      refine ⟨344826906565643799061613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 919538417508383464164301 344826906565643799061613)
                      ·
                        rfl

theorem cell23_671548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_671548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671548 prefixEnd_671548 := by exact prefixLift 671548
  have htrace : WordTrace (prefixWord ++ tailWord_671548) baseStart_671548 baseEnd_671548 := by
    simpa [prefixWord, tailWord_671548, baseEnd_671548] using wordTrace_append hprefix tailTrace_671548
  have hstable : (prefixWord ++ tailWord_671548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671548).length < 2 ^ (prefixWord ++ tailWord_671548).sum := by decide
  have hdescent : baseEnd_671548 < baseStart_671548 := by decide
  rcases family_descends (prefixWord ++ tailWord_671548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671551 : List Nat := [1, 1, 2, 2, 6, 1, 1, 9]
def baseStart_671551 : Nat := 118140960795 + 671551 * 2 ^ 59
def prefixEnd_671551 : Nat := 4983230072969 + 3 ^ 40 * 671551 * 2
def baseEnd_671551 : Nat := 12771423963244714345337

theorem tailTrace_671551 : CollatzResearch.WordTrace tailWord_671551 prefixEnd_671551 12771423963244714345337 := by
  unfold tailWord_671551
  simp only [CollatzResearch.WordTrace]
  refine ⟨24493477190092893624830507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16328984793395262416553671 24493477190092893624830507)
  ·
    refine ⟨36740215785139340437245761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24493477190092893624830507 36740215785139340437245761)
    ·
      refine ⟨27555161838854505327934321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36740215785139340437245761 27555161838854505327934321)
      ·
        refine ⟨20666371379140878995950741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27555161838854505327934321 20666371379140878995950741)
        ·
          refine ⟨968736158397228702935191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20666371379140878995950741 968736158397228702935191)
          ·
            refine ⟨1453104237595843054402787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 968736158397228702935191 1453104237595843054402787)
            ·
              refine ⟨2179656356393764581604181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1453104237595843054402787 2179656356393764581604181)
              ·
                refine ⟨12771423963244714345337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2179656356393764581604181 12771423963244714345337)
                ·
                  rfl

theorem cell23_671551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 9].length) (baseStart_671551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671551 prefixEnd_671551 := by exact prefixLift 671551
  have htrace : WordTrace (prefixWord ++ tailWord_671551) baseStart_671551 baseEnd_671551 := by
    simpa [prefixWord, tailWord_671551, baseEnd_671551] using wordTrace_append hprefix tailTrace_671551
  have hstable : (prefixWord ++ tailWord_671551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671551).length < 2 ^ (prefixWord ++ tailWord_671551).sum := by decide
  have hdescent : baseEnd_671551 < baseStart_671551 := by decide
  rcases family_descends (prefixWord ++ tailWord_671551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671561 : List Nat := [1, 2, 1, 1, 2, 4, 2, 1, 3, 3, 3]
def baseStart_671561 : Nat := 118140960795 + 671561 * 2 ^ 59
def prefixEnd_671561 : Nat := 4983230072969 + 3 ^ 40 * 671561 * 2
def baseEnd_671561 : Nat := 344833581814152248199053

theorem tailTrace_671561 : CollatzResearch.WordTrace tailWord_671561 prefixEnd_671561 344833581814152248199053 := by
  unfold tailWord_671561
  simp only [CollatzResearch.WordTrace]
  refine ⟨24493841920056665332694537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16329227946704443555129691 24493841920056665332694537)
  ·
    refine ⟨18370381440042498999520903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24493841920056665332694537 18370381440042498999520903)
    ·
      refine ⟨27555572160063748499281355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18370381440042498999520903 27555572160063748499281355)
      ·
        refine ⟨41333358240095622748922033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27555572160063748499281355 41333358240095622748922033)
        ·
          refine ⟨31000018680071717061691525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41333358240095622748922033 31000018680071717061691525)
          ·
            refine ⟨5812503502513446949067161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31000018680071717061691525 5812503502513446949067161)
            ·
              refine ⟨4359377626885085211800371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5812503502513446949067161 4359377626885085211800371)
              ·
                refine ⟨6539066440327627817700557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4359377626885085211800371 6539066440327627817700557)
                ·
                  refine ⟨2452149915122860431637709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6539066440327627817700557 2452149915122860431637709)
                  ·
                    refine ⟨919556218171072661864141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2452149915122860431637709 919556218171072661864141)
                    ·
                      refine ⟨344833581814152248199053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 919556218171072661864141 344833581814152248199053)
                      ·
                        rfl

theorem cell23_671561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 3, 3].length) (baseStart_671561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671561 prefixEnd_671561 := by exact prefixLift 671561
  have htrace : WordTrace (prefixWord ++ tailWord_671561) baseStart_671561 baseEnd_671561 := by
    simpa [prefixWord, tailWord_671561, baseEnd_671561] using wordTrace_append hprefix tailTrace_671561
  have hstable : (prefixWord ++ tailWord_671561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671561).length < 2 ^ (prefixWord ++ tailWord_671561).sum := by decide
  have hdescent : baseEnd_671561 < baseStart_671561 := by decide
  rcases family_descends (prefixWord ++ tailWord_671561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671565 : List Nat := [1, 6, 1, 2, 1, 2, 2, 1, 1, 1, 5]
def baseStart_671565 : Nat := 118140960795 + 671565 * 2 ^ 59
def prefixEnd_671565 : Nat := 4983230072969 + 3 ^ 40 * 671565 * 2
def baseEnd_671565 : Nat := 344835635736770232549035

theorem tailTrace_671565 : CollatzResearch.WordTrace tailWord_671565 prefixEnd_671565 344835635736770232549035 := by
  unfold tailWord_671565
  simp only [CollatzResearch.WordTrace]
  refine ⟨24493987812042174015840149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16329325208028116010560099 24493987812042174015840149)
  ·
    refine ⟨1148155678689476906992507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24493987812042174015840149 1148155678689476906992507)
    ·
      refine ⟨1722233518034215360488761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1148155678689476906992507 1722233518034215360488761)
      ·
        refine ⟨1291675138525661520366571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1722233518034215360488761 1291675138525661520366571)
        ·
          refine ⟨1937512707788492280549857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1291675138525661520366571 1937512707788492280549857)
          ·
            refine ⟨1453134530841369210412393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1937512707788492280549857 1453134530841369210412393)
            ·
              refine ⟨1089850898131026907809295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1453134530841369210412393 1089850898131026907809295)
              ·
                refine ⟨1634776347196540361713943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1089850898131026907809295 1634776347196540361713943)
                ·
                  refine ⟨2452164520794810542570915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1634776347196540361713943 2452164520794810542570915)
                  ·
                    refine ⟨3678246781192215813856373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2452164520794810542570915 3678246781192215813856373)
                    ·
                      refine ⟨344835635736770232549035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3678246781192215813856373 344835635736770232549035)
                      ·
                        rfl

theorem cell23_671565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_671565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671565 prefixEnd_671565 := by exact prefixLift 671565
  have htrace : WordTrace (prefixWord ++ tailWord_671565) baseStart_671565 baseEnd_671565 := by
    simpa [prefixWord, tailWord_671565, baseEnd_671565] using wordTrace_append hprefix tailTrace_671565
  have hstable : (prefixWord ++ tailWord_671565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671565).length < 2 ^ (prefixWord ++ tailWord_671565).sum := by decide
  have hdescent : baseEnd_671565 < baseStart_671565 := by decide
  rcases family_descends (prefixWord ++ tailWord_671565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671578 : List Nat := [3, 1, 1, 2, 1, 3, 1, 3, 4, 1, 3]
def baseStart_671578 : Nat := 118140960795 + 671578 * 2 ^ 59
def prefixEnd_671578 : Nat := 4983230072969 + 3 ^ 40 * 671578 * 2
def baseEnd_671578 : Nat := 344842310985278681686475

theorem tailTrace_671578 : CollatzResearch.WordTrace tailWord_671578 prefixEnd_671578 344842310985278681686475 := by
  unfold tailWord_671578
  simp only [CollatzResearch.WordTrace]
  refine ⟨6123615490248769309015847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16329641307330051490708925 6123615490248769309015847)
  ·
    refine ⟨9185423235373153963523771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6123615490248769309015847 9185423235373153963523771)
    ·
      refine ⟨13778134853059730945285657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9185423235373153963523771 13778134853059730945285657)
      ·
        refine ⟨10333601139794798208964243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13778134853059730945285657 10333601139794798208964243)
        ·
          refine ⟨15500401709692197313446365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10333601139794798208964243 15500401709692197313446365)
          ·
            refine ⟨5812650641134573992542387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15500401709692197313446365 5812650641134573992542387)
            ·
              refine ⟨8718975961701860988813581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5812650641134573992542387 8718975961701860988813581)
              ·
                refine ⟨3269615985638197870805093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8718975961701860988813581 3269615985638197870805093)
                ·
                  refine ⟨613052997307162100775955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3269615985638197870805093 613052997307162100775955)
                  ·
                    refine ⟨919579495960743151163933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 613052997307162100775955 919579495960743151163933)
                    ·
                      refine ⟨344842310985278681686475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 919579495960743151163933 344842310985278681686475)
                      ·
                        rfl

theorem cell23_671578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 4, 1, 3].length) (baseStart_671578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671578 prefixEnd_671578 := by exact prefixLift 671578
  have htrace : WordTrace (prefixWord ++ tailWord_671578) baseStart_671578 baseEnd_671578 := by
    simpa [prefixWord, tailWord_671578, baseEnd_671578] using wordTrace_append hprefix tailTrace_671578
  have hstable : (prefixWord ++ tailWord_671578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671578).length < 2 ^ (prefixWord ++ tailWord_671578).sum := by decide
  have hdescent : baseEnd_671578 < baseStart_671578 := by decide
  rcases family_descends (prefixWord ++ tailWord_671578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671605 : List Nat := [1, 3, 4, 1, 1, 1, 3, 1, 3, 3, 2]
def baseStart_671605 : Nat := 118140960795 + 671605 * 2 ^ 59
def prefixEnd_671605 : Nat := 4983230072969 + 3 ^ 40 * 671605 * 2
def baseEnd_671605 : Nat := 344856174962950076048851

theorem tailTrace_671605 : CollatzResearch.WordTrace tailWord_671605 prefixEnd_671605 344856174962950076048851 := by
  unfold tailWord_671605
  simp only [CollatzResearch.WordTrace]
  refine ⟨24495446731897260847296269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16330297821264840564864179 24495446731897260847296269)
  ·
    refine ⟨9185792524461472817736101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24495446731897260847296269 9185792524461472817736101)
    ·
      refine ⟨1722336098336526153325519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9185792524461472817736101 1722336098336526153325519)
      ·
        refine ⟨2583504147504789229988279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1722336098336526153325519 2583504147504789229988279)
        ·
          refine ⟨3875256221257183844982419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2583504147504789229988279 3875256221257183844982419)
          ·
            refine ⟨5812884331885775767473629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3875256221257183844982419 5812884331885775767473629)
            ·
              refine ⟨2179831624457165912802611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5812884331885775767473629 2179831624457165912802611)
              ·
                refine ⟨3269747436685748869203917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2179831624457165912802611 3269747436685748869203917)
                ·
                  refine ⟨1226155288757155825951469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3269747436685748869203917 1226155288757155825951469)
                  ·
                    refine ⟨459808233283933434731801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1226155288757155825951469 459808233283933434731801)
                    ·
                      refine ⟨344856174962950076048851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 459808233283933434731801 344856174962950076048851)
                      ·
                        rfl

theorem cell23_671605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_671605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671605 prefixEnd_671605 := by exact prefixLift 671605
  have htrace : WordTrace (prefixWord ++ tailWord_671605) baseStart_671605 baseEnd_671605 := by
    simpa [prefixWord, tailWord_671605, baseEnd_671605] using wordTrace_append hprefix tailTrace_671605
  have hstable : (prefixWord ++ tailWord_671605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671605).length < 2 ^ (prefixWord ++ tailWord_671605).sum := by decide
  have hdescent : baseEnd_671605 < baseStart_671605 := by decide
  rcases family_descends (prefixWord ++ tailWord_671605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671621 : List Nat := [1, 3, 1, 1, 3, 2, 1, 3, 2, 1, 5]
def baseStart_671621 : Nat := 118140960795 + 671621 * 2 ^ 59
def prefixEnd_671621 : Nat := 4983230072969 + 3 ^ 40 * 671621 * 2
def baseEnd_671621 : Nat := 344864390653422013448777

theorem tailTrace_671621 : CollatzResearch.WordTrace tailWord_671621 prefixEnd_671621 344864390653422013448777 := by
  unfold tailWord_671621
  simp only [CollatzResearch.WordTrace]
  refine ⟨24496030299839295579878717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16330686866559530386585811 24496030299839295579878717)
  ·
    refine ⟨9186011362439735842454519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24496030299839295579878717 9186011362439735842454519)
    ·
      refine ⟨13779017043659603763681779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9186011362439735842454519 13779017043659603763681779)
      ·
        refine ⟨20668525565489405645522669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13779017043659603763681779 20668525565489405645522669)
        ·
          refine ⟨7750697087058527117071001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20668525565489405645522669 7750697087058527117071001)
          ·
            refine ⟨5813022815293895337803251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7750697087058527117071001 5813022815293895337803251)
            ·
              refine ⟨8719534222940843006704877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5813022815293895337803251 8719534222940843006704877)
              ·
                refine ⟨3269825333602816127514329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8719534222940843006704877 3269825333602816127514329)
                ·
                  refine ⟨2452369000202112095635747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3269825333602816127514329 2452369000202112095635747)
                  ·
                    refine ⟨3678553500303168143453621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2452369000202112095635747 3678553500303168143453621)
                    ·
                      refine ⟨344864390653422013448777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3678553500303168143453621 344864390653422013448777)
                      ·
                        rfl

theorem cell23_671621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_671621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671621 prefixEnd_671621 := by exact prefixLift 671621
  have htrace : WordTrace (prefixWord ++ tailWord_671621) baseStart_671621 baseEnd_671621 := by
    simpa [prefixWord, tailWord_671621, baseEnd_671621] using wordTrace_append hprefix tailTrace_671621
  have hstable : (prefixWord ++ tailWord_671621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671621).length < 2 ^ (prefixWord ++ tailWord_671621).sum := by decide
  have hdescent : baseEnd_671621 < baseStart_671621 := by decide
  rcases family_descends (prefixWord ++ tailWord_671621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671630 : List Nat := [4, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2]
def baseStart_671630 : Nat := 118140960795 + 671630 * 2 ^ 59
def prefixEnd_671630 : Nat := 4983230072969 + 3 ^ 40 * 671630 * 2
def baseEnd_671630 : Nat := 344869011979312478236237

theorem tailTrace_671630 : CollatzResearch.WordTrace tailWord_671630 prefixEnd_671630 344869011979312478236237 := by
  unfold tailWord_671630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3062044819600836264619543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16330905704537793411304229 3062044819600836264619543)
  ·
    refine ⟨4593067229401254396929315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3062044819600836264619543 4593067229401254396929315)
    ·
      refine ⟨6889600844101881595393973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4593067229401254396929315 6889600844101881595393973)
      ·
        refine ⟨645900079134551399568185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6889600844101881595393973 645900079134551399568185)
        ·
          refine ⟨484425059350913549676139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 645900079134551399568185 484425059350913549676139)
          ·
            refine ⟨726637589026370324514209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484425059350913549676139 726637589026370324514209)
            ·
              refine ⟨544978191769777743385657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 726637589026370324514209 544978191769777743385657)
              ·
                refine ⟨408733643827333307539243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 544978191769777743385657 408733643827333307539243)
                ·
                  refine ⟨613100465740999961308865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 408733643827333307539243 613100465740999961308865)
                  ·
                    refine ⟨459825349305749970981649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 613100465740999961308865 459825349305749970981649)
                    ·
                      refine ⟨344869011979312478236237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 459825349305749970981649 344869011979312478236237)
                      ·
                        rfl

theorem cell23_671630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_671630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671630 prefixEnd_671630 := by exact prefixLift 671630
  have htrace : WordTrace (prefixWord ++ tailWord_671630) baseStart_671630 baseEnd_671630 := by
    simpa [prefixWord, tailWord_671630, baseEnd_671630] using wordTrace_append hprefix tailTrace_671630
  have hstable : (prefixWord ++ tailWord_671630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671630).length < 2 ^ (prefixWord ++ tailWord_671630).sum := by decide
  have hdescent : baseEnd_671630 < baseStart_671630 := by decide
  rcases family_descends (prefixWord ++ tailWord_671630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671652 : List Nat := [2, 3, 1, 2, 1, 3, 2, 3, 2, 2, 2]
def baseStart_671652 : Nat := 118140960795 + 671652 * 2 ^ 59
def prefixEnd_671652 : Nat := 4983230072969 + 3 ^ 40 * 671652 * 2
def baseEnd_671652 : Nat := 344880308553711392161135

theorem tailTrace_671652 : CollatzResearch.WordTrace tailWord_671652 prefixEnd_671652 344880308553711392161135 := by
  unfold tailWord_671652
  simp only [CollatzResearch.WordTrace]
  refine ⟨12248580481363493937128605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16331440641817991916171473 12248580481363493937128605)
  ·
    refine ⟨4593217680511310226423227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12248580481363493937128605 4593217680511310226423227)
    ·
      refine ⟨6889826520766965339634841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4593217680511310226423227 6889826520766965339634841)
      ·
        refine ⟨5167369890575224004726131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6889826520766965339634841 5167369890575224004726131)
        ·
          refine ⟨7751054835862836007089197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5167369890575224004726131 7751054835862836007089197)
          ·
            refine ⟨2906645563448563502658449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7751054835862836007089197 2906645563448563502658449)
            ·
              refine ⟨2179984172586422626993837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2906645563448563502658449 2179984172586422626993837)
              ·
                refine ⟨817494064719908485122689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2179984172586422626993837 817494064719908485122689)
                ·
                  refine ⟨613120548539931363842017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 817494064719908485122689 613120548539931363842017)
                  ·
                    refine ⟨459840411404948522881513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 613120548539931363842017 459840411404948522881513)
                    ·
                      refine ⟨344880308553711392161135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 459840411404948522881513 344880308553711392161135)
                      ·
                        rfl

theorem cell23_671652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_671652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671652 prefixEnd_671652 := by exact prefixLift 671652
  have htrace : WordTrace (prefixWord ++ tailWord_671652) baseStart_671652 baseEnd_671652 := by
    simpa [prefixWord, tailWord_671652, baseEnd_671652] using wordTrace_append hprefix tailTrace_671652
  have hstable : (prefixWord ++ tailWord_671652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671652).length < 2 ^ (prefixWord ++ tailWord_671652).sum := by decide
  have hdescent : baseEnd_671652 < baseStart_671652 := by decide
  rcases family_descends (prefixWord ++ tailWord_671652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671728 : List Nat := [2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 3]
def baseStart_671728 : Nat := 118140960795 + 671728 * 2 ^ 59
def prefixEnd_671728 : Nat := 4983230072969 + 3 ^ 40 * 671728 * 2
def baseEnd_671728 : Nat := 344919333083453094810785

theorem tailTrace_671728 : CollatzResearch.WordTrace tailWord_671728 prefixEnd_671728 344919333083453094810785 := by
  unfold tailWord_671728
  simp only [CollatzResearch.WordTrace]
  refine ⟨12249966455225826427011919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16333288606967768569349225 12249966455225826427011919)
  ·
    refine ⟨18374949682838739640517879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12249966455225826427011919 18374949682838739640517879)
    ·
      refine ⟨27562424524258109460776819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18374949682838739640517879 27562424524258109460776819)
      ·
        refine ⟨41343636786387164191165229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27562424524258109460776819 41343636786387164191165229)
        ·
          refine ⟨15503863794895186571686961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41343636786387164191165229 15503863794895186571686961)
          ·
            refine ⟨11627897846171389928765221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15503863794895186571686961 11627897846171389928765221)
            ·
              refine ⟨2180230846157135611643479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11627897846171389928765221 2180230846157135611643479)
              ·
                refine ⟨3270346269235703417465219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2180230846157135611643479 3270346269235703417465219)
                ·
                  refine ⟨4905519403853555126197829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3270346269235703417465219 4905519403853555126197829)
                  ·
                    refine ⟨919784888222541586162093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4905519403853555126197829 919784888222541586162093)
                    ·
                      refine ⟨344919333083453094810785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 919784888222541586162093 344919333083453094810785)
                      ·
                        rfl

theorem cell23_671728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 3].length) (baseStart_671728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671728 prefixEnd_671728 := by exact prefixLift 671728
  have htrace : WordTrace (prefixWord ++ tailWord_671728) baseStart_671728 baseEnd_671728 := by
    simpa [prefixWord, tailWord_671728, baseEnd_671728] using wordTrace_append hprefix tailTrace_671728
  have hstable : (prefixWord ++ tailWord_671728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671728).length < 2 ^ (prefixWord ++ tailWord_671728).sum := by decide
  have hdescent : baseEnd_671728 < baseStart_671728 := by decide
  rcases family_descends (prefixWord ++ tailWord_671728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671742 : List Nat := [4, 2, 2, 2, 1, 2, 1, 2, 2, 1, 4]
def baseStart_671742 : Nat := 118140960795 + 671742 * 2 ^ 59
def prefixEnd_671742 : Nat := 4983230072969 + 3 ^ 40 * 671742 * 2
def baseEnd_671742 : Nat := 344926521812616040035721

theorem tailTrace_671742 : CollatzResearch.WordTrace tailWord_671742 prefixEnd_671742 344926521812616040035721 := by
  unfold tailWord_671742
  simp only [CollatzResearch.WordTrace]
  refine ⟨3062555441550116655629185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16333629021600622163355653 3062555441550116655629185)
  ·
    refine ⟨2296916581162587491721889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3062555441550116655629185 2296916581162587491721889)
    ·
      refine ⟨1722687435871940618791417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2296916581162587491721889 1722687435871940618791417)
      ·
        refine ⟨1292015576903955464093563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1722687435871940618791417 1292015576903955464093563)
        ·
          refine ⟨1938023365355933196140345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1292015576903955464093563 1938023365355933196140345)
          ·
            refine ⟨1453517524016949897105259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1938023365355933196140345 1453517524016949897105259)
            ·
              refine ⟨2180276286025424845657889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1453517524016949897105259 2180276286025424845657889)
              ·
                refine ⟨1635207214519068634243417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2180276286025424845657889 1635207214519068634243417)
                ·
                  refine ⟨1226405410889301475682563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1635207214519068634243417 1226405410889301475682563)
                  ·
                    refine ⟨1839608116333952213523845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1226405410889301475682563 1839608116333952213523845)
                    ·
                      refine ⟨344926521812616040035721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1839608116333952213523845 344926521812616040035721)
                      ·
                        rfl

theorem cell23_671742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_671742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671742 prefixEnd_671742 := by exact prefixLift 671742
  have htrace : WordTrace (prefixWord ++ tailWord_671742) baseStart_671742 baseEnd_671742 := by
    simpa [prefixWord, tailWord_671742, baseEnd_671742] using wordTrace_append hprefix tailTrace_671742
  have hstable : (prefixWord ++ tailWord_671742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671742).length < 2 ^ (prefixWord ++ tailWord_671742).sum := by decide
  have hdescent : baseEnd_671742 < baseStart_671742 := by decide
  rcases family_descends (prefixWord ++ tailWord_671742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671745 : List Nat := [1, 2, 4, 1, 2, 1, 3, 2, 2, 2, 3]
def baseStart_671745 : Nat := 118140960795 + 671745 * 2 ^ 59
def prefixEnd_671745 : Nat := 4983230072969 + 3 ^ 40 * 671745 * 2
def baseEnd_671745 : Nat := 344928062254579528298207

theorem tailTrace_671745 : CollatzResearch.WordTrace tailWord_671745 prefixEnd_671745 344928062254579528298207 := by
  unfold tailWord_671745
  simp only [CollatzResearch.WordTrace]
  refine ⟨24500552951390064757392689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16333701967593376504928459 24500552951390064757392689)
  ·
    refine ⟨18375414713542548568044517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24500552951390064757392689 18375414713542548568044517)
    ·
      refine ⟨3445390258789227856508347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18375414713542548568044517 3445390258789227856508347)
      ·
        refine ⟨5168085388183841784762521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3445390258789227856508347 5168085388183841784762521)
        ·
          refine ⟨3876064041137881338571891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5168085388183841784762521 3876064041137881338571891)
          ·
            refine ⟨5814096061706822007857837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3876064041137881338571891 5814096061706822007857837)
            ·
              refine ⟨2180286023140058252946689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5814096061706822007857837 2180286023140058252946689)
              ·
                refine ⟨1635214517355043689710017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2180286023140058252946689 1635214517355043689710017)
                ·
                  refine ⟨1226410888016282767282513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1635214517355043689710017 1226410888016282767282513)
                  ·
                    refine ⟨919808166012212075461885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1226410888016282767282513 919808166012212075461885)
                    ·
                      refine ⟨344928062254579528298207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 919808166012212075461885 344928062254579528298207)
                      ·
                        rfl

theorem cell23_671745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_671745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671745 prefixEnd_671745 := by exact prefixLift 671745
  have htrace : WordTrace (prefixWord ++ tailWord_671745) baseStart_671745 baseEnd_671745 := by
    simpa [prefixWord, tailWord_671745, baseEnd_671745] using wordTrace_append hprefix tailTrace_671745
  have hstable : (prefixWord ++ tailWord_671745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671745).length < 2 ^ (prefixWord ++ tailWord_671745).sum := by decide
  have hdescent : baseEnd_671745 < baseStart_671745 := by decide
  rcases family_descends (prefixWord ++ tailWord_671745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671761 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 1, 11]
def baseStart_671761 : Nat := 118140960795 + 671761 * 2 ^ 59
def prefixEnd_671761 : Nat := 4983230072969 + 3 ^ 40 * 671761 * 2
def baseEnd_671761 : Nat := 114978759315017155232711

theorem tailTrace_671761 : CollatzResearch.WordTrace tailWord_671761 prefixEnd_671761 114978759315017155232711 := by
  unfold tailWord_671761
  simp only [CollatzResearch.WordTrace]
  refine ⟨24501136519332099489975137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16334091012888066326650091 24501136519332099489975137)
  ·
    refine ⟨18375852389499074617481353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24501136519332099489975137 18375852389499074617481353)
    ·
      refine ⟨13781889292124305963111015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18375852389499074617481353 13781889292124305963111015)
      ·
        refine ⟨20672833938186458944666523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13781889292124305963111015 20672833938186458944666523)
        ·
          refine ⟨31009250907279688416999785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20672833938186458944666523 31009250907279688416999785)
          ·
            refine ⟨23256938180459766312749839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31009250907279688416999785 23256938180459766312749839)
            ·
              refine ⟨34885407270689649469124759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23256938180459766312749839 34885407270689649469124759)
              ·
                refine ⟨52328110906034474203687139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34885407270689649469124759 52328110906034474203687139)
                ·
                  refine ⟨78492166359051711305530709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52328110906034474203687139 78492166359051711305530709)
                  ·
                    refine ⟨114978759315017155232711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 78492166359051711305530709 114978759315017155232711)
                    ·
                      rfl

theorem cell23_671761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 11].length) (baseStart_671761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671761 prefixEnd_671761 := by exact prefixLift 671761
  have htrace : WordTrace (prefixWord ++ tailWord_671761) baseStart_671761 baseEnd_671761 := by
    simpa [prefixWord, tailWord_671761, baseEnd_671761] using wordTrace_append hprefix tailTrace_671761
  have hstable : (prefixWord ++ tailWord_671761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671761).length < 2 ^ (prefixWord ++ tailWord_671761).sum := by decide
  have hdescent : baseEnd_671761 < baseStart_671761 := by decide
  rcases family_descends (prefixWord ++ tailWord_671761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671765 : List Nat := [1, 3, 2, 1, 5, 1, 1, 3, 6]
def baseStart_671765 : Nat := 118140960795 + 671765 * 2 ^ 59
def prefixEnd_671765 : Nat := 4983230072969 + 3 ^ 40 * 671765 * 2
def baseEnd_671765 : Nat := 38326481318629938894235

theorem tailTrace_671765 : CollatzResearch.WordTrace tailWord_671765 prefixEnd_671765 38326481318629938894235 := by
  unfold tailWord_671765
  simp only [CollatzResearch.WordTrace]
  refine ⟨24501282411317608173120749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16334188274211738782080499 24501282411317608173120749)
  ·
    refine ⟨9187980904244103064920281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24501282411317608173120749 9187980904244103064920281)
    ·
      refine ⟨6890985678183077298690211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9187980904244103064920281 6890985678183077298690211)
      ·
        refine ⟨10336478517274615948035317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6890985678183077298690211 10336478517274615948035317)
        ·
          refine ⟨969044860994495245128311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10336478517274615948035317 969044860994495245128311)
          ·
            refine ⟨1453567291491742867692467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 969044860994495245128311 1453567291491742867692467)
            ·
              refine ⟨2180350937237614301538701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1453567291491742867692467 2180350937237614301538701)
              ·
                refine ⟨817631601464105363077013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2180350937237614301538701 817631601464105363077013)
                ·
                  refine ⟨38326481318629938894235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 817631601464105363077013 38326481318629938894235)
                  ·
                    rfl

theorem cell23_671765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 6].length) (baseStart_671765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671765 prefixEnd_671765 := by exact prefixLift 671765
  have htrace : WordTrace (prefixWord ++ tailWord_671765) baseStart_671765 baseEnd_671765 := by
    simpa [prefixWord, tailWord_671765, baseEnd_671765] using wordTrace_append hprefix tailTrace_671765
  have hstable : (prefixWord ++ tailWord_671765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671765).length < 2 ^ (prefixWord ++ tailWord_671765).sum := by decide
  have hdescent : baseEnd_671765 < baseStart_671765 := by decide
  rcases family_descends (prefixWord ++ tailWord_671765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671771 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 7]
def baseStart_671771 : Nat := 118140960795 + 671771 * 2 ^ 59
def prefixEnd_671771 : Nat := 4983230072969 + 3 ^ 40 * 671771 * 2
def baseEnd_671771 : Nat := 344941412751596426573087

theorem tailTrace_671771 : CollatzResearch.WordTrace tailWord_671771 prefixEnd_671771 344941412751596426573087 := by
  unfold tailWord_671771
  simp only [CollatzResearch.WordTrace]
  refine ⟨24501501249295871197839167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16334334166197247465226111 24501501249295871197839167)
  ·
    refine ⟨36752251873943806796758751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24501501249295871197839167 36752251873943806796758751)
    ·
      refine ⟨55128377810915710195138127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36752251873943806796758751 55128377810915710195138127)
      ·
        refine ⟨82692566716373565292707191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55128377810915710195138127 82692566716373565292707191)
        ·
          refine ⟨124038850074560347939060787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82692566716373565292707191 124038850074560347939060787)
          ·
            refine ⟨186058275111840521908591181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124038850074560347939060787 186058275111840521908591181)
            ·
              refine ⟨69771853166940195715721693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 186058275111840521908591181 69771853166940195715721693)
              ·
                refine ⟨26164444937602573393395635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69771853166940195715721693 26164444937602573393395635)
                ·
                  refine ⟨39246667406403860090093453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26164444937602573393395635 39246667406403860090093453)
                  ·
                    refine ⟨14717500277401447533785045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39246667406403860090093453 14717500277401447533785045)
                    ·
                      refine ⟨344941412751596426573087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 14717500277401447533785045 344941412751596426573087)
                      ·
                        rfl

theorem cell23_671771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 7].length) (baseStart_671771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671771 prefixEnd_671771 := by exact prefixLift 671771
  have htrace : WordTrace (prefixWord ++ tailWord_671771) baseStart_671771 baseEnd_671771 := by
    simpa [prefixWord, tailWord_671771, baseEnd_671771] using wordTrace_append hprefix tailTrace_671771
  have hstable : (prefixWord ++ tailWord_671771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671771).length < 2 ^ (prefixWord ++ tailWord_671771).sum := by decide
  have hdescent : baseEnd_671771 < baseStart_671771 := by decide
  rcases family_descends (prefixWord ++ tailWord_671771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671775 : List Nat := [1, 1, 2, 4, 1, 2, 2, 1, 5, 1, 3]
def baseStart_671775 : Nat := 118140960795 + 671775 * 2 ^ 59
def prefixEnd_671775 : Nat := 4983230072969 + 3 ^ 40 * 671775 * 2
def baseEnd_671775 : Nat := 344943466674214410923069

theorem tailTrace_671775 : CollatzResearch.WordTrace tailWord_671775 prefixEnd_671775 344943466674214410923069 := by
  unfold tailWord_671775
  simp only [CollatzResearch.WordTrace]
  refine ⟨24501647141281379880984779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16334431427520919920656519 24501647141281379880984779)
  ·
    refine ⟨36752470711922069821477169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24501647141281379880984779 36752470711922069821477169)
    ·
      refine ⟨27564353033941552366107877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36752470711922069821477169 27564353033941552366107877)
      ·
        refine ⟨5168316193864041068645227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27564353033941552366107877 5168316193864041068645227)
        ·
          refine ⟨7752474290796061602967841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5168316193864041068645227 7752474290796061602967841)
          ·
            refine ⟨5814355718097046202225881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7752474290796061602967841 5814355718097046202225881)
            ·
              refine ⟨4360766788572784651669411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5814355718097046202225881 4360766788572784651669411)
              ·
                refine ⟨6541150182859176977504117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4360766788572784651669411 6541150182859176977504117)
                ·
                  refine ⟨613232829643047841641011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6541150182859176977504117 613232829643047841641011)
                  ·
                    refine ⟨919849244464571762461517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 613232829643047841641011 919849244464571762461517)
                    ·
                      refine ⟨344943466674214410923069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 919849244464571762461517 344943466674214410923069)
                      ·
                        rfl

theorem cell23_671775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_671775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671775 prefixEnd_671775 := by exact prefixLift 671775
  have htrace : WordTrace (prefixWord ++ tailWord_671775) baseStart_671775 baseEnd_671775 := by
    simpa [prefixWord, tailWord_671775, baseEnd_671775] using wordTrace_append hprefix tailTrace_671775
  have hstable : (prefixWord ++ tailWord_671775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671775).length < 2 ^ (prefixWord ++ tailWord_671775).sum := by decide
  have hdescent : baseEnd_671775 < baseStart_671775 := by decide
  rcases family_descends (prefixWord ++ tailWord_671775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671818 : List Nat := [3, 1, 2, 1, 1, 2, 1, 3, 3, 1, 5]
def baseStart_671818 : Nat := 118140960795 + 671818 * 2 ^ 59
def prefixEnd_671818 : Nat := 4983230072969 + 3 ^ 40 * 671818 * 2
def baseEnd_671818 : Nat := 344965546342357742685371

theorem tailTrace_671818 : CollatzResearch.WordTrace tailWord_671818 prefixEnd_671818 344965546342357742685371 := by
  unfold tailWord_671818
  simp only [CollatzResearch.WordTrace]
  refine ⟨6125803870031399556200027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16335476986750398816533405 6125803870031399556200027)
  ·
    refine ⟨9188705805047099334300041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6125803870031399556200027 9188705805047099334300041)
    ·
      refine ⟨6891529353785324500725031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9188705805047099334300041 6891529353785324500725031)
      ·
        refine ⟨10337294030677986751087547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6891529353785324500725031 10337294030677986751087547)
        ·
          refine ⟨15505941046016980126631321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10337294030677986751087547 15505941046016980126631321)
          ·
            refine ⟨11629455784512735094973491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15505941046016980126631321 11629455784512735094973491)
            ·
              refine ⟨17444183676769102642460237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11629455784512735094973491 17444183676769102642460237)
              ·
                refine ⟨6541568878788413490922589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17444183676769102642460237 6541568878788413490922589)
                ·
                  refine ⟨2453088329545655059095971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6541568878788413490922589 2453088329545655059095971)
                  ·
                    refine ⟨3679632494318482588643957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2453088329545655059095971 3679632494318482588643957)
                    ·
                      refine ⟨344965546342357742685371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3679632494318482588643957 344965546342357742685371)
                      ·
                        rfl

theorem cell23_671818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_671818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671818 prefixEnd_671818 := by exact prefixLift 671818
  have htrace : WordTrace (prefixWord ++ tailWord_671818) baseStart_671818 baseEnd_671818 := by
    simpa [prefixWord, tailWord_671818, baseEnd_671818] using wordTrace_append hprefix tailTrace_671818
  have hstable : (prefixWord ++ tailWord_671818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671818).length < 2 ^ (prefixWord ++ tailWord_671818).sum := by decide
  have hdescent : baseEnd_671818 < baseStart_671818 := by decide
  rcases family_descends (prefixWord ++ tailWord_671818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671832 : List Nat := [2, 1, 2, 2, 1, 4, 1, 1, 5, 2, 2]
def baseStart_671832 : Nat := 118140960795 + 671832 * 2 ^ 59
def prefixEnd_671832 : Nat := 4983230072969 + 3 ^ 40 * 671832 * 2
def baseEnd_671832 : Nat := 344972735071520687910307

theorem tailTrace_671832 : CollatzResearch.WordTrace tailWord_671832 prefixEnd_671832 344972735071520687910307 := by
  unfold tailWord_671832
  simp only [CollatzResearch.WordTrace]
  refine ⟨12251863051037439307904875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16335817401383252410539833 12251863051037439307904875)
  ·
    refine ⟨18377794576556158961857313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12251863051037439307904875 18377794576556158961857313)
    ·
      refine ⟨13783345932417119221392985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18377794576556158961857313 13783345932417119221392985)
      ·
        refine ⟨10337509449312839416044739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13783345932417119221392985 10337509449312839416044739)
        ·
          refine ⟨15506264173969259124067109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10337509449312839416044739 15506264173969259124067109)
          ·
            refine ⟨2907424532619236085762583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15506264173969259124067109 2907424532619236085762583)
            ·
              refine ⟨4361136798928854128643875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2907424532619236085762583 4361136798928854128643875)
              ·
                refine ⟨6541705198393281192965813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4361136798928854128643875 6541705198393281192965813)
                ·
                  refine ⟨613284862349370111840545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6541705198393281192965813 613284862349370111840545)
                  ·
                    refine ⟨459963646762027583880409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 613284862349370111840545 459963646762027583880409)
                    ·
                      refine ⟨344972735071520687910307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 459963646762027583880409 344972735071520687910307)
                      ·
                        rfl

theorem cell23_671832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 5, 2, 2].length) (baseStart_671832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671832 prefixEnd_671832 := by exact prefixLift 671832
  have htrace : WordTrace (prefixWord ++ tailWord_671832) baseStart_671832 baseEnd_671832 := by
    simpa [prefixWord, tailWord_671832, baseEnd_671832] using wordTrace_append hprefix tailTrace_671832
  have hstable : (prefixWord ++ tailWord_671832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671832).length < 2 ^ (prefixWord ++ tailWord_671832).sum := by decide
  have hdescent : baseEnd_671832 < baseStart_671832 := by decide
  rcases family_descends (prefixWord ++ tailWord_671832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671845 : List Nat := [1, 3, 1, 3, 2, 2, 2, 2, 1, 2, 4]
def baseStart_671845 : Nat := 118140960795 + 671845 * 2 ^ 59
def prefixEnd_671845 : Nat := 4983230072969 + 3 ^ 40 * 671845 * 2
def baseEnd_671845 : Nat := 344979410320029137047747

theorem tailTrace_671845 : CollatzResearch.WordTrace tailWord_671845 prefixEnd_671845 344979410320029137047747 := by
  unfold tailWord_671845
  simp only [CollatzResearch.WordTrace]
  refine ⟨24504200251027781836032989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16336133500685187890688659 24504200251027781836032989)
  ·
    refine ⟨9189075094135418188512371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24504200251027781836032989 9189075094135418188512371)
    ·
      refine ⟨13783612641203127282768557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9189075094135418188512371 13783612641203127282768557)
      ·
        refine ⟨5168854740451172731038209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13783612641203127282768557 5168854740451172731038209)
        ·
          refine ⟨3876641055338379548278657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5168854740451172731038209 3876641055338379548278657)
          ·
            refine ⟨2907480791503784661208993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3876641055338379548278657 2907480791503784661208993)
            ·
              refine ⟨2180610593627838495906745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2907480791503784661208993 2180610593627838495906745)
              ·
                refine ⟨1635457945220878871930059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2180610593627838495906745 1635457945220878871930059)
                ·
                  refine ⟨2453186917831318307895089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1635457945220878871930059 2453186917831318307895089)
                  ·
                    refine ⟨1839890188373488730921317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2453186917831318307895089 1839890188373488730921317)
                    ·
                      refine ⟨344979410320029137047747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1839890188373488730921317 344979410320029137047747)
                      ·
                        rfl

theorem cell23_671845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_671845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671845 prefixEnd_671845 := by exact prefixLift 671845
  have htrace : WordTrace (prefixWord ++ tailWord_671845) baseStart_671845 baseEnd_671845 := by
    simpa [prefixWord, tailWord_671845, baseEnd_671845] using wordTrace_append hprefix tailTrace_671845
  have hstable : (prefixWord ++ tailWord_671845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671845).length < 2 ^ (prefixWord ++ tailWord_671845).sum := by decide
  have hdescent : baseEnd_671845 < baseStart_671845 := by decide
  rcases family_descends (prefixWord ++ tailWord_671845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671852 : List Nat := [2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 3]
def baseStart_671852 : Nat := 118140960795 + 671852 * 2 ^ 59
def prefixEnd_671852 : Nat := 4983230072969 + 3 ^ 40 * 671852 * 2
def baseEnd_671852 : Nat := 344983004684610609660215

theorem tailTrace_671852 : CollatzResearch.WordTrace tailWord_671852 prefixEnd_671852 344983004684610609660215 := by
  unfold tailWord_671852
  simp only [CollatzResearch.WordTrace]
  refine ⟨12252227781001211015768905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16336303708001614687691873 12252227781001211015768905)
  ·
    refine ⟨9189170835750908261826679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12252227781001211015768905 9189170835750908261826679)
    ·
      refine ⟨13783756253626362392740019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9189170835750908261826679 13783756253626362392740019)
      ·
        refine ⟨20675634380439543589110029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13783756253626362392740019 20675634380439543589110029)
        ·
          refine ⟨7753362892664828845916261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20675634380439543589110029 7753362892664828845916261)
          ·
            refine ⟨1453755542374655408609299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7753362892664828845916261 1453755542374655408609299)
            ·
              refine ⟨2180633313561983112913949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1453755542374655408609299 2180633313561983112913949)
              ·
                refine ⟨817737492585743667342731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2180633313561983112913949 817737492585743667342731)
                ·
                  refine ⟨1226606238878615501014097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 817737492585743667342731 1226606238878615501014097)
                  ·
                    refine ⟨919954679158961625760573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1226606238878615501014097 919954679158961625760573)
                    ·
                      refine ⟨344983004684610609660215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 919954679158961625760573 344983004684610609660215)
                      ·
                        rfl

theorem cell23_671852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 3].length) (baseStart_671852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671852 prefixEnd_671852 := by exact prefixLift 671852
  have htrace : WordTrace (prefixWord ++ tailWord_671852) baseStart_671852 baseEnd_671852 := by
    simpa [prefixWord, tailWord_671852, baseEnd_671852] using wordTrace_append hprefix tailTrace_671852
  have hstable : (prefixWord ++ tailWord_671852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671852).length < 2 ^ (prefixWord ++ tailWord_671852).sum := by decide
  have hdescent : baseEnd_671852 < baseStart_671852 := by decide
  rcases family_descends (prefixWord ++ tailWord_671852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671882 : List Nat := [3, 1, 2, 3, 1, 2, 3, 1, 1, 3, 3]
def baseStart_671882 : Nat := 118140960795 + 671882 * 2 ^ 59
def prefixEnd_671882 : Nat := 4983230072969 + 3 ^ 40 * 671882 * 2
def baseEnd_671882 : Nat := 344998409104245492285077

theorem tailTrace_671882 : CollatzResearch.WordTrace tailWord_671882 prefixEnd_671882 344998409104245492285077 := by
  unfold tailWord_671882
  simp only [CollatzResearch.WordTrace]
  refine ⟨6126387437973434288782475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16337033167929158103419933 6126387437973434288782475)
  ·
    refine ⟨9189581156960151433173713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6126387437973434288782475 9189581156960151433173713)
    ·
      refine ⟨6892185867720113574880285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9189581156960151433173713 6892185867720113574880285)
      ·
        refine ⟨2584569700395042590580107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6892185867720113574880285 2584569700395042590580107)
        ·
          refine ⟨3876854550592563885870161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2584569700395042590580107 3876854550592563885870161)
          ·
            refine ⟨2907640912944422914402621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3876854550592563885870161 2907640912944422914402621)
            ·
              refine ⟨1090365342354158592900983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2907640912944422914402621 1090365342354158592900983)
              ·
                refine ⟨1635548013531237889351475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1090365342354158592900983 1635548013531237889351475)
                ·
                  refine ⟨2453322020296856834027213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1635548013531237889351475 2453322020296856834027213)
                  ·
                    refine ⟨919995757611321312760205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2453322020296856834027213 919995757611321312760205)
                    ·
                      refine ⟨344998409104245492285077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 919995757611321312760205 344998409104245492285077)
                      ·
                        rfl

theorem cell23_671882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_671882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671882 prefixEnd_671882 := by exact prefixLift 671882
  have htrace : WordTrace (prefixWord ++ tailWord_671882) baseStart_671882 baseEnd_671882 := by
    simpa [prefixWord, tailWord_671882, baseEnd_671882] using wordTrace_append hprefix tailTrace_671882
  have hstable : (prefixWord ++ tailWord_671882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671882).length < 2 ^ (prefixWord ++ tailWord_671882).sum := by decide
  have hdescent : baseEnd_671882 < baseStart_671882 := by decide
  rcases family_descends (prefixWord ++ tailWord_671882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671894 : List Nat := [5, 3, 2, 1, 1, 2, 1, 3, 1, 1, 3]
def baseStart_671894 : Nat := 118140960795 + 671894 * 2 ^ 59
def prefixEnd_671894 : Nat := 4983230072969 + 3 ^ 40 * 671894 * 2
def baseEnd_671894 : Nat := 345004570872099445335023

theorem tailTrace_671894 : CollatzResearch.WordTrace tailWord_671894 prefixEnd_671894 345004570872099445335023 := by
  unfold tailWord_671894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1531624214240641450285421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16337324951900175469711157 1531624214240641450285421)
  ·
    refine ⟨574359080340240543857033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1531624214240641450285421 574359080340240543857033)
    ·
      refine ⟨430769310255180407892775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 574359080340240543857033 430769310255180407892775)
      ·
        refine ⟨646153965382770611839163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 430769310255180407892775 646153965382770611839163)
        ·
          refine ⟨969230948074155917758745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 646153965382770611839163 969230948074155917758745)
          ·
            refine ⟨726923211055616938319059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 969230948074155917758745 726923211055616938319059)
            ·
              refine ⟨1090384816583425407478589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 726923211055616938319059 1090384816583425407478589)
              ·
                refine ⟨408894306218784527804471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1090384816583425407478589 408894306218784527804471)
                ·
                  refine ⟨613341459328176791706707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 408894306218784527804471 613341459328176791706707)
                  ·
                    refine ⟨920012188992265187560061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 613341459328176791706707 920012188992265187560061)
                    ·
                      refine ⟨345004570872099445335023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 920012188992265187560061 345004570872099445335023)
                      ·
                        rfl

theorem cell23_671894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_671894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671894 prefixEnd_671894 := by exact prefixLift 671894
  have htrace : WordTrace (prefixWord ++ tailWord_671894) baseStart_671894 baseEnd_671894 := by
    simpa [prefixWord, tailWord_671894, baseEnd_671894] using wordTrace_append hprefix tailTrace_671894
  have hstable : (prefixWord ++ tailWord_671894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671894).length < 2 ^ (prefixWord ++ tailWord_671894).sum := by decide
  have hdescent : baseEnd_671894 < baseStart_671894 := by decide
  rcases family_descends (prefixWord ++ tailWord_671894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671985 : List Nat := [1, 2, 2, 2, 2, 1, 4, 1, 1, 2, 5]
def baseStart_671985 : Nat := 118140960795 + 671985 * 2 ^ 59
def prefixEnd_671985 : Nat := 4983230072969 + 3 ^ 40 * 671985 * 2
def baseEnd_671985 : Nat := 345051297611658589297103

theorem tailTrace_671985 : CollatzResearch.WordTrace tailWord_671985 prefixEnd_671985 345051297611658589297103 := by
  unfold tailWord_671985
  simp only [CollatzResearch.WordTrace]
  refine ⟨24509306470520585746129409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16339537647013723830752939 24509306470520585746129409)
  ·
    refine ⟨18381979852890439309597057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24509306470520585746129409 18381979852890439309597057)
    ·
      refine ⟨13786484889667829482197793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18381979852890439309597057 13786484889667829482197793)
      ·
        refine ⟨10339863667250872111648345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13786484889667829482197793 10339863667250872111648345)
        ·
          refine ⟨7754897750438154083736259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10339863667250872111648345 7754897750438154083736259)
          ·
            refine ⟨11632346625657231125604389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7754897750438154083736259 11632346625657231125604389)
            ·
              refine ⟨2181064992310730836050823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11632346625657231125604389 2181064992310730836050823)
              ·
                refine ⟨3271597488466096254076235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2181064992310730836050823 3271597488466096254076235)
                ·
                  refine ⟨4907396232699144381114353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3271597488466096254076235 4907396232699144381114353)
                  ·
                    refine ⟨3680547174524358285835765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4907396232699144381114353 3680547174524358285835765)
                    ·
                      refine ⟨345051297611658589297103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3680547174524358285835765 345051297611658589297103)
                      ·
                        rfl

theorem cell23_671985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_671985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_671985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_671985 prefixEnd_671985 := by exact prefixLift 671985
  have htrace : WordTrace (prefixWord ++ tailWord_671985) baseStart_671985 baseEnd_671985 := by
    simpa [prefixWord, tailWord_671985, baseEnd_671985] using wordTrace_append hprefix tailTrace_671985
  have hstable : (prefixWord ++ tailWord_671985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671985).length < 2 ^ (prefixWord ++ tailWord_671985).sum := by decide
  have hdescent : baseEnd_671985 < baseStart_671985 := by decide
  rcases family_descends (prefixWord ++ tailWord_671985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672012 : List Nat := [2, 2, 1, 2, 2, 2, 1, 2, 1, 6, 2]
def baseStart_672012 : Nat := 118140960795 + 672012 * 2 ^ 59
def prefixEnd_672012 : Nat := 4983230072969 + 3 ^ 40 * 672012 * 2
def baseEnd_672012 : Nat := 345065161589329983659479

theorem tailTrace_672012 : CollatzResearch.WordTrace tailWord_672012 prefixEnd_672012 345065161589329983659479 := by
  unfold tailWord_672012
  simp only [CollatzResearch.WordTrace]
  refine ⟨12255145620711384678681145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16340194160948512904908193 12255145620711384678681145)
  ·
    refine ⟨9191359215533538509010859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12255145620711384678681145 9191359215533538509010859)
    ·
      refine ⟨13787038823300307763516289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9191359215533538509010859 13787038823300307763516289)
      ·
        refine ⟨10340279117475230822637217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13787038823300307763516289 10340279117475230822637217)
        ·
          refine ⟨7755209338106423116977913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10340279117475230822637217 7755209338106423116977913)
          ·
            refine ⟨5816407003579817337733435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7755209338106423116977913 5816407003579817337733435)
            ·
              refine ⟨8724610505369726006600153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5816407003579817337733435 8724610505369726006600153)
              ·
                refine ⟨6543457879027294504950115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8724610505369726006600153 6543457879027294504950115)
                ·
                  refine ⟨9815186818540941757425173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6543457879027294504950115 9815186818540941757425173)
                  ·
                    refine ⟨460086882119106644879305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9815186818540941757425173 460086882119106644879305)
                    ·
                      refine ⟨345065161589329983659479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 460086882119106644879305 345065161589329983659479)
                      ·
                        rfl

theorem cell23_672012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 6, 2].length) (baseStart_672012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672012 prefixEnd_672012 := by exact prefixLift 672012
  have htrace : WordTrace (prefixWord ++ tailWord_672012) baseStart_672012 baseEnd_672012 := by
    simpa [prefixWord, tailWord_672012, baseEnd_672012] using wordTrace_append hprefix tailTrace_672012
  have hstable : (prefixWord ++ tailWord_672012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672012).length < 2 ^ (prefixWord ++ tailWord_672012).sum := by decide
  have hdescent : baseEnd_672012 < baseStart_672012 := by decide
  rcases family_descends (prefixWord ++ tailWord_672012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672035 : List Nat := [1, 1, 1, 4, 2, 2, 3, 1, 8]
def baseStart_672035 : Nat := 118140960795 + 672035 * 2 ^ 59
def prefixEnd_672035 : Nat := 4983230072969 + 3 ^ 40 * 672035 * 2
def baseEnd_672035 : Nat := 38341885738264821519097

theorem tailTrace_672035 : CollatzResearch.WordTrace tailWord_672035 prefixEnd_672035 38341885738264821519097 := by
  unfold tailWord_672035
  simp only [CollatzResearch.WordTrace]
  refine ⟨24511130120339444285449559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16340753413559629523633039 24511130120339444285449559)
  ·
    refine ⟨36766695180509166428174339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24511130120339444285449559 36766695180509166428174339)
    ·
      refine ⟨55150042770763749642261509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36766695180509166428174339 55150042770763749642261509)
      ·
        refine ⟨10340633019518203057924033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55150042770763749642261509 10340633019518203057924033)
        ·
          refine ⟨7755474764638652293443025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10340633019518203057924033 7755474764638652293443025)
          ·
            refine ⟨5816606073478989220082269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7755474764638652293443025 5816606073478989220082269)
            ·
              refine ⟨2181227277554620957530851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5816606073478989220082269 2181227277554620957530851)
              ·
                refine ⟨3271840916331931436296277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2181227277554620957530851 3271840916331931436296277)
                ·
                  refine ⟨38341885738264821519097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3271840916331931436296277 38341885738264821519097)
                  ·
                    rfl

theorem cell23_672035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 8].length) (baseStart_672035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672035 prefixEnd_672035 := by exact prefixLift 672035
  have htrace : WordTrace (prefixWord ++ tailWord_672035) baseStart_672035 baseEnd_672035 := by
    simpa [prefixWord, tailWord_672035, baseEnd_672035] using wordTrace_append hprefix tailTrace_672035
  have hstable : (prefixWord ++ tailWord_672035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672035).length < 2 ^ (prefixWord ++ tailWord_672035).sum := by decide
  have hdescent : baseEnd_672035 < baseStart_672035 := by decide
  rcases family_descends (prefixWord ++ tailWord_672035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672129 : List Nat := [1, 2, 4, 3, 1, 2, 1, 2, 1, 6]
def baseStart_672129 : Nat := 118140960795 + 672129 * 2 ^ 59
def prefixEnd_672129 : Nat := 4983230072969 + 3 ^ 40 * 672129 * 2
def baseEnd_672129 : Nat := 115041746275302008632147

theorem tailTrace_672129 : CollatzResearch.WordTrace tailWord_672129 prefixEnd_672129 115041746275302008632147 := by
  unfold tailWord_672129
  simp only [CollatzResearch.WordTrace]
  refine ⟨24514558581998898339371441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16343039054665932226247627 24514558581998898339371441)
  ·
    refine ⟨18385918936499173754528581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24514558581998898339371441 18385918936499173754528581)
    ·
      refine ⟨3447359800593595078974109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18385918936499173754528581 3447359800593595078974109)
      ·
        refine ⟨1292759925222598154615291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3447359800593595078974109 1292759925222598154615291)
        ·
          refine ⟨1939139887833897231922937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1292759925222598154615291 1939139887833897231922937)
          ·
            refine ⟨1454354915875422923942203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1939139887833897231922937 1454354915875422923942203)
            ·
              refine ⟨2181532373813134385913305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1454354915875422923942203 2181532373813134385913305)
              ·
                refine ⟨1636149280359850789434979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2181532373813134385913305 1636149280359850789434979)
                ·
                  refine ⟨2454223920539776184152469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1636149280359850789434979 2454223920539776184152469)
                  ·
                    refine ⟨115041746275302008632147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2454223920539776184152469 115041746275302008632147)
                    ·
                      rfl

theorem cell23_672129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_672129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672129 prefixEnd_672129 := by exact prefixLift 672129
  have htrace : WordTrace (prefixWord ++ tailWord_672129) baseStart_672129 baseEnd_672129 := by
    simpa [prefixWord, tailWord_672129, baseEnd_672129] using wordTrace_append hprefix tailTrace_672129
  have hstable : (prefixWord ++ tailWord_672129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672129).length < 2 ^ (prefixWord ++ tailWord_672129).sum := by decide
  have hdescent : baseEnd_672129 < baseStart_672129 := by decide
  rcases family_descends (prefixWord ++ tailWord_672129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672136 : List Nat := [2, 1, 3, 3, 1, 1, 5, 1, 1, 1, 4]
def baseStart_672136 : Nat := 118140960795 + 672136 * 2 ^ 59
def prefixEnd_672136 : Nat := 4983230072969 + 3 ^ 40 * 672136 * 2
def baseEnd_672136 : Nat := 345128833190487498508909

theorem tailTrace_672136 : CollatzResearch.WordTrace tailWord_672136 prefixEnd_672136 345128833190487498508909 := by
  unfold tailWord_672136
  simp only [CollatzResearch.WordTrace]
  refine ⟨12257406946486769267438131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16343209261982359023250841 12257406946486769267438131)
  ·
    refine ⟨18386110419730153901157197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12257406946486769267438131 18386110419730153901157197)
    ·
      refine ⟨6894791407398807712933949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18386110419730153901157197 6894791407398807712933949)
      ·
        refine ⟨2585546777774552892350231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6894791407398807712933949 2585546777774552892350231)
        ·
          refine ⟨3878320166661829338525347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2585546777774552892350231 3878320166661829338525347)
          ·
            refine ⟨5817480249992744007788021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3878320166661829338525347 5817480249992744007788021)
            ·
              refine ⟨545388773436819750730127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5817480249992744007788021 545388773436819750730127)
              ·
                refine ⟨818083160155229626095191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 545388773436819750730127 818083160155229626095191)
                ·
                  refine ⟨1227124740232844439142787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 818083160155229626095191 1227124740232844439142787)
                  ·
                    refine ⟨1840687110349266658714181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1227124740232844439142787 1840687110349266658714181)
                    ·
                      refine ⟨345128833190487498508909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1840687110349266658714181 345128833190487498508909)
                      ·
                        rfl

theorem cell23_672136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_672136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672136 prefixEnd_672136 := by exact prefixLift 672136
  have htrace : WordTrace (prefixWord ++ tailWord_672136) baseStart_672136 baseEnd_672136 := by
    simpa [prefixWord, tailWord_672136, baseEnd_672136] using wordTrace_append hprefix tailTrace_672136
  have hstable : (prefixWord ++ tailWord_672136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672136).length < 2 ^ (prefixWord ++ tailWord_672136).sum := by decide
  have hdescent : baseEnd_672136 < baseStart_672136 := by decide
  rcases family_descends (prefixWord ++ tailWord_672136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672139 : List Nat := [1, 1, 1, 1, 4, 6, 1, 1, 1, 1, 5]
def baseStart_672139 : Nat := 118140960795 + 672139 * 2 ^ 59
def prefixEnd_672139 : Nat := 4983230072969 + 3 ^ 40 * 672139 * 2
def baseEnd_672139 : Nat := 345130373632450986771395

theorem tailTrace_672139 : CollatzResearch.WordTrace tailWord_672139 prefixEnd_672139 345130373632450986771395 := by
  unfold tailWord_672139
  simp only [CollatzResearch.WordTrace]
  refine ⟨24514923311962670047235471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16343282207975113364823647 24514923311962670047235471)
  ·
    refine ⟨36772384967944005070853207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24514923311962670047235471 36772384967944005070853207)
    ·
      refine ⟨55158577451916007606279811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36772384967944005070853207 55158577451916007606279811)
      ·
        refine ⟨82737866177874011409419717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55158577451916007606279811 82737866177874011409419717)
        ·
          refine ⟨15513349908351377139266197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82737866177874011409419717 15513349908351377139266197)
          ·
            refine ⟨727188276953970803403103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15513349908351377139266197 727188276953970803403103)
            ·
              refine ⟨1090782415430956205104655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 727188276953970803403103 1090782415430956205104655)
              ·
                refine ⟨1636173623146434307656983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1090782415430956205104655 1636173623146434307656983)
                ·
                  refine ⟨2454260434719651461485475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1636173623146434307656983 2454260434719651461485475)
                  ·
                    refine ⟨3681390652079477192228213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2454260434719651461485475 3681390652079477192228213)
                    ·
                      refine ⟨345130373632450986771395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3681390652079477192228213 345130373632450986771395)
                      ·
                        rfl

theorem cell23_672139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 1, 5].length) (baseStart_672139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672139 prefixEnd_672139 := by exact prefixLift 672139
  have htrace : WordTrace (prefixWord ++ tailWord_672139) baseStart_672139 baseEnd_672139 := by
    simpa [prefixWord, tailWord_672139, baseEnd_672139] using wordTrace_append hprefix tailTrace_672139
  have hstable : (prefixWord ++ tailWord_672139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672139).length < 2 ^ (prefixWord ++ tailWord_672139).sum := by decide
  have hdescent : baseEnd_672139 < baseStart_672139 := by decide
  rcases family_descends (prefixWord ++ tailWord_672139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672142 : List Nat := [4, 1, 1, 4, 1, 12]
def baseStart_672142 : Nat := 118140960795 + 672142 * 2 ^ 59
def prefixEnd_672142 : Nat := 4983230072969 + 3 ^ 40 * 672142 * 2
def baseEnd_672142 : Nat := 1420295942693063683267

theorem tailTrace_672142 : CollatzResearch.WordTrace tailWord_672142 prefixEnd_672142 1420295942693063683267 := by
  unfold tailWord_672142
  simp only [CollatzResearch.WordTrace]
  refine ⟨3064379091368975194949335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16343355153967867706396453 3064379091368975194949335)
  ·
    refine ⟨4596568637053462792424003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3064379091368975194949335 4596568637053462792424003)
    ·
      refine ⟨6894852955580194188636005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4596568637053462792424003 6894852955580194188636005)
      ·
        refine ⟨1292784929171286410369251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6894852955580194188636005 1292784929171286410369251)
        ·
          refine ⟨1939177393756929615553877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1292784929171286410369251 1939177393756929615553877)
          ·
            refine ⟨1420295942693063683267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 1939177393756929615553877 1420295942693063683267)
            ·
              rfl

theorem cell23_672142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 12].length) (baseStart_672142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672142 prefixEnd_672142 := by exact prefixLift 672142
  have htrace : WordTrace (prefixWord ++ tailWord_672142) baseStart_672142 baseEnd_672142 := by
    simpa [prefixWord, tailWord_672142, baseEnd_672142] using wordTrace_append hprefix tailTrace_672142
  have hstable : (prefixWord ++ tailWord_672142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672142).length < 2 ^ (prefixWord ++ tailWord_672142).sum := by decide
  have hdescent : baseEnd_672142 < baseStart_672142 := by decide
  rcases family_descends (prefixWord ++ tailWord_672142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672153 : List Nat := [1, 2, 1, 2, 1, 4, 3, 4, 1, 2, 2]
def baseStart_672153 : Nat := 118140960795 + 672153 * 2 ^ 59
def prefixEnd_672153 : Nat := 4983230072969 + 3 ^ 40 * 672153 * 2
def baseEnd_672153 : Nat := 345137562361613931996331

theorem tailTrace_672153 : CollatzResearch.WordTrace tailWord_672153 prefixEnd_672153 345137562361613931996331 := by
  unfold tailWord_672153
  simp only [CollatzResearch.WordTrace]
  refine ⟨24515433933911950438245113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16343622622607966958830075 24515433933911950438245113)
  ·
    refine ⟨18386575450433962828683835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24515433933911950438245113 18386575450433962828683835)
    ·
      refine ⟨27579863175650944243025753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18386575450433962828683835 27579863175650944243025753)
      ·
        refine ⟨20684897381738208182269315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27579863175650944243025753 20684897381738208182269315)
        ·
          refine ⟨31027346072607312273403973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20684897381738208182269315 31027346072607312273403973)
          ·
            refine ⟨5817627388613871051263245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31027346072607312273403973 5817627388613871051263245)
            ·
              refine ⟨2181610270730201644223717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5817627388613871051263245 2181610270730201644223717)
              ·
                refine ⟨409051925761912808291947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2181610270730201644223717 409051925761912808291947)
                ·
                  refine ⟨613577888642869212437921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 409051925761912808291947 613577888642869212437921)
                  ·
                    refine ⟨460183416482151909328441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 613577888642869212437921 460183416482151909328441)
                    ·
                      refine ⟨345137562361613931996331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 460183416482151909328441 345137562361613931996331)
                      ·
                        rfl

theorem cell23_672153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 4, 1, 2, 2].length) (baseStart_672153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672153 prefixEnd_672153 := by exact prefixLift 672153
  have htrace : WordTrace (prefixWord ++ tailWord_672153) baseStart_672153 baseEnd_672153 := by
    simpa [prefixWord, tailWord_672153, baseEnd_672153] using wordTrace_append hprefix tailTrace_672153
  have hstable : (prefixWord ++ tailWord_672153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672153).length < 2 ^ (prefixWord ++ tailWord_672153).sum := by decide
  have hdescent : baseEnd_672153 < baseStart_672153 := by decide
  rcases family_descends (prefixWord ++ tailWord_672153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672202 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 4, 6]
def baseStart_672202 : Nat := 118140960795 + 672202 * 2 ^ 59
def prefixEnd_672202 : Nat := 4983230072969 + 3 ^ 40 * 672202 * 2
def baseEnd_672202 : Nat := 115054240971228080094535

theorem tailTrace_672202 : CollatzResearch.WordTrace tailWord_672202 prefixEnd_672202 115054240971228080094535 := by
  unfold tailWord_672202
  simp only [CollatzResearch.WordTrace]
  refine ⟨6129305277683607951694715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16344814073822954537852573 6129305277683607951694715)
  ·
    refine ⟨9193957916525411927542073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6129305277683607951694715 9193957916525411927542073)
    ·
      refine ⟨6895468437394058945656555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9193957916525411927542073 6895468437394058945656555)
      ·
        refine ⟨10343202656091088418484833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6895468437394058945656555 10343202656091088418484833)
        ·
          refine ⟨7757401992068316313863625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10343202656091088418484833 7757401992068316313863625)
          ·
            refine ⟨5818051494051237235397719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7757401992068316313863625 5818051494051237235397719)
            ·
              refine ⟨8727077241076855853096579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5818051494051237235397719 8727077241076855853096579)
              ·
                refine ⟨13090615861615283779644869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8727077241076855853096579 13090615861615283779644869)
                ·
                  refine ⟨2454490474052865708683413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13090615861615283779644869 2454490474052865708683413)
                  ·
                    refine ⟨115054240971228080094535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2454490474052865708683413 115054240971228080094535)
                    ·
                      rfl

theorem cell23_672202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_672202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672202 prefixEnd_672202 := by exact prefixLift 672202
  have htrace : WordTrace (prefixWord ++ tailWord_672202) baseStart_672202 baseEnd_672202 := by
    simpa [prefixWord, tailWord_672202, baseEnd_672202] using wordTrace_append hprefix tailTrace_672202
  have hstable : (prefixWord ++ tailWord_672202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672202).length < 2 ^ (prefixWord ++ tailWord_672202).sum := by decide
  have hdescent : baseEnd_672202 < baseStart_672202 := by decide
  rcases family_descends (prefixWord ++ tailWord_672202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672209 : List Nat := [1, 2, 2, 1, 2, 1, 1, 4, 3, 4, 2]
def baseStart_672209 : Nat := 118140960795 + 672209 * 2 ^ 59
def prefixEnd_672209 : Nat := 4983230072969 + 3 ^ 40 * 672209 * 2
def baseEnd_672209 : Nat := 345166317278265712896073

theorem tailTrace_672209 : CollatzResearch.WordTrace tailWord_672209 prefixEnd_672209 345166317278265712896073 := by
  unfold tailWord_672209
  simp only [CollatzResearch.WordTrace]
  refine ⟨24517476421709072002283681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16344984281139381334855787 24517476421709072002283681)
  ·
    refine ⟨18388107316281804001712761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24517476421709072002283681 18388107316281804001712761)
    ·
      refine ⟨13791080487211353001284571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18388107316281804001712761 13791080487211353001284571)
      ·
        refine ⟨20686620730817029501926857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13791080487211353001284571 20686620730817029501926857)
        ·
          refine ⟨15514965548112772126445143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20686620730817029501926857 15514965548112772126445143)
          ·
            refine ⟨23272448322169158189667715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15514965548112772126445143 23272448322169158189667715)
            ·
              refine ⟨34908672483253737284501573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23272448322169158189667715 34908672483253737284501573)
              ·
                refine ⟨6545376090610075740844045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34908672483253737284501573 6545376090610075740844045)
                ·
                  refine ⟨2454516033978778402816517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6545376090610075740844045 2454516033978778402816517)
                  ·
                    refine ⟨460221756371020950528097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2454516033978778402816517 460221756371020950528097)
                    ·
                      refine ⟨345166317278265712896073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 460221756371020950528097 345166317278265712896073)
                      ·
                        rfl

theorem cell23_672209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 4, 2].length) (baseStart_672209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672209 prefixEnd_672209 := by exact prefixLift 672209
  have htrace : WordTrace (prefixWord ++ tailWord_672209) baseStart_672209 baseEnd_672209 := by
    simpa [prefixWord, tailWord_672209, baseEnd_672209] using wordTrace_append hprefix tailTrace_672209
  have hstable : (prefixWord ++ tailWord_672209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672209).length < 2 ^ (prefixWord ++ tailWord_672209).sum := by decide
  have hdescent : baseEnd_672209 < baseStart_672209 := by decide
  rcases family_descends (prefixWord ++ tailWord_672209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672296 : List Nat := [2, 1, 5, 2, 1, 1, 1, 3, 2, 5]
def baseStart_672296 : Nat := 118140960795 + 672296 * 2 ^ 59
def prefixEnd_672296 : Nat := 4983230072969 + 3 ^ 40 * 672296 * 2
def baseEnd_672296 : Nat := 115070330031735624169391

theorem tailTrace_672296 : CollatzResearch.WordTrace tailWord_672296 prefixEnd_672296 115070330031735624169391 := by
  unfold tailWord_672296
  simp only [CollatzResearch.WordTrace]
  refine ⟨12260324786196942930350371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16347099714929257240467161 12260324786196942930350371)
  ·
    refine ⟨18390487179295414395525557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12260324786196942930350371 18390487179295414395525557)
    ·
      refine ⟨1724108173058945099580521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18390487179295414395525557 1724108173058945099580521)
      ·
        refine ⟨1293081129794208824685391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1724108173058945099580521 1293081129794208824685391)
        ·
          refine ⟨1939621694691313237028087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1293081129794208824685391 1939621694691313237028087)
          ·
            refine ⟨2909432542036969855542131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1939621694691313237028087 2909432542036969855542131)
            ·
              refine ⟨4364148813055454783313197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2909432542036969855542131 4364148813055454783313197)
              ·
                refine ⟨1636555804895795543742449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4364148813055454783313197 1636555804895795543742449)
                ·
                  refine ⟨1227416853671846657806837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1636555804895795543742449 1227416853671846657806837)
                  ·
                    refine ⟨115070330031735624169391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1227416853671846657806837 115070330031735624169391)
                    ·
                      rfl

theorem cell23_672296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_672296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672296 prefixEnd_672296 := by exact prefixLift 672296
  have htrace : WordTrace (prefixWord ++ tailWord_672296) baseStart_672296 baseEnd_672296 := by
    simpa [prefixWord, tailWord_672296, baseEnd_672296] using wordTrace_append hprefix tailTrace_672296
  have hstable : (prefixWord ++ tailWord_672296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672296).length < 2 ^ (prefixWord ++ tailWord_672296).sum := by decide
  have hdescent : baseEnd_672296 < baseStart_672296 := by decide
  rcases family_descends (prefixWord ++ tailWord_672296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672316 : List Nat := [2, 2, 2, 2, 3, 1, 2, 2, 2, 1, 4]
def baseStart_672316 : Nat := 118140960795 + 672316 * 2 ^ 59
def prefixEnd_672316 : Nat := 4983230072969 + 3 ^ 40 * 672316 * 2
def baseEnd_672316 : Nat := 345221259708296794258081

theorem tailTrace_672316 : CollatzResearch.WordTrace tailWord_672316 prefixEnd_672316 345221259708296794258081 := by
  unfold tailWord_672316
  simp only [CollatzResearch.WordTrace]
  refine ⟨12260689516160714638214401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16347586021547619517619201 12260689516160714638214401)
  ·
    refine ⟨9195517137120535978660801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12260689516160714638214401 9195517137120535978660801)
    ·
      refine ⟨6896637852840401983995601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9195517137120535978660801 6896637852840401983995601)
      ·
        refine ⟨5172478389630301487996701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6896637852840401983995601 5172478389630301487996701)
        ·
          refine ⟨1939679396111363057998763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5172478389630301487996701 1939679396111363057998763)
          ·
            refine ⟨2909519094167044586998145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1939679396111363057998763 2909519094167044586998145)
            ·
              refine ⟨2182139320625283440248609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2909519094167044586998145 2182139320625283440248609)
              ·
                refine ⟨1636604490468962580186457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2182139320625283440248609 1636604490468962580186457)
                ·
                  refine ⟨1227453367851721935139843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1636604490468962580186457 1227453367851721935139843)
                  ·
                    refine ⟨1841180051777582902709765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1227453367851721935139843 1841180051777582902709765)
                    ·
                      refine ⟨345221259708296794258081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1841180051777582902709765 345221259708296794258081)
                      ·
                        rfl

theorem cell23_672316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_672316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672316 prefixEnd_672316 := by exact prefixLift 672316
  have htrace : WordTrace (prefixWord ++ tailWord_672316) baseStart_672316 baseEnd_672316 := by
    simpa [prefixWord, tailWord_672316, baseEnd_672316] using wordTrace_append hprefix tailTrace_672316
  have hstable : (prefixWord ++ tailWord_672316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672316).length < 2 ^ (prefixWord ++ tailWord_672316).sum := by decide
  have hdescent : baseEnd_672316 < baseStart_672316 := by decide
  rcases family_descends (prefixWord ++ tailWord_672316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672333 : List Nat := [1, 6, 1, 1, 2, 1, 1, 1, 1, 6, 2]
def baseStart_672333 : Nat := 118140960795 + 672333 * 2 ^ 59
def prefixEnd_672333 : Nat := 4983230072969 + 3 ^ 40 * 672333 * 2
def baseEnd_672333 : Nat := 345229988879423227745503

theorem tailTrace_672333 : CollatzResearch.WordTrace tailWord_672333 prefixEnd_672333 345229988879423227745503 := by
  unfold tailWord_672333
  simp only [CollatzResearch.WordTrace]
  refine ⟨24521999073259841179797653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16347999382173227453198435 24521999073259841179797653)
  ·
    refine ⟨1149468706559055055303015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24521999073259841179797653 1149468706559055055303015)
    ·
      refine ⟨1724203059838582582954523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1149468706559055055303015 1724203059838582582954523)
      ·
        refine ⟨2586304589757873874431785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1724203059838582582954523 2586304589757873874431785)
        ·
          refine ⟨1939728442318405405823839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2586304589757873874431785 1939728442318405405823839)
          ·
            refine ⟨2909592663477608108735759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1939728442318405405823839 2909592663477608108735759)
            ·
              refine ⟨4364388995216412163103639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2909592663477608108735759 4364388995216412163103639)
              ·
                refine ⟨6546583492824618244655459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4364388995216412163103639 6546583492824618244655459)
                ·
                  refine ⟨9819875239236927366983189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6546583492824618244655459 9819875239236927366983189)
                  ·
                    refine ⟨460306651839230970327337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9819875239236927366983189 460306651839230970327337)
                    ·
                      refine ⟨345229988879423227745503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 460306651839230970327337 345229988879423227745503)
                      ·
                        rfl

theorem cell23_672333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_672333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672333 prefixEnd_672333 := by exact prefixLift 672333
  have htrace : WordTrace (prefixWord ++ tailWord_672333) baseStart_672333 baseEnd_672333 := by
    simpa [prefixWord, tailWord_672333, baseEnd_672333] using wordTrace_append hprefix tailTrace_672333
  have hstable : (prefixWord ++ tailWord_672333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672333).length < 2 ^ (prefixWord ++ tailWord_672333).sum := by decide
  have hdescent : baseEnd_672333 < baseStart_672333 := by decide
  rcases family_descends (prefixWord ++ tailWord_672333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672353 : List Nat := [1, 2, 3, 1, 1, 6, 1, 1, 2, 2, 3]
def baseStart_672353 : Nat := 118140960795 + 672353 * 2 ^ 59
def prefixEnd_672353 : Nat := 4983230072969 + 3 ^ 40 * 672353 * 2
def baseEnd_672353 : Nat := 345240258492513149495411

theorem tailTrace_672353 : CollatzResearch.WordTrace tailWord_672353 prefixEnd_672353 345240258492513149495411 := by
  unfold tailWord_672353
  simp only [CollatzResearch.WordTrace]
  refine ⟨24522728533187384595525713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16348485688791589730350475 24522728533187384595525713)
  ·
    refine ⟨18392046399890538446644285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24522728533187384595525713 18392046399890538446644285)
    ·
      refine ⟨6897017399958951917491607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18392046399890538446644285 6897017399958951917491607)
      ·
        refine ⟨10345526099938427876237411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6897017399958951917491607 10345526099938427876237411)
        ·
          refine ⟨15518289149907641814356117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10345526099938427876237411 15518289149907641814356117)
          ·
            refine ⟨727419803901920710047943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15518289149907641814356117 727419803901920710047943)
            ·
              refine ⟨1091129705852881065071915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 727419803901920710047943 1091129705852881065071915)
              ·
                refine ⟨1636694558779321597607873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1091129705852881065071915 1636694558779321597607873)
                ·
                  refine ⟨1227520919084491198205905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1636694558779321597607873 1227520919084491198205905)
                  ·
                    refine ⟨920640689313368398654429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1227520919084491198205905 920640689313368398654429)
                    ·
                      refine ⟨345240258492513149495411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 920640689313368398654429 345240258492513149495411)
                      ·
                        rfl

theorem cell23_672353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 2, 3].length) (baseStart_672353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672353 prefixEnd_672353 := by exact prefixLift 672353
  have htrace : WordTrace (prefixWord ++ tailWord_672353) baseStart_672353 baseEnd_672353 := by
    simpa [prefixWord, tailWord_672353, baseEnd_672353] using wordTrace_append hprefix tailTrace_672353
  have hstable : (prefixWord ++ tailWord_672353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672353).length < 2 ^ (prefixWord ++ tailWord_672353).sum := by decide
  have hdescent : baseEnd_672353 < baseStart_672353 := by decide
  rcases family_descends (prefixWord ++ tailWord_672353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672409 : List Nat := [1, 2, 1, 2, 1, 2, 3, 2, 3, 1, 5]
def baseStart_672409 : Nat := 118140960795 + 672409 * 2 ^ 59
def prefixEnd_672409 : Nat := 4983230072969 + 3 ^ 40 * 672409 * 2
def baseEnd_672409 : Nat := 345269013409164930395153

theorem tailTrace_672409 : CollatzResearch.WordTrace tailWord_672409 prefixEnd_672409 345269013409164930395153 := by
  unfold tailWord_672409
  simp only [CollatzResearch.WordTrace]
  refine ⟨24524771020984506159564281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16349847347323004106376187 24524771020984506159564281)
  ·
    refine ⟨18393578265738379619673211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24524771020984506159564281 18393578265738379619673211)
    ·
      refine ⟨27590367398607569429509817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18393578265738379619673211 27590367398607569429509817)
      ·
        refine ⟨20692775548955677072132363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27590367398607569429509817 20692775548955677072132363)
        ·
          refine ⟨31039163323433515608198545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20692775548955677072132363 31039163323433515608198545)
          ·
            refine ⟨23279372492575136706148909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31039163323433515608198545 23279372492575136706148909)
            ·
              refine ⟨8729764684715676264805841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23279372492575136706148909 8729764684715676264805841)
              ·
                refine ⟨6547323513536757198604381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8729764684715676264805841 6547323513536757198604381)
                ·
                  refine ⟨2455246317576283949476643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6547323513536757198604381 2455246317576283949476643)
                  ·
                    refine ⟨3682869476364425924214965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2455246317576283949476643 3682869476364425924214965)
                    ·
                      refine ⟨345269013409164930395153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3682869476364425924214965 345269013409164930395153)
                      ·
                        rfl

theorem cell23_672409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_672409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672409 prefixEnd_672409 := by exact prefixLift 672409
  have htrace : WordTrace (prefixWord ++ tailWord_672409) baseStart_672409 baseEnd_672409 := by
    simpa [prefixWord, tailWord_672409, baseEnd_672409] using wordTrace_append hprefix tailTrace_672409
  have hstable : (prefixWord ++ tailWord_672409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672409).length < 2 ^ (prefixWord ++ tailWord_672409).sum := by decide
  have hdescent : baseEnd_672409 < baseStart_672409 := by decide
  rcases family_descends (prefixWord ++ tailWord_672409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672446 : List Nat := [4, 2, 1, 1, 2, 1, 4, 8]
def baseStart_672446 : Nat := 118140960795 + 672446 * 2 ^ 59
def prefixEnd_672446 : Nat := 4983230072969 + 3 ^ 40 * 672446 * 2
def baseEnd_672446 : Nat := 12788444896051158727129

theorem tailTrace_672446 : CollatzResearch.WordTrace tailWord_672446 prefixEnd_672446 12788444896051158727129 := by
  unfold tailWord_672446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3065765065231307684832649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16350747014566974319107461 3065765065231307684832649)
  ·
    refine ⟨2299323798923480763624487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3065765065231307684832649 2299323798923480763624487)
    ·
      refine ⟨3448985698385221145436731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2299323798923480763624487 3448985698385221145436731)
      ·
        refine ⟨5173478547577831718155097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3448985698385221145436731 5173478547577831718155097)
        ·
          refine ⟨3880108910683373788616323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5173478547577831718155097 3880108910683373788616323)
          ·
            refine ⟨5820163366025060682924485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3880108910683373788616323 5820163366025060682924485)
            ·
              refine ⟨1091280631129698878048341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5820163366025060682924485 1091280631129698878048341)
              ·
                refine ⟨12788444896051158727129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1091280631129698878048341 12788444896051158727129)
                ·
                  rfl

theorem cell23_672446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 8].length) (baseStart_672446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672446 prefixEnd_672446 := by exact prefixLift 672446
  have htrace : WordTrace (prefixWord ++ tailWord_672446) baseStart_672446 baseEnd_672446 := by
    simpa [prefixWord, tailWord_672446, baseEnd_672446] using wordTrace_append hprefix tailTrace_672446
  have hstable : (prefixWord ++ tailWord_672446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672446).length < 2 ^ (prefixWord ++ tailWord_672446).sum := by decide
  have hdescent : baseEnd_672446 < baseStart_672446 := by decide
  rcases family_descends (prefixWord ++ tailWord_672446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672454 : List Nat := [6, 1, 2, 1, 2, 2, 1, 2, 1, 5]
def baseStart_672454 : Nat := 118140960795 + 672454 * 2 ^ 59
def prefixEnd_672454 : Nat := 4983230072969 + 3 ^ 40 * 672454 * 2
def baseEnd_672454 : Nat := 115097373346205751444149

theorem tailTrace_672454 : CollatzResearch.WordTrace tailWord_672454 prefixEnd_672454 115097373346205751444149 := by
  unfold tailWord_672454
  simp only [CollatzResearch.WordTrace]
  refine ⟨766450384556921213904763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16350941537214319229968277 766450384556921213904763)
  ·
    refine ⟨1149675576835381820857145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 766450384556921213904763 1149675576835381820857145)
    ·
      refine ⟨862256682626536365642859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1149675576835381820857145 862256682626536365642859)
      ·
        refine ⟨1293385023939804548464289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 862256682626536365642859 1293385023939804548464289)
        ·
          refine ⟨970038767954853411348217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1293385023939804548464289 970038767954853411348217)
          ·
            refine ⟨727529075966140058511163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 970038767954853411348217 727529075966140058511163)
            ·
              refine ⟨1091293613949210087766745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 727529075966140058511163 1091293613949210087766745)
              ·
                refine ⟨818470210461907565825059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1091293613949210087766745 818470210461907565825059)
                ·
                  refine ⟨1227705315692861348737589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 818470210461907565825059 1227705315692861348737589)
                  ·
                    refine ⟨115097373346205751444149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1227705315692861348737589 115097373346205751444149)
                    ·
                      rfl

theorem cell23_672454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_672454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672454 prefixEnd_672454 := by exact prefixLift 672454
  have htrace : WordTrace (prefixWord ++ tailWord_672454) baseStart_672454 baseEnd_672454 := by
    simpa [prefixWord, tailWord_672454, baseEnd_672454] using wordTrace_append hprefix tailTrace_672454
  have hstable : (prefixWord ++ tailWord_672454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672454).length < 2 ^ (prefixWord ++ tailWord_672454).sum := by decide
  have hdescent : baseEnd_672454 < baseStart_672454 := by decide
  rcases family_descends (prefixWord ++ tailWord_672454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672460 : List Nat := [2, 2, 1, 5, 1, 1, 3, 2, 1, 2, 3]
def baseStart_672460 : Nat := 118140960795 + 672460 * 2 ^ 59
def prefixEnd_672460 : Nat := 4983230072969 + 3 ^ 40 * 672460 * 2
def baseEnd_672460 : Nat := 345295200922544230857419

theorem tailTrace_672460 : CollatzResearch.WordTrace tailWord_672460 prefixEnd_672460 345295200922544230857419 := by
  unfold tailWord_672460
  simp only [CollatzResearch.WordTrace]
  refine ⟨12263315571899870934835417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16351087429199827913113889 12263315571899870934835417)
  ·
    refine ⟨9197486678924903201126563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12263315571899870934835417 9197486678924903201126563)
    ·
      refine ⟨13796230018387354801689845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9197486678924903201126563 13796230018387354801689845)
      ·
        refine ⟨1293396564223814512658423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13796230018387354801689845 1293396564223814512658423)
        ·
          refine ⟨1940094846335721768987635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1293396564223814512658423 1940094846335721768987635)
          ·
            refine ⟨2910142269503582653481453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1940094846335721768987635 2910142269503582653481453)
            ·
              refine ⟨1091303351063843495055545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2910142269503582653481453 1091303351063843495055545)
              ·
                refine ⟨818477513297882621291659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1091303351063843495055545 818477513297882621291659)
                ·
                  refine ⟨1227716269946823931937489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 818477513297882621291659 1227716269946823931937489)
                  ·
                    refine ⟨920787202460117948953117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1227716269946823931937489 920787202460117948953117)
                    ·
                      refine ⟨345295200922544230857419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 920787202460117948953117 345295200922544230857419)
                      ·
                        rfl

theorem cell23_672460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_672460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672460 prefixEnd_672460 := by exact prefixLift 672460
  have htrace : WordTrace (prefixWord ++ tailWord_672460) baseStart_672460 baseEnd_672460 := by
    simpa [prefixWord, tailWord_672460, baseEnd_672460] using wordTrace_append hprefix tailTrace_672460
  have hstable : (prefixWord ++ tailWord_672460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672460).length < 2 ^ (prefixWord ++ tailWord_672460).sum := by decide
  have hdescent : baseEnd_672460 < baseStart_672460 := by decide
  rcases family_descends (prefixWord ++ tailWord_672460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672526 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4]
def baseStart_672526 : Nat := 118140960795 + 672526 * 2 ^ 59
def prefixEnd_672526 : Nat := 4983230072969 + 3 ^ 40 * 672526 * 2
def baseEnd_672526 : Nat := 345329090645740972632115

theorem tailTrace_672526 : CollatzResearch.WordTrace tailWord_672526 prefixEnd_672526 345329090645740972632115 := by
  unfold tailWord_672526
  simp only [CollatzResearch.WordTrace]
  refine ⟨3066129795195079392696679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16352692241040423427715621 3066129795195079392696679)
  ·
    refine ⟨4599194692792619089045019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3066129795195079392696679 4599194692792619089045019)
    ·
      refine ⟨6898792039188928633567529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4599194692792619089045019 6898792039188928633567529)
      ·
        refine ⟨5174094029391696475175647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6898792039188928633567529 5174094029391696475175647)
        ·
          refine ⟨7761141044087544712763471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5174094029391696475175647 7761141044087544712763471)
          ·
            refine ⟨11641711566131317069145207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7761141044087544712763471 11641711566131317069145207)
            ·
              refine ⟨17462567349196975603717811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11641711566131317069145207 17462567349196975603717811)
              ·
                refine ⟨26193851023795463405576717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17462567349196975603717811 26193851023795463405576717)
                ·
                  refine ⟨9822694133923298777091269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26193851023795463405576717 9822694133923298777091269)
                  ·
                    refine ⟨1841755150110618520704613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9822694133923298777091269 1841755150110618520704613)
                    ·
                      refine ⟨345329090645740972632115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1841755150110618520704613 345329090645740972632115)
                      ·
                        rfl

theorem cell23_672526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_672526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672526 prefixEnd_672526 := by exact prefixLift 672526
  have htrace : WordTrace (prefixWord ++ tailWord_672526) baseStart_672526 baseEnd_672526 := by
    simpa [prefixWord, tailWord_672526, baseEnd_672526] using wordTrace_append hprefix tailTrace_672526
  have hstable : (prefixWord ++ tailWord_672526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672526).length < 2 ^ (prefixWord ++ tailWord_672526).sum := by decide
  have hdescent : baseEnd_672526 < baseStart_672526 := by decide
  rcases family_descends (prefixWord ++ tailWord_672526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672541 : List Nat := [1, 4, 2, 4, 2, 1, 1, 2, 2, 1, 3]
def baseStart_672541 : Nat := 118140960795 + 672541 * 2 ^ 59
def prefixEnd_672541 : Nat := 4983230072969 + 3 ^ 40 * 672541 * 2
def baseEnd_672541 : Nat := 345336792855558413944547

theorem tailTrace_672541 : CollatzResearch.WordTrace tailWord_672541 prefixEnd_672541 345336792855558413944547 := by
  unfold tailWord_672541
  simp only [CollatzResearch.WordTrace]
  refine ⟨24529585456506292703369477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16353056971004195135579651 24529585456506292703369477)
  ·
    refine ⟨4599297273094929881881777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24529585456506292703369477 4599297273094929881881777)
    ·
      refine ⟨3449472954821197411411333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4599297273094929881881777 3449472954821197411411333)
      ·
        refine ⟨646776179028974514639625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3449472954821197411411333 646776179028974514639625)
        ·
          refine ⟨485082134271730885979719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 646776179028974514639625 485082134271730885979719)
          ·
            refine ⟨727623201407596328969579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485082134271730885979719 727623201407596328969579)
            ·
              refine ⟨1091434802111394493454369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 727623201407596328969579 1091434802111394493454369)
              ·
                refine ⟨818576101583545870090777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1091434802111394493454369 818576101583545870090777)
                ·
                  refine ⟨613932076187659402568083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 818576101583545870090777 613932076187659402568083)
                  ·
                    refine ⟨920898114281489103852125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 613932076187659402568083 920898114281489103852125)
                    ·
                      refine ⟨345336792855558413944547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 920898114281489103852125 345336792855558413944547)
                      ·
                        rfl

theorem cell23_672541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_672541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672541 prefixEnd_672541 := by exact prefixLift 672541
  have htrace : WordTrace (prefixWord ++ tailWord_672541) baseStart_672541 baseEnd_672541 := by
    simpa [prefixWord, tailWord_672541, baseEnd_672541] using wordTrace_append hprefix tailTrace_672541
  have hstable : (prefixWord ++ tailWord_672541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672541).length < 2 ^ (prefixWord ++ tailWord_672541).sum := by decide
  have hdescent : baseEnd_672541 < baseStart_672541 := by decide
  rcases family_descends (prefixWord ++ tailWord_672541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672563 : List Nat := [1, 1, 1, 2, 6, 1, 2, 1, 2, 3, 3]
def baseStart_672563 : Nat := 118140960795 + 672563 * 2 ^ 59
def prefixEnd_672563 : Nat := 4983230072969 + 3 ^ 40 * 672563 * 2
def baseEnd_672563 : Nat := 345348089429957327869445

theorem tailTrace_672563 : CollatzResearch.WordTrace tailWord_672563 prefixEnd_672563 345348089429957327869445 := by
  unfold tailWord_672563
  simp only [CollatzResearch.WordTrace]
  refine ⟨24530387862426590460670343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16353591908284393640446895 24530387862426590460670343)
  ·
    refine ⟨36795581793639885691005515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24530387862426590460670343 36795581793639885691005515)
    ·
      refine ⟨55193372690459828536508273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36795581793639885691005515 55193372690459828536508273)
      ·
        refine ⟨41395029517844871402381205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55193372690459828536508273 41395029517844871402381205)
        ·
          refine ⟨1940392008648978346986619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41395029517844871402381205 1940392008648978346986619)
          ·
            refine ⟨2910588012973467520479929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1940392008648978346986619 2910588012973467520479929)
            ·
              refine ⟨2182941009730100640359947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2910588012973467520479929 2182941009730100640359947)
              ·
                refine ⟨3274411514595150960539921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2182941009730100640359947 3274411514595150960539921)
                ·
                  refine ⟨2455808635946363220404941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3274411514595150960539921 2455808635946363220404941)
                  ·
                    refine ⟨920928238479886207651853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2455808635946363220404941 920928238479886207651853)
                    ·
                      refine ⟨345348089429957327869445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 920928238479886207651853 345348089429957327869445)
                      ·
                        rfl

theorem cell23_672563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 3, 3].length) (baseStart_672563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672563 prefixEnd_672563 := by exact prefixLift 672563
  have htrace : WordTrace (prefixWord ++ tailWord_672563) baseStart_672563 baseEnd_672563 := by
    simpa [prefixWord, tailWord_672563, baseEnd_672563] using wordTrace_append hprefix tailTrace_672563
  have hstable : (prefixWord ++ tailWord_672563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672563).length < 2 ^ (prefixWord ++ tailWord_672563).sum := by decide
  have hdescent : baseEnd_672563 < baseStart_672563 := by decide
  rcases family_descends (prefixWord ++ tailWord_672563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672564 : List Nat := [2, 5, 1, 1, 3, 2, 1, 1, 1, 4, 2]
def baseStart_672564 : Nat := 118140960795 + 672564 * 2 ^ 59
def prefixEnd_672564 : Nat := 4983230072969 + 3 ^ 40 * 672564 * 2
def baseEnd_672564 : Nat := 345348602910611823956941

theorem tailTrace_672564 : CollatzResearch.WordTrace tailWord_672564 prefixEnd_672564 345348602910611823956941 := by
  unfold tailWord_672564
  simp only [CollatzResearch.WordTrace]
  refine ⟨12265212167711483815728373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16353616223615311754304497 12265212167711483815728373)
  ·
    refine ⟨1149863640722951607724535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12265212167711483815728373 1149863640722951607724535)
    ·
      refine ⟨1724795461084427411586803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1149863640722951607724535 1724795461084427411586803)
      ·
        refine ⟨2587193191626641117380205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1724795461084427411586803 2587193191626641117380205)
        ·
          refine ⟨970197446859990419017577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2587193191626641117380205 970197446859990419017577)
          ·
            refine ⟨727648085144992814263183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 970197446859990419017577 727648085144992814263183)
            ·
              refine ⟨1091472127717489221394775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 727648085144992814263183 1091472127717489221394775)
              ·
                refine ⟨1637208191576233832092163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1091472127717489221394775 1637208191576233832092163)
                ·
                  refine ⟨2455812287364350748138245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1637208191576233832092163 2455812287364350748138245)
                  ·
                    refine ⟨460464803880815765275921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2455812287364350748138245 460464803880815765275921)
                    ·
                      refine ⟨345348602910611823956941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 460464803880815765275921 345348602910611823956941)
                      ·
                        rfl

theorem cell23_672564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_672564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672564 prefixEnd_672564 := by exact prefixLift 672564
  have htrace : WordTrace (prefixWord ++ tailWord_672564) baseStart_672564 baseEnd_672564 := by
    simpa [prefixWord, tailWord_672564, baseEnd_672564] using wordTrace_append hprefix tailTrace_672564
  have hstable : (prefixWord ++ tailWord_672564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672564).length < 2 ^ (prefixWord ++ tailWord_672564).sum := by decide
  have hdescent : baseEnd_672564 < baseStart_672564 := by decide
  rcases family_descends (prefixWord ++ tailWord_672564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672610 : List Nat := [3, 3, 2, 1, 3, 1, 1, 1, 1, 2, 5]
def baseStart_672610 : Nat := 118140960795 + 672610 * 2 ^ 59
def prefixEnd_672610 : Nat := 4983230072969 + 3 ^ 40 * 672610 * 2
def baseEnd_672610 : Nat := 345372223020718643981729

theorem tailTrace_672610 : CollatzResearch.WordTrace tailWord_672610 prefixEnd_672610 345372223020718643981729 := by
  unfold tailWord_672610
  simp only [CollatzResearch.WordTrace]
  refine ⟨6133025523314079371907821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16354734728837544991754189 6133025523314079371907821)
  ·
    refine ⟨2299884571242779764465433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6133025523314079371907821 2299884571242779764465433)
    ·
      refine ⟨1724913428432084823349075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2299884571242779764465433 1724913428432084823349075)
      ·
        refine ⟨2587370142648127235023613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1724913428432084823349075 2587370142648127235023613)
        ·
          refine ⟨970263803493047713133855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2587370142648127235023613 970263803493047713133855)
          ·
            refine ⟨1455395705239571569700783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 970263803493047713133855 1455395705239571569700783)
            ·
              refine ⟨2183093557859357354551175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1455395705239571569700783 2183093557859357354551175)
              ·
                refine ⟨3274640336789036031826763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2183093557859357354551175 3274640336789036031826763)
                ·
                  refine ⟨4911960505183554047740145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3274640336789036031826763 4911960505183554047740145)
                  ·
                    refine ⟨3683970378887665535805109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4911960505183554047740145 3683970378887665535805109)
                    ·
                      refine ⟨345372223020718643981729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3683970378887665535805109 345372223020718643981729)
                      ·
                        rfl

theorem cell23_672610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_672610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672610 prefixEnd_672610 := by exact prefixLift 672610
  have htrace : WordTrace (prefixWord ++ tailWord_672610) baseStart_672610 baseEnd_672610 := by
    simpa [prefixWord, tailWord_672610, baseEnd_672610] using wordTrace_append hprefix tailTrace_672610
  have hstable : (prefixWord ++ tailWord_672610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672610).length < 2 ^ (prefixWord ++ tailWord_672610).sum := by decide
  have hdescent : baseEnd_672610 < baseStart_672610 := by decide
  rcases family_descends (prefixWord ++ tailWord_672610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672660 : List Nat := [2, 4, 2, 1, 1, 1, 4, 2, 6]
def baseStart_672660 : Nat := 118140960795 + 672660 * 2 ^ 59
def prefixEnd_672660 : Nat := 4983230072969 + 3 ^ 40 * 672660 * 2
def baseEnd_672660 : Nat := 38377544117049272039611

theorem tailTrace_672660 : CollatzResearch.WordTrace tailWord_672660 prefixEnd_672660 38377544117049272039611 := by
  unfold tailWord_672660
  simp only [CollatzResearch.WordTrace]
  refine ⟨12266962871537588013475717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16355950495383450684634289 12266962871537588013475717)
  ·
    refine ⟨2300055538413297752526697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12266962871537588013475717 2300055538413297752526697)
    ·
      refine ⟨1725041653809973314395023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2300055538413297752526697 1725041653809973314395023)
      ·
        refine ⟨2587562480714959971592535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1725041653809973314395023 2587562480714959971592535)
        ·
          refine ⟨3881343721072439957388803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2587562480714959971592535 3881343721072439957388803)
          ·
            refine ⟨5822015581608659936083205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3881343721072439957388803 5822015581608659936083205)
            ·
              refine ⟨1091627921551623738015601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5822015581608659936083205 1091627921551623738015601)
              ·
                refine ⟨818720941163717803511701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1091627921551623738015601 818720941163717803511701)
                ·
                  refine ⟨38377544117049272039611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 818720941163717803511701 38377544117049272039611)
                  ·
                    rfl

theorem cell23_672660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_672660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672660 prefixEnd_672660 := by exact prefixLift 672660
  have htrace : WordTrace (prefixWord ++ tailWord_672660) baseStart_672660 baseEnd_672660 := by
    simpa [prefixWord, tailWord_672660, baseEnd_672660] using wordTrace_append hprefix tailTrace_672660
  have hstable : (prefixWord ++ tailWord_672660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672660).length < 2 ^ (prefixWord ++ tailWord_672660).sum := by decide
  have hdescent : baseEnd_672660 < baseStart_672660 := by decide
  rcases family_descends (prefixWord ++ tailWord_672660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672697 : List Nat := [1, 2, 1, 4, 2, 2, 3, 1, 2, 3, 2]
def baseStart_672697 : Nat := 118140960795 + 672697 * 2 ^ 59
def prefixEnd_672697 : Nat := 4983230072969 + 3 ^ 40 * 672697 * 2
def baseEnd_672697 : Nat := 345416895837659803593829

theorem tailTrace_672697 : CollatzResearch.WordTrace tailWord_672697 prefixEnd_672697 345416895837659803593829 := by
  unfold tailWord_672697
  simp only [CollatzResearch.WordTrace]
  refine ⟨24535275243941131346048345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16356850162627420897365563 24535275243941131346048345)
  ·
    refine ⟨18401456432955848509536259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24535275243941131346048345 18401456432955848509536259)
    ·
      refine ⟨27602184649433772764304389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18401456432955848509536259 27602184649433772764304389)
      ·
        refine ⟨5175409621768832393307073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27602184649433772764304389 5175409621768832393307073)
        ·
          refine ⟨3881557216326624294980305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5175409621768832393307073 3881557216326624294980305)
          ·
            refine ⟨2911167912244968221235229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3881557216326624294980305 2911167912244968221235229)
            ·
              refine ⟨1091687967091863082963211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2911167912244968221235229 1091687967091863082963211)
              ·
                refine ⟨1637531950637794624444817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1091687967091863082963211 1637531950637794624444817)
                ·
                  refine ⟨1228148962978345968333613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1637531950637794624444817 1228148962978345968333613)
                  ·
                    refine ⟨460555861116879738125105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1228148962978345968333613 460555861116879738125105)
                    ·
                      refine ⟨345416895837659803593829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 460555861116879738125105 345416895837659803593829)
                      ·
                        rfl

theorem cell23_672697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_672697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672697 prefixEnd_672697 := by exact prefixLift 672697
  have htrace : WordTrace (prefixWord ++ tailWord_672697) baseStart_672697 baseEnd_672697 := by
    simpa [prefixWord, tailWord_672697, baseEnd_672697] using wordTrace_append hprefix tailTrace_672697
  have hstable : (prefixWord ++ tailWord_672697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672697).length < 2 ^ (prefixWord ++ tailWord_672697).sum := by decide
  have hdescent : baseEnd_672697 < baseStart_672697 := by decide
  rcases family_descends (prefixWord ++ tailWord_672697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672704 : List Nat := [2, 1, 1, 2, 3, 4, 2, 3, 1, 1, 3]
def baseStart_672704 : Nat := 118140960795 + 672704 * 2 ^ 59
def prefixEnd_672704 : Nat := 4983230072969 + 3 ^ 40 * 672704 * 2
def baseEnd_672704 : Nat := 345420490202241276206297

theorem tailTrace_672704 : CollatzResearch.WordTrace tailWord_672704 prefixEnd_672704 345420490202241276206297 := by
  unfold tailWord_672704
  simp only [CollatzResearch.WordTrace]
  refine ⟨12267765277457885770776583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16357020369943847694368777 12267765277457885770776583)
  ·
    refine ⟨18401647916186828656164875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12267765277457885770776583 18401647916186828656164875)
    ·
      refine ⟨27602471874280242984247313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18401647916186828656164875 27602471874280242984247313)
      ·
        refine ⟨20701853905710182238185485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27602471874280242984247313 20701853905710182238185485)
        ·
          refine ⟨7763195214641318339319557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20701853905710182238185485 7763195214641318339319557)
          ·
            refine ⟨1455599102745247188622417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7763195214641318339319557 1455599102745247188622417)
            ·
              refine ⟨1091699327058935391466813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1455599102745247188622417 1091699327058935391466813)
              ·
                refine ⟨409387247647100771800055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1091699327058935391466813 409387247647100771800055)
                ·
                  refine ⟨614080871470651157700083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 409387247647100771800055 614080871470651157700083)
                  ·
                    refine ⟨921121307205976736550125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 614080871470651157700083 921121307205976736550125)
                    ·
                      refine ⟨345420490202241276206297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 921121307205976736550125 345420490202241276206297)
                      ·
                        rfl

theorem cell23_672704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 3, 1, 1, 3].length) (baseStart_672704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672704 prefixEnd_672704 := by exact prefixLift 672704
  have htrace : WordTrace (prefixWord ++ tailWord_672704) baseStart_672704 baseEnd_672704 := by
    simpa [prefixWord, tailWord_672704, baseEnd_672704] using wordTrace_append hprefix tailTrace_672704
  have hstable : (prefixWord ++ tailWord_672704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672704).length < 2 ^ (prefixWord ++ tailWord_672704).sum := by decide
  have hdescent : baseEnd_672704 < baseStart_672704 := by decide
  rcases family_descends (prefixWord ++ tailWord_672704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672730 : List Nat := [3, 1, 1, 2, 4, 2, 1, 2, 1, 1, 5]
def baseStart_672730 : Nat := 118140960795 + 672730 * 2 ^ 59
def prefixEnd_672730 : Nat := 4983230072969 + 3 ^ 40 * 672730 * 2
def baseEnd_672730 : Nat := 345433840699258174481177

theorem tailTrace_672730 : CollatzResearch.WordTrace tailWord_672730 prefixEnd_672730 345433840699258174481177 := by
  unfold tailWord_672730
  simp only [CollatzResearch.WordTrace]
  refine ⟨6134119713205394495499911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16357652568547718654666429 6134119713205394495499911)
  ·
    refine ⟨9201179569808091743249867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6134119713205394495499911 9201179569808091743249867)
    ·
      refine ⟨13801769354712137614874801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9201179569808091743249867 13801769354712137614874801)
      ·
        refine ⟨10351327016034103211156101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13801769354712137614874801 10351327016034103211156101)
        ·
          refine ⟨1940873815506394352091769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10351327016034103211156101 1940873815506394352091769)
          ·
            refine ⟨1455655361629795764068827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1940873815506394352091769 1455655361629795764068827)
            ·
              refine ⟨2183483042444693646103241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1455655361629795764068827 2183483042444693646103241)
              ·
                refine ⟨1637612281833520234577431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2183483042444693646103241 1637612281833520234577431)
                ·
                  refine ⟨2456418422750280351866147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1637612281833520234577431 2456418422750280351866147)
                  ·
                    refine ⟨3684627634125420527799221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2456418422750280351866147 3684627634125420527799221)
                    ·
                      refine ⟨345433840699258174481177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3684627634125420527799221 345433840699258174481177)
                      ·
                        rfl

theorem cell23_672730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_672730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672730 prefixEnd_672730 := by exact prefixLift 672730
  have htrace : WordTrace (prefixWord ++ tailWord_672730) baseStart_672730 baseEnd_672730 := by
    simpa [prefixWord, tailWord_672730, baseEnd_672730] using wordTrace_append hprefix tailTrace_672730
  have hstable : (prefixWord ++ tailWord_672730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672730).length < 2 ^ (prefixWord ++ tailWord_672730).sum := by decide
  have hdescent : baseEnd_672730 < baseStart_672730 := by decide
  rcases family_descends (prefixWord ++ tailWord_672730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672750 : List Nat := [4, 1, 2, 1, 4, 1, 1, 9]
def baseStart_672750 : Nat := 118140960795 + 672750 * 2 ^ 59
def prefixEnd_672750 : Nat := 4983230072969 + 3 ^ 40 * 672750 * 2
def baseEnd_672750 : Nat := 12794226307864744304855

theorem tailTrace_672750 : CollatzResearch.WordTrace tailWord_672750 prefixEnd_672750 12794226307864744304855 := by
  unfold tailWord_672750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3067151039093640174715963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16358138875166080931818469 3067151039093640174715963)
  ·
    refine ⟨4600726558640460262073945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3067151039093640174715963 4600726558640460262073945)
    ·
      refine ⟨3450544918980345196555459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4600726558640460262073945 3450544918980345196555459)
      ·
        refine ⟨5175817378470517794833189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3450544918980345196555459 5175817378470517794833189)
        ·
          refine ⟨970465758463222086531223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5175817378470517794833189 970465758463222086531223)
          ·
            refine ⟨1455698637694833129796835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 970465758463222086531223 1455698637694833129796835)
            ·
              refine ⟨2183547956542249694695253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1455698637694833129796835 2183547956542249694695253)
              ·
                refine ⟨12794226307864744304855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2183547956542249694695253 12794226307864744304855)
                ·
                  rfl

theorem cell23_672750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 9].length) (baseStart_672750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672750 prefixEnd_672750 := by exact prefixLift 672750
  have htrace : WordTrace (prefixWord ++ tailWord_672750) baseStart_672750 baseEnd_672750 := by
    simpa [prefixWord, tailWord_672750, baseEnd_672750] using wordTrace_append hprefix tailTrace_672750
  have hstable : (prefixWord ++ tailWord_672750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672750).length < 2 ^ (prefixWord ++ tailWord_672750).sum := by decide
  have hdescent : baseEnd_672750 < baseStart_672750 := by decide
  rcases family_descends (prefixWord ++ tailWord_672750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672773 : List Nat := [1, 3, 1, 1, 2, 3, 1, 2, 2, 2, 5]
def baseStart_672773 : Nat := 118140960795 + 672773 * 2 ^ 59
def prefixEnd_672773 : Nat := 4983230072969 + 3 ^ 40 * 672773 * 2
def baseEnd_672773 : Nat := 345455920367401506243479

theorem tailTrace_672773 : CollatzResearch.WordTrace tailWord_672773 prefixEnd_672773 345455920367401506243479 := by
  unfold tailWord_672773
  simp only [CollatzResearch.WordTrace]
  refine ⟨24538047191665796325814973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16358698127777197550543315 24538047191665796325814973)
  ·
    refine ⟨9201767696874673622180615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24538047191665796325814973 9201767696874673622180615)
    ·
      refine ⟨13802651545312010433270923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9201767696874673622180615 13802651545312010433270923)
      ·
        refine ⟨20703977317968015649906385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13802651545312010433270923 20703977317968015649906385)
        ·
          refine ⟨15527982988476011737429789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20703977317968015649906385 15527982988476011737429789)
          ·
            refine ⟨5822993620678504401536171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15527982988476011737429789 5822993620678504401536171)
            ·
              refine ⟨8734490431017756602304257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5822993620678504401536171 8734490431017756602304257)
              ·
                refine ⟨6550867823263317451728193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8734490431017756602304257 6550867823263317451728193)
                ·
                  refine ⟨4913150867447488088796145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6550867823263317451728193 4913150867447488088796145)
                  ·
                    refine ⟨3684863150585616066597109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4913150867447488088796145 3684863150585616066597109)
                    ·
                      refine ⟨345455920367401506243479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3684863150585616066597109 345455920367401506243479)
                      ·
                        rfl

theorem cell23_672773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_672773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672773 prefixEnd_672773 := by exact prefixLift 672773
  have htrace : WordTrace (prefixWord ++ tailWord_672773) baseStart_672773 baseEnd_672773 := by
    simpa [prefixWord, tailWord_672773, baseEnd_672773] using wordTrace_append hprefix tailTrace_672773
  have hstable : (prefixWord ++ tailWord_672773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672773).length < 2 ^ (prefixWord ++ tailWord_672773).sum := by decide
  have hdescent : baseEnd_672773 < baseStart_672773 := by decide
  rcases family_descends (prefixWord ++ tailWord_672773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672778 : List Nat := [3, 1, 2, 2, 3, 2, 3, 2, 1, 2, 2]
def baseStart_672778 : Nat := 118140960795 + 672778 * 2 ^ 59
def prefixEnd_672778 : Nat := 4983230072969 + 3 ^ 40 * 672778 * 2
def baseEnd_672778 : Nat := 345458487770673986680957

theorem tailTrace_672778 : CollatzResearch.WordTrace tailWord_672778 prefixEnd_672778 345458487770673986680957 := by
  unfold tailWord_672778
  simp only [CollatzResearch.WordTrace]
  refine ⟨6134557389161920544936747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16358819704431788119831325 6134557389161920544936747)
  ·
    refine ⟨9201836083742880817405121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6134557389161920544936747 9201836083742880817405121)
    ·
      refine ⟨6901377062807160613053841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9201836083742880817405121 6901377062807160613053841)
      ·
        refine ⟨5176032797105370459790381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6901377062807160613053841 5176032797105370459790381)
        ·
          refine ⟨1941012298914513922421393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5176032797105370459790381 1941012298914513922421393)
          ·
            refine ⟨1455759224185885441816045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1941012298914513922421393 1455759224185885441816045)
            ·
              refine ⟨545909709069707040681017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1455759224185885441816045 545909709069707040681017)
              ·
                refine ⟨409432281802280280510763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 545909709069707040681017 409432281802280280510763)
                ·
                  refine ⟨614148422703420420766145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 409432281802280280510763 614148422703420420766145)
                  ·
                    refine ⟨460611317027565315574609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 614148422703420420766145 460611317027565315574609)
                    ·
                      refine ⟨345458487770673986680957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 460611317027565315574609 345458487770673986680957)
                      ·
                        rfl

theorem cell23_672778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 2, 1, 2, 2].length) (baseStart_672778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672778 prefixEnd_672778 := by exact prefixLift 672778
  have htrace : WordTrace (prefixWord ++ tailWord_672778) baseStart_672778 baseEnd_672778 := by
    simpa [prefixWord, tailWord_672778, baseEnd_672778] using wordTrace_append hprefix tailTrace_672778
  have hstable : (prefixWord ++ tailWord_672778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672778).length < 2 ^ (prefixWord ++ tailWord_672778).sum := by decide
  have hdescent : baseEnd_672778 < baseStart_672778 := by decide
  rcases family_descends (prefixWord ++ tailWord_672778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672793 : List Nat := [1, 2, 1, 2, 1, 1, 4, 3, 2, 6]
def baseStart_672793 : Nat := 118140960795 + 672793 * 2 ^ 59
def prefixEnd_672793 : Nat := 4983230072969 + 3 ^ 40 * 672793 * 2
def baseEnd_672793 : Nat := 115155396660163809331129

theorem tailTrace_672793 : CollatzResearch.WordTrace tailWord_672793 prefixEnd_672793 115155396660163809331129 := by
  unfold tailWord_672793
  simp only [CollatzResearch.WordTrace]
  refine ⟨24538776651593339741543033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16359184434395559827695355 24538776651593339741543033)
  ·
    refine ⟨18404082488695004806157275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24538776651593339741543033 18404082488695004806157275)
    ·
      refine ⟨27606123733042507209235913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18404082488695004806157275 27606123733042507209235913)
      ·
        refine ⟨20704592799781880406926935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27606123733042507209235913 20704592799781880406926935)
        ·
          refine ⟨31056889199672820610390403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20704592799781880406926935 31056889199672820610390403)
          ·
            refine ⟨46585333799509230915585605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31056889199672820610390403 46585333799509230915585605)
            ·
              refine ⟨8734750087407980796672301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46585333799509230915585605 8734750087407980796672301)
              ·
                refine ⟨3275531282777992798752113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8734750087407980796672301 3275531282777992798752113)
                ·
                  refine ⟨2456648462083494599064085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3275531282777992798752113 2456648462083494599064085)
                  ·
                    refine ⟨115155396660163809331129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2456648462083494599064085 115155396660163809331129)
                    ·
                      rfl

theorem cell23_672793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 6].length) (baseStart_672793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672793 prefixEnd_672793 := by exact prefixLift 672793
  have htrace : WordTrace (prefixWord ++ tailWord_672793) baseStart_672793 baseEnd_672793 := by
    simpa [prefixWord, tailWord_672793, baseEnd_672793] using wordTrace_append hprefix tailTrace_672793
  have hstable : (prefixWord ++ tailWord_672793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672793).length < 2 ^ (prefixWord ++ tailWord_672793).sum := by decide
  have hdescent : baseEnd_672793 < baseStart_672793 := by decide
  rcases family_descends (prefixWord ++ tailWord_672793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672804 : List Nat := [2, 3, 1, 4, 1, 2, 1, 1, 3, 3, 2]
def baseStart_672804 : Nat := 118140960795 + 672804 * 2 ^ 59
def prefixEnd_672804 : Nat := 4983230072969 + 3 ^ 40 * 672804 * 2
def baseEnd_672804 : Nat := 345471838267690884955837

theorem tailTrace_672804 : CollatzResearch.WordTrace tailWord_672804 prefixEnd_672804 345471838267690884955837 := by
  unfold tailWord_672804
  simp only [CollatzResearch.WordTrace]
  refine ⟨12269588927276744310096733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16359451903035659080128977 12269588927276744310096733)
  ·
    refine ⟨4601095847728779116286275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12269588927276744310096733 4601095847728779116286275)
    ·
      refine ⟨6901643771593168674429413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4601095847728779116286275 6901643771593168674429413)
      ·
        refine ⟨1294058207173719126455515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6901643771593168674429413 1294058207173719126455515)
        ·
          refine ⟨1941087310760578689683273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1294058207173719126455515 1941087310760578689683273)
          ·
            refine ⟨1455815483070434017262455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1941087310760578689683273 1455815483070434017262455)
            ·
              refine ⟨2183723224605651025893683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1455815483070434017262455 2183723224605651025893683)
              ·
                refine ⟨3275584836908476538840525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2183723224605651025893683 3275584836908476538840525)
                ·
                  refine ⟨1228344313840678702065197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3275584836908476538840525 1228344313840678702065197)
                  ·
                    refine ⟨460629117690254513274449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1228344313840678702065197 460629117690254513274449)
                    ·
                      refine ⟨345471838267690884955837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 460629117690254513274449 345471838267690884955837)
                      ·
                        rfl

theorem cell23_672804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_672804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672804 prefixEnd_672804 := by exact prefixLift 672804
  have htrace : WordTrace (prefixWord ++ tailWord_672804) baseStart_672804 baseEnd_672804 := by
    simpa [prefixWord, tailWord_672804, baseEnd_672804] using wordTrace_append hprefix tailTrace_672804
  have hstable : (prefixWord ++ tailWord_672804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672804).length < 2 ^ (prefixWord ++ tailWord_672804).sum := by decide
  have hdescent : baseEnd_672804 < baseStart_672804 := by decide
  rcases family_descends (prefixWord ++ tailWord_672804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672817 : List Nat := [1, 2, 2, 3, 1, 2, 3, 2, 1, 4, 2]
def baseStart_672817 : Nat := 118140960795 + 672817 * 2 ^ 59
def prefixEnd_672817 : Nat := 4983230072969 + 3 ^ 40 * 672817 * 2
def baseEnd_672817 : Nat := 345478513516199334093277

theorem tailTrace_672817 : CollatzResearch.WordTrace tailWord_672817 prefixEnd_672817 345478513516199334093277 := by
  unfold tailWord_672817
  simp only [CollatzResearch.WordTrace]
  refine ⟨24539652003506391840416705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16359768002337594560277803 24539652003506391840416705)
  ·
    refine ⟨18404739002629793880312529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24539652003506391840416705 18404739002629793880312529)
    ·
      refine ⟨13803554251972345410234397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18404739002629793880312529 13803554251972345410234397)
      ·
        refine ⟨5176332844489629528837899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13803554251972345410234397 5176332844489629528837899)
        ·
          refine ⟨7764499266734444293256849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5176332844489629528837899 7764499266734444293256849)
          ·
            refine ⟨5823374450050833219942637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7764499266734444293256849 5823374450050833219942637)
            ·
              refine ⟨2183765418769062457478489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5823374450050833219942637 2183765418769062457478489)
              ·
                refine ⟨1637824064076796843108867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2183765418769062457478489 1637824064076796843108867)
                ·
                  refine ⟨2456736096115195264663301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1637824064076796843108867 2456736096115195264663301)
                  ·
                    refine ⟨460638018021599112124369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2456736096115195264663301 460638018021599112124369)
                    ·
                      refine ⟨345478513516199334093277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 460638018021599112124369 345478513516199334093277)
                      ·
                        rfl

theorem cell23_672817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_672817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672817 prefixEnd_672817 := by exact prefixLift 672817
  have htrace : WordTrace (prefixWord ++ tailWord_672817) baseStart_672817 baseEnd_672817 := by
    simpa [prefixWord, tailWord_672817, baseEnd_672817] using wordTrace_append hprefix tailTrace_672817
  have hstable : (prefixWord ++ tailWord_672817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672817).length < 2 ^ (prefixWord ++ tailWord_672817).sum := by decide
  have hdescent : baseEnd_672817 < baseStart_672817 := by decide
  rcases family_descends (prefixWord ++ tailWord_672817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672874 : List Nat := [3, 1, 3, 2, 2, 2, 2, 3, 5]
def baseStart_672874 : Nat := 118140960795 + 672874 * 2 ^ 59
def prefixEnd_672874 : Nat := 4983230072969 + 3 ^ 40 * 672874 * 2
def baseEnd_672874 : Nat := 38389753545945067897835

theorem tailTrace_672874 : CollatzResearch.WordTrace tailWord_672874 prefixEnd_672874 38389753545945067897835 := by
  unfold tailWord_672874
  simp only [CollatzResearch.WordTrace]
  refine ⟨6135432741074972643810419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16361153976199927050161117 6135432741074972643810419)
  ·
    refine ⟨9203149111612458965715629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6135432741074972643810419 9203149111612458965715629)
    ·
      refine ⟨3451180916854672112143361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9203149111612458965715629 3451180916854672112143361)
      ·
        refine ⟨2588385687641004084107521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3451180916854672112143361 2588385687641004084107521)
        ·
          refine ⟨1941289265730753063080641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2588385687641004084107521 1941289265730753063080641)
          ·
            refine ⟨1455966949298064797310481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1941289265730753063080641 1455966949298064797310481)
            ·
              refine ⟨1091975211973548597982861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1455966949298064797310481 1091975211973548597982861)
              ·
                refine ⟨409490704490080724243573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1091975211973548597982861 409490704490080724243573)
                ·
                  refine ⟨38389753545945067897835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 409490704490080724243573 38389753545945067897835)
                  ·
                    rfl

theorem cell23_672874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 3, 5].length) (baseStart_672874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672874 prefixEnd_672874 := by exact prefixLift 672874
  have htrace : WordTrace (prefixWord ++ tailWord_672874) baseStart_672874 baseEnd_672874 := by
    simpa [prefixWord, tailWord_672874, baseEnd_672874] using wordTrace_append hprefix tailTrace_672874
  have hstable : (prefixWord ++ tailWord_672874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672874).length < 2 ^ (prefixWord ++ tailWord_672874).sum := by decide
  have hdescent : baseEnd_672874 < baseStart_672874 := by decide
  rcases family_descends (prefixWord ++ tailWord_672874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672883 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 3, 10]
def baseStart_672883 : Nat := 118140960795 + 672883 * 2 ^ 59
def prefixEnd_672883 : Nat := 4983230072969 + 3 ^ 40 * 672883 * 2
def baseEnd_672883 : Nat := 115170801079798691955991

theorem tailTrace_672883 : CollatzResearch.WordTrace tailWord_672883 prefixEnd_672883 115170801079798691955991 := by
  unfold tailWord_672883
  simp only [CollatzResearch.WordTrace]
  refine ⟨24542059221267285112319303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16361372814178190074879535 24542059221267285112319303)
  ·
    refine ⟨36813088831900927668478955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24542059221267285112319303 36813088831900927668478955)
    ·
      refine ⟨55219633247851391502718433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36813088831900927668478955 55219633247851391502718433)
      ·
        refine ⟨41414724935888543627038825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55219633247851391502718433 41414724935888543627038825)
        ·
          refine ⟨31061043701916407720279119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41414724935888543627038825 31061043701916407720279119)
          ·
            refine ⟨46591565552874611580418679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31061043701916407720279119 46591565552874611580418679)
            ·
              refine ⟨69887348329311917370628019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46591565552874611580418679 69887348329311917370628019)
              ·
                refine ⟨104831022493967876055942029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69887348329311917370628019 104831022493967876055942029)
                ·
                  refine ⟨39311633435237953520978261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104831022493967876055942029 39311633435237953520978261)
                  ·
                    refine ⟨115170801079798691955991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 39311633435237953520978261 115170801079798691955991)
                    ·
                      rfl

theorem cell23_672883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 10].length) (baseStart_672883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672883 prefixEnd_672883 := by exact prefixLift 672883
  have htrace : WordTrace (prefixWord ++ tailWord_672883) baseStart_672883 baseEnd_672883 := by
    simpa [prefixWord, tailWord_672883, baseEnd_672883] using wordTrace_append hprefix tailTrace_672883
  have hstable : (prefixWord ++ tailWord_672883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672883).length < 2 ^ (prefixWord ++ tailWord_672883).sum := by decide
  have hdescent : baseEnd_672883 < baseStart_672883 := by decide
  rcases family_descends (prefixWord ++ tailWord_672883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672885 : List Nat := [1, 3, 4, 3, 1, 2, 1, 2, 2, 2, 2]
def baseStart_672885 : Nat := 118140960795 + 672885 * 2 ^ 59
def prefixEnd_672885 : Nat := 4983230072969 + 3 ^ 40 * 672885 * 2
def baseEnd_672885 : Nat := 345513430200705068042965

theorem tailTrace_672885 : CollatzResearch.WordTrace tailWord_672885 prefixEnd_672885 345513430200705068042965 := by
  unfold tailWord_672885
  simp only [CollatzResearch.WordTrace]
  refine ⟨24542132167260039453892109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16361421444840026302594739 24542132167260039453892109)
  ·
    refine ⟨9203299562722514795209541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24542132167260039453892109 9203299562722514795209541)
    ·
      refine ⟨1725618668010471524101789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9203299562722514795209541 1725618668010471524101789)
      ·
        refine ⟨647107000503926821538171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1725618668010471524101789 647107000503926821538171)
        ·
          refine ⟨970660500755890232307257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 647107000503926821538171 970660500755890232307257)
          ·
            refine ⟨727995375566917674230443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 970660500755890232307257 727995375566917674230443)
            ·
              refine ⟨1091993063350376511345665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 727995375566917674230443 1091993063350376511345665)
              ·
                refine ⟨818994797512782383509249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1091993063350376511345665 818994797512782383509249)
                ·
                  refine ⟨614246098134586787631937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 818994797512782383509249 614246098134586787631937)
                  ·
                    refine ⟨460684573600940090723953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 614246098134586787631937 460684573600940090723953)
                    ·
                      refine ⟨345513430200705068042965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 460684573600940090723953 345513430200705068042965)
                      ·
                        rfl

theorem cell23_672885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_672885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672885 prefixEnd_672885 := by exact prefixLift 672885
  have htrace : WordTrace (prefixWord ++ tailWord_672885) baseStart_672885 baseEnd_672885 := by
    simpa [prefixWord, tailWord_672885, baseEnd_672885] using wordTrace_append hprefix tailTrace_672885
  have hstable : (prefixWord ++ tailWord_672885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672885).length < 2 ^ (prefixWord ++ tailWord_672885).sum := by decide
  have hdescent : baseEnd_672885 < baseStart_672885 := by decide
  rcases family_descends (prefixWord ++ tailWord_672885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672951 : List Nat := [1, 1, 3, 1, 4, 1, 5, 2, 1, 4]
def baseStart_672951 : Nat := 118140960795 + 672951 * 2 ^ 59
def prefixEnd_672951 : Nat := 4983230072969 + 3 ^ 40 * 672951 * 2
def baseEnd_672951 : Nat := 115182439974633936605887

theorem tailTrace_672951 : CollatzResearch.WordTrace tailWord_672951 prefixEnd_672951 115182439974633936605887 := by
  unfold tailWord_672951
  simp only [CollatzResearch.WordTrace]
  refine ⟨24544539385020932725794707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16363026256680621817196471 24544539385020932725794707)
  ·
    refine ⟨36816809077531399088692061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24544539385020932725794707 36816809077531399088692061)
    ·
      refine ⟨13806303404074274658259523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36816809077531399088692061 13806303404074274658259523)
      ·
        refine ⟨20709455106111411987389285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13806303404074274658259523 20709455106111411987389285)
        ·
          refine ⟨3883022832395889747635491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20709455106111411987389285 3883022832395889747635491)
          ·
            refine ⟨5824534248593834621453237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3883022832395889747635491 5824534248593834621453237)
            ·
              refine ⟨546050085805671995761241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5824534248593834621453237 546050085805671995761241)
              ·
                refine ⟨409537564354253996820931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 546050085805671995761241 409537564354253996820931)
                ·
                  refine ⟨614306346531380995231397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 409537564354253996820931 614306346531380995231397)
                  ·
                    refine ⟨115182439974633936605887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 614306346531380995231397 115182439974633936605887)
                    ·
                      rfl

theorem cell23_672951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 2, 1, 4].length) (baseStart_672951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672951 prefixEnd_672951 := by exact prefixLift 672951
  have htrace : WordTrace (prefixWord ++ tailWord_672951) baseStart_672951 baseEnd_672951 := by
    simpa [prefixWord, tailWord_672951, baseEnd_672951] using wordTrace_append hprefix tailTrace_672951
  have hstable : (prefixWord ++ tailWord_672951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672951).length < 2 ^ (prefixWord ++ tailWord_672951).sum := by decide
  have hdescent : baseEnd_672951 < baseStart_672951 := by decide
  rcases family_descends (prefixWord ++ tailWord_672951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672964 : List Nat := [2, 3, 3, 1, 3, 1, 1, 3, 6]
def baseStart_672964 : Nat := 118140960795 + 672964 * 2 ^ 59
def prefixEnd_672964 : Nat := 4983230072969 + 3 ^ 40 * 672964 * 2
def baseEnd_672964 : Nat := 38394888352490028772789

theorem tailTrace_672964 : CollatzResearch.WordTrace tailWord_672964 prefixEnd_672964 38394888352490028772789 := by
  unfold tailWord_672964
  simp only [CollatzResearch.WordTrace]
  refine ⟨12272506766986917973008973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16363342355982557297345297 12272506766986917973008973)
  ·
    refine ⟨4602190037620094239878365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12272506766986917973008973 4602190037620094239878365)
    ·
      refine ⟨1725821264107535339954387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4602190037620094239878365 1725821264107535339954387)
      ·
        refine ⟨2588731896161303009931581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1725821264107535339954387 2588731896161303009931581)
        ·
          refine ⟨970774461060488628724343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2588731896161303009931581 970774461060488628724343)
          ·
            refine ⟨1456161691590732943086515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 970774461060488628724343 1456161691590732943086515)
            ·
              refine ⟨2184242537386099414629773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1456161691590732943086515 2184242537386099414629773)
              ·
                refine ⟨819090951519787280486165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2184242537386099414629773 819090951519787280486165)
                ·
                  refine ⟨38394888352490028772789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 819090951519787280486165 38394888352490028772789)
                  ·
                    rfl

theorem cell23_672964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 6].length) (baseStart_672964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672964 prefixEnd_672964 := by exact prefixLift 672964
  have htrace : WordTrace (prefixWord ++ tailWord_672964) baseStart_672964 baseEnd_672964 := by
    simpa [prefixWord, tailWord_672964, baseEnd_672964] using wordTrace_append hprefix tailTrace_672964
  have hstable : (prefixWord ++ tailWord_672964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672964).length < 2 ^ (prefixWord ++ tailWord_672964).sum := by decide
  have hdescent : baseEnd_672964 < baseStart_672964 := by decide
  rcases family_descends (prefixWord ++ tailWord_672964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672967 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 3, 5, 2]
def baseStart_672967 : Nat := 118140960795 + 672967 * 2 ^ 59
def prefixEnd_672967 : Nat := 4983230072969 + 3 ^ 40 * 672967 * 2
def baseEnd_672967 : Nat := 345555535614373747217587

theorem tailTrace_672967 : CollatzResearch.WordTrace tailWord_672967 prefixEnd_672967 345555535614373747217587 := by
  unfold tailWord_672967
  simp only [CollatzResearch.WordTrace]
  refine ⟨24545122952962967458377155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16363415301975311638918103 24545122952962967458377155)
  ·
    refine ⟨36817684429444451187565733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24545122952962967458377155 36817684429444451187565733)
    ·
      refine ⟨6903315830520834597668575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36817684429444451187565733 6903315830520834597668575)
      ·
        refine ⟨10354973745781251896502863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6903315830520834597668575 10354973745781251896502863)
        ·
          refine ⟨15532460618671877844754295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10354973745781251896502863 15532460618671877844754295)
          ·
            refine ⟨23298690928007816767131443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15532460618671877844754295 23298690928007816767131443)
            ·
              refine ⟨34948036392011725150697165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23298690928007816767131443 34948036392011725150697165)
              ·
                refine ⟨13105513647004396931511437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34948036392011725150697165 13105513647004396931511437)
                ·
                  refine ⟨4914567617626648849316789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13105513647004396931511437 4914567617626648849316789)
                  ·
                    refine ⟨460740714152498329623449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4914567617626648849316789 460740714152498329623449)
                    ·
                      refine ⟨345555535614373747217587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 460740714152498329623449 345555535614373747217587)
                      ·
                        rfl

theorem cell23_672967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 5, 2].length) (baseStart_672967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_672967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_672967 prefixEnd_672967 := by exact prefixLift 672967
  have htrace : WordTrace (prefixWord ++ tailWord_672967) baseStart_672967 baseEnd_672967 := by
    simpa [prefixWord, tailWord_672967, baseEnd_672967] using wordTrace_append hprefix tailTrace_672967
  have hstable : (prefixWord ++ tailWord_672967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672967).length < 2 ^ (prefixWord ++ tailWord_672967).sum := by decide
  have hdescent : baseEnd_672967 < baseStart_672967 := by decide
  rcases family_descends (prefixWord ++ tailWord_672967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673014 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2]
def baseStart_673014 : Nat := 118140960795 + 673014 * 2 ^ 59
def prefixEnd_673014 : Nat := 4983230072969 + 3 ^ 40 * 673014 * 2
def baseEnd_673014 : Nat := 345579669205135063329871

theorem tailTrace_673014 : CollatzResearch.WordTrace tailWord_673014 prefixEnd_673014 345579669205135063329871 := by
  unfold tailWord_673014
  simp only [CollatzResearch.WordTrace]
  refine ⟨1534177323987043405333631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16364558122528462990225397 1534177323987043405333631)
  ·
    refine ⟨2301265985980565108000447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1534177323987043405333631 2301265985980565108000447)
    ·
      refine ⟨3451898978970847662000671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2301265985980565108000447 3451898978970847662000671)
      ·
        refine ⟨5177848468456271493001007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3451898978970847662000671 5177848468456271493001007)
        ·
          refine ⟨7766772702684407239501511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5177848468456271493001007 7766772702684407239501511)
          ·
            refine ⟨11650159054026610859252267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7766772702684407239501511 11650159054026610859252267)
            ·
              refine ⟨17475238581039916288878401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11650159054026610859252267 17475238581039916288878401)
              ·
                refine ⟨13106428935779937216658801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17475238581039916288878401 13106428935779937216658801)
                ·
                  refine ⟨9829821701834952912494101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13106428935779937216658801 9829821701834952912494101)
                  ·
                    refine ⟨460772892273513417773161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9829821701834952912494101 460772892273513417773161)
                    ·
                      refine ⟨345579669205135063329871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 460772892273513417773161 345579669205135063329871)
                      ·
                        rfl

theorem cell23_673014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_673014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673014 prefixEnd_673014 := by exact prefixLift 673014
  have htrace : WordTrace (prefixWord ++ tailWord_673014) baseStart_673014 baseEnd_673014 := by
    simpa [prefixWord, tailWord_673014, baseEnd_673014] using wordTrace_append hprefix tailTrace_673014
  have hstable : (prefixWord ++ tailWord_673014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673014).length < 2 ^ (prefixWord ++ tailWord_673014).sum := by decide
  have hdescent : baseEnd_673014 < baseStart_673014 := by decide
  rcases family_descends (prefixWord ++ tailWord_673014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673017 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 5, 2, 3]
def baseStart_673017 : Nat := 118140960795 + 673017 * 2 ^ 59
def prefixEnd_673017 : Nat := 4983230072969 + 3 ^ 40 * 673017 * 2
def baseEnd_673017 : Nat := 345581209647098551592357

theorem tailTrace_673017 : CollatzResearch.WordTrace tailWord_673017 prefixEnd_673017 345581209647098551592357 := by
  unfold tailWord_673017
  simp only [CollatzResearch.WordTrace]
  refine ⟨24546946602781825997697305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16364631068521217331798203 24546946602781825997697305)
  ·
    refine ⟨18410209952086369498272979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24546946602781825997697305 18410209952086369498272979)
    ·
      refine ⟨27615314928129554247409469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18410209952086369498272979 27615314928129554247409469)
      ·
        refine ⟨10355743098048582842778551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27615314928129554247409469 10355743098048582842778551)
        ·
          refine ⟨15533614647072874264167827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10355743098048582842778551 15533614647072874264167827)
          ·
            refine ⟨23300421970609311396251741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15533614647072874264167827 23300421970609311396251741)
            ·
              refine ⟨8737658238978491773594403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23300421970609311396251741 8737658238978491773594403)
              ·
                refine ⟨13106487358467737660391605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8737658238978491773594403 13106487358467737660391605)
                ·
                  refine ⟨1228733189856350405661713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13106487358467737660391605 1228733189856350405661713)
                  ·
                    refine ⟨921549892392262804246285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1228733189856350405661713 921549892392262804246285)
                    ·
                      refine ⟨345581209647098551592357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 921549892392262804246285 345581209647098551592357)
                      ·
                        rfl

theorem cell23_673017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_673017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673017 prefixEnd_673017 := by exact prefixLift 673017
  have htrace : WordTrace (prefixWord ++ tailWord_673017) baseStart_673017 baseEnd_673017 := by
    simpa [prefixWord, tailWord_673017, baseEnd_673017] using wordTrace_append hprefix tailTrace_673017
  have hstable : (prefixWord ++ tailWord_673017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673017).length < 2 ^ (prefixWord ++ tailWord_673017).sum := by decide
  have hdescent : baseEnd_673017 < baseStart_673017 := by decide
  rcases family_descends (prefixWord ++ tailWord_673017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673027 : List Nat := [1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 4]
def baseStart_673027 : Nat := 118140960795 + 673027 * 2 ^ 59
def prefixEnd_673027 : Nat := 4983230072969 + 3 ^ 40 * 673027 * 2
def baseEnd_673027 : Nat := 345586344453643512467311

theorem tailTrace_673027 : CollatzResearch.WordTrace tailWord_673027 prefixEnd_673027 345586344453643512467311 := by
  unfold tailWord_673027
  simp only [CollatzResearch.WordTrace]
  refine ⟨24547311332745597705561335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16364874221830398470374223 24547311332745597705561335)
  ·
    refine ⟨36820966999118396558342003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24547311332745597705561335 36820966999118396558342003)
    ·
      refine ⟨55231450498677594837513005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36820966999118396558342003 55231450498677594837513005)
      ·
        refine ⟨20711793937004098064067377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55231450498677594837513005 20711793937004098064067377)
        ·
          refine ⟨15533845452753073548050533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20711793937004098064067377 15533845452753073548050533)
          ·
            refine ⟨2912596022391201290259475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15533845452753073548050533 2912596022391201290259475)
            ·
              refine ⟨4368894033586801935389213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2912596022391201290259475 4368894033586801935389213)
              ·
                refine ⟨1638335262595050725770955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4368894033586801935389213 1638335262595050725770955)
                ·
                  refine ⟨2457502893892576088656433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1638335262595050725770955 2457502893892576088656433)
                  ·
                    refine ⟨1843127170419432066492325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2457502893892576088656433 1843127170419432066492325)
                    ·
                      refine ⟨345586344453643512467311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1843127170419432066492325 345586344453643512467311)
                      ·
                        rfl

theorem cell23_673027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 4].length) (baseStart_673027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673027 prefixEnd_673027 := by exact prefixLift 673027
  have htrace : WordTrace (prefixWord ++ tailWord_673027) baseStart_673027 baseEnd_673027 := by
    simpa [prefixWord, tailWord_673027, baseEnd_673027] using wordTrace_append hprefix tailTrace_673027
  have hstable : (prefixWord ++ tailWord_673027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673027).length < 2 ^ (prefixWord ++ tailWord_673027).sum := by decide
  have hdescent : baseEnd_673027 < baseStart_673027 := by decide
  rcases family_descends (prefixWord ++ tailWord_673027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673034 : List Nat := [3, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3]
def baseStart_673034 : Nat := 118140960795 + 673034 * 2 ^ 59
def prefixEnd_673034 : Nat := 4983230072969 + 3 ^ 40 * 673034 * 2
def baseEnd_673034 : Nat := 345589938818224985079779

theorem tailTrace_673034 : CollatzResearch.WordTrace tailWord_673034 prefixEnd_673034 345589938818224985079779 := by
  unfold tailWord_673034
  simp only [CollatzResearch.WordTrace]
  refine ⟨6136891660930059475266539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16365044429146825267377437 6136891660930059475266539)
  ·
    refine ⟨9205337491395089212899809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6136891660930059475266539 9205337491395089212899809)
    ·
      refine ⟨6904003118546316909674857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9205337491395089212899809 6904003118546316909674857)
      ·
        refine ⟨5178002338909737682256143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6904003118546316909674857 5178002338909737682256143)
        ·
          refine ⟨7767003508364606523384215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5178002338909737682256143 7767003508364606523384215)
          ·
            refine ⟨11650505262546909785076323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7767003508364606523384215 11650505262546909785076323)
            ·
              refine ⟨17475757893820364677614485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11650505262546909785076323 17475757893820364677614485)
              ·
                refine ⟨819176151272829594263179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17475757893820364677614485 819176151272829594263179)
                ·
                  refine ⟨1228764226909244391394769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 819176151272829594263179 1228764226909244391394769)
                  ·
                    refine ⟨921573170181933293546077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1228764226909244391394769 921573170181933293546077)
                    ·
                      refine ⟨345589938818224985079779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 921573170181933293546077 345589938818224985079779)
                      ·
                        rfl

theorem cell23_673034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_673034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673034 prefixEnd_673034 := by exact prefixLift 673034
  have htrace : WordTrace (prefixWord ++ tailWord_673034) baseStart_673034 baseEnd_673034 := by
    simpa [prefixWord, tailWord_673034, baseEnd_673034] using wordTrace_append hprefix tailTrace_673034
  have hstable : (prefixWord ++ tailWord_673034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673034).length < 2 ^ (prefixWord ++ tailWord_673034).sum := by decide
  have hdescent : baseEnd_673034 < baseStart_673034 := by decide
  rcases family_descends (prefixWord ++ tailWord_673034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673040 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 6]
def baseStart_673040 : Nat := 118140960795 + 673040 * 2 ^ 59
def prefixEnd_673040 : Nat := 4983230072969 + 3 ^ 40 * 673040 * 2
def baseEnd_673040 : Nat := 345593019702151961604751

theorem tailTrace_673040 : CollatzResearch.WordTrace tailWord_673040 prefixEnd_673040 345593019702151961604751 := by
  unfold tailWord_673040
  simp only [CollatzResearch.WordTrace]
  refine ⟨12273892740849250462892287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16365190321132333950523049 12273892740849250462892287)
  ·
    refine ⟨18410839111273875694338431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12273892740849250462892287 18410839111273875694338431)
    ·
      refine ⟨27616258666910813541507647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18410839111273875694338431 27616258666910813541507647)
      ·
        refine ⟨41424388000366220312261471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27616258666910813541507647 41424388000366220312261471)
        ·
          refine ⟨62136582000549330468392207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41424388000366220312261471 62136582000549330468392207)
          ·
            refine ⟨93204873000823995702588311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62136582000549330468392207 93204873000823995702588311)
            ·
              refine ⟨139807309501235993553882467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93204873000823995702588311 139807309501235993553882467)
              ·
                refine ⟨209710964251853990330823701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139807309501235993553882467 209710964251853990330823701)
                ·
                  refine ⟨9830201449305655796757361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 209710964251853990330823701 9830201449305655796757361)
                  ·
                    refine ⟨7372651086979241847568021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9830201449305655796757361 7372651086979241847568021)
                    ·
                      refine ⟨345593019702151961604751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7372651086979241847568021 345593019702151961604751)
                      ·
                        rfl

theorem cell23_673040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 6].length) (baseStart_673040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673040 prefixEnd_673040 := by exact prefixLift 673040
  have htrace : WordTrace (prefixWord ++ tailWord_673040) baseStart_673040 baseEnd_673040 := by
    simpa [prefixWord, tailWord_673040, baseEnd_673040] using wordTrace_append hprefix tailTrace_673040
  have hstable : (prefixWord ++ tailWord_673040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673040).length < 2 ^ (prefixWord ++ tailWord_673040).sum := by decide
  have hdescent : baseEnd_673040 < baseStart_673040 := by decide
  rcases family_descends (prefixWord ++ tailWord_673040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673042 : List Nat := [3, 2, 4, 2, 1, 1, 2, 3, 1, 1, 3]
def baseStart_673042 : Nat := 118140960795 + 673042 * 2 ^ 59
def prefixEnd_673042 : Nat := 4983230072969 + 3 ^ 40 * 673042 * 2
def baseEnd_673042 : Nat := 345594046663460953779743

theorem tailTrace_673042 : CollatzResearch.WordTrace tailWord_673042 prefixEnd_673042 345594046663460953779743 := by
  unfold tailWord_673042
  simp only [CollatzResearch.WordTrace]
  refine ⟨6136964606922813816839345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16365238951794170178238253 6136964606922813816839345)
  ·
    refine ⟨4602723455192110362629509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6136964606922813816839345 4602723455192110362629509)
    ·
      refine ⟨863010647848520692993033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4602723455192110362629509 863010647848520692993033)
      ·
        refine ⟨647257985886390519744775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 863010647848520692993033 647257985886390519744775)
        ·
          refine ⟨970886978829585779617163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 647257985886390519744775 970886978829585779617163)
          ·
            refine ⟨1456330468244378669425745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 970886978829585779617163 1456330468244378669425745)
            ·
              refine ⟨1092247851183284002069309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1456330468244378669425745 1092247851183284002069309)
              ·
                refine ⟨409592944193731500775991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1092247851183284002069309 409592944193731500775991)
                ·
                  refine ⟨614389416290597251163987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 409592944193731500775991 614389416290597251163987)
                  ·
                    refine ⟨921584124435895876745981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 614389416290597251163987 921584124435895876745981)
                    ·
                      refine ⟨345594046663460953779743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 921584124435895876745981 345594046663460953779743)
                      ·
                        rfl

theorem cell23_673042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_673042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673042 prefixEnd_673042 := by exact prefixLift 673042
  have htrace : WordTrace (prefixWord ++ tailWord_673042) baseStart_673042 baseEnd_673042 := by
    simpa [prefixWord, tailWord_673042, baseEnd_673042] using wordTrace_append hprefix tailTrace_673042
  have hstable : (prefixWord ++ tailWord_673042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673042).length < 2 ^ (prefixWord ++ tailWord_673042).sum := by decide
  have hdescent : baseEnd_673042 < baseStart_673042 := by decide
  rcases family_descends (prefixWord ++ tailWord_673042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673048 : List Nat := [2, 1, 2, 3, 1, 3, 1, 5, 1, 2, 2]
def baseStart_673048 : Nat := 118140960795 + 673048 * 2 ^ 59
def prefixEnd_673048 : Nat := 4983230072969 + 3 ^ 40 * 673048 * 2
def baseEnd_673048 : Nat := 345597127547387930304715

theorem tailTrace_673048 : CollatzResearch.WordTrace tailWord_673048 prefixEnd_673048 345597127547387930304715 := by
  unfold tailWord_673048
  simp only [CollatzResearch.WordTrace]
  refine ⟨12274038632834759146037899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16365384843779678861383865 12274038632834759146037899)
  ·
    refine ⟨18411057949252138719056849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12274038632834759146037899 18411057949252138719056849)
    ·
      refine ⟨13808293461939104039292637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18411057949252138719056849 13808293461939104039292637)
      ·
        refine ⟨5178110048227164014734739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13808293461939104039292637 5178110048227164014734739)
        ·
          refine ⟨7767165072340746022102109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5178110048227164014734739 7767165072340746022102109)
          ·
            refine ⟨2912686902127779758288291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7767165072340746022102109 2912686902127779758288291)
            ·
              refine ⟨4369030353191669637432437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2912686902127779758288291 4369030353191669637432437)
              ·
                refine ⟨409596595611719028509291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4369030353191669637432437 409596595611719028509291)
                ·
                  refine ⟨614394893417578542763937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 409596595611719028509291 614394893417578542763937)
                  ·
                    refine ⟨460796170063183907072953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 614394893417578542763937 460796170063183907072953)
                    ·
                      refine ⟨345597127547387930304715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 460796170063183907072953 345597127547387930304715)
                      ·
                        rfl

theorem cell23_673048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 5, 1, 2, 2].length) (baseStart_673048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673048 prefixEnd_673048 := by exact prefixLift 673048
  have htrace : WordTrace (prefixWord ++ tailWord_673048) baseStart_673048 baseEnd_673048 := by
    simpa [prefixWord, tailWord_673048, baseEnd_673048] using wordTrace_append hprefix tailTrace_673048
  have hstable : (prefixWord ++ tailWord_673048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673048).length < 2 ^ (prefixWord ++ tailWord_673048).sum := by decide
  have hdescent : baseEnd_673048 < baseStart_673048 := by decide
  rcases family_descends (prefixWord ++ tailWord_673048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673058 : List Nat := [3, 3, 1, 1, 4, 2, 1, 2, 2, 4]
def baseStart_673058 : Nat := 118140960795 + 673058 * 2 ^ 59
def prefixEnd_673058 : Nat := 4983230072969 + 3 ^ 40 * 673058 * 2
def baseEnd_673058 : Nat := 115200754117977630393223

theorem tailTrace_673058 : CollatzResearch.WordTrace tailWord_673058 prefixEnd_673058 115200754117977630393223 := by
  unfold tailWord_673058
  simp only [CollatzResearch.WordTrace]
  refine ⟨6137110498908322499984957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16365627997088859999959885 6137110498908322499984957)
  ·
    refine ⟨2301416437090620937494359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6137110498908322499984957 2301416437090620937494359)
    ·
      refine ⟨3452124655635931406241539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2301416437090620937494359 3452124655635931406241539)
      ·
        refine ⟨5178186983453897109362309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3452124655635931406241539 5178186983453897109362309)
        ·
          refine ⟨970910059397605708005433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5178186983453897109362309 970910059397605708005433)
          ·
            refine ⟨728182544548204281004075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 970910059397605708005433 728182544548204281004075)
            ·
              refine ⟨1092273816822306421506113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 728182544548204281004075 1092273816822306421506113)
              ·
                refine ⟨819205362616729816129585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1092273816822306421506113 819205362616729816129585)
                ·
                  refine ⟨614404021962547362097189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 819205362616729816129585 614404021962547362097189)
                  ·
                    refine ⟨115200754117977630393223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 614404021962547362097189 115200754117977630393223)
                    ·
                      rfl

theorem cell23_673058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_673058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673058 prefixEnd_673058 := by exact prefixLift 673058
  have htrace : WordTrace (prefixWord ++ tailWord_673058) baseStart_673058 baseEnd_673058 := by
    simpa [prefixWord, tailWord_673058, baseEnd_673058] using wordTrace_append hprefix tailTrace_673058
  have hstable : (prefixWord ++ tailWord_673058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673058).length < 2 ^ (prefixWord ++ tailWord_673058).sum := by decide
  have hdescent : baseEnd_673058 < baseStart_673058 := by decide
  rcases family_descends (prefixWord ++ tailWord_673058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673104 : List Nat := [2, 1, 1, 1, 1, 5, 2, 1, 3, 4, 2]
def baseStart_673104 : Nat := 118140960795 + 673104 * 2 ^ 59
def prefixEnd_673104 : Nat := 4983230072969 + 3 ^ 40 * 673104 * 2
def baseEnd_673104 : Nat := 345625882464039711204457

theorem tailTrace_673104 : CollatzResearch.WordTrace tailWord_673104 prefixEnd_673104 345625882464039711204457 := by
  unfold tailWord_673104
  simp only [CollatzResearch.WordTrace]
  refine ⟨12275059876733319928057183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16366746502311093237409577 12275059876733319928057183)
  ·
    refine ⟨18412589815099979892085775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12275059876733319928057183 18412589815099979892085775)
    ·
      refine ⟨27618884722649969838128663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18412589815099979892085775 27618884722649969838128663)
      ·
        refine ⟨41428327083974954757192995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27618884722649969838128663 41428327083974954757192995)
        ·
          refine ⟨62142490625962432135789493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41428327083974954757192995 62142490625962432135789493)
          ·
            refine ⟨5825858496183978012730265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62142490625962432135789493 5825858496183978012730265)
            ·
              refine ⟨4369393872137983509547699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5825858496183978012730265 4369393872137983509547699)
              ·
                refine ⟨6554090808206975264321549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4369393872137983509547699 6554090808206975264321549)
                ·
                  refine ⟨2457784053077615724120581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6554090808206975264321549 2457784053077615724120581)
                  ·
                    refine ⟨460834509952052948272609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2457784053077615724120581 460834509952052948272609)
                    ·
                      refine ⟨345625882464039711204457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 460834509952052948272609 345625882464039711204457)
                      ·
                        rfl

theorem cell23_673104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 3, 4, 2].length) (baseStart_673104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673104 prefixEnd_673104 := by exact prefixLift 673104
  have htrace : WordTrace (prefixWord ++ tailWord_673104) baseStart_673104 baseEnd_673104 := by
    simpa [prefixWord, tailWord_673104, baseEnd_673104] using wordTrace_append hprefix tailTrace_673104
  have hstable : (prefixWord ++ tailWord_673104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673104).length < 2 ^ (prefixWord ++ tailWord_673104).sum := by decide
  have hdescent : baseEnd_673104 < baseStart_673104 := by decide
  rcases family_descends (prefixWord ++ tailWord_673104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673107 : List Nat := [1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 5]
def baseStart_673107 : Nat := 118140960795 + 673107 * 2 ^ 59
def prefixEnd_673107 : Nat := 4983230072969 + 3 ^ 40 * 673107 * 2
def baseEnd_673107 : Nat := 345627422906003199466943

theorem tailTrace_673107 : CollatzResearch.WordTrace tailWord_673107 prefixEnd_673107 345627422906003199466943 := by
  unfold tailWord_673107
  simp only [CollatzResearch.WordTrace]
  refine ⟨24550229172455771368473575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16366819448303847578982383 24550229172455771368473575)
  ·
    refine ⟨36825343758683657052710363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24550229172455771368473575 36825343758683657052710363)
    ·
      refine ⟨55238015638025485579065545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36825343758683657052710363 55238015638025485579065545)
      ·
        refine ⟨41428511728519114184299159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55238015638025485579065545 41428511728519114184299159)
        ·
          refine ⟨62142767592778671276448739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41428511728519114184299159 62142767592778671276448739)
          ·
            refine ⟨93214151389168006914673109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62142767592778671276448739 93214151389168006914673109)
            ·
              refine ⟨2184706673183625162062651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 93214151389168006914673109 2184706673183625162062651)
              ·
                refine ⟨3277060009775437743093977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2184706673183625162062651 3277060009775437743093977)
                ·
                  refine ⟨2457795007331578307320483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3277060009775437743093977 2457795007331578307320483)
                  ·
                    refine ⟨3686692510997367460980725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2457795007331578307320483 3686692510997367460980725)
                    ·
                      refine ⟨345627422906003199466943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3686692510997367460980725 345627422906003199466943)
                      ·
                        rfl

theorem cell23_673107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 5].length) (baseStart_673107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673107 prefixEnd_673107 := by exact prefixLift 673107
  have htrace : WordTrace (prefixWord ++ tailWord_673107) baseStart_673107 baseEnd_673107 := by
    simpa [prefixWord, tailWord_673107, baseEnd_673107] using wordTrace_append hprefix tailTrace_673107
  have hstable : (prefixWord ++ tailWord_673107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673107).length < 2 ^ (prefixWord ++ tailWord_673107).sum := by decide
  have hdescent : baseEnd_673107 < baseStart_673107 := by decide
  rcases family_descends (prefixWord ++ tailWord_673107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673138 : List Nat := [3, 2, 1, 2, 1, 2, 3, 3, 2, 2, 2]
def baseStart_673138 : Nat := 118140960795 + 673138 * 2 ^ 59
def prefixEnd_673138 : Nat := 4983230072969 + 3 ^ 40 * 673138 * 2
def baseEnd_673138 : Nat := 345643340806292578179301

theorem tailTrace_673138 : CollatzResearch.WordTrace tailWord_673138 prefixEnd_673138 345643340806292578179301 := by
  unfold tailWord_673138
  simp only [CollatzResearch.WordTrace]
  refine ⟨6137839958835865915713017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16367573223562309108568045 6137839958835865915713017)
  ·
    refine ⟨4603379969126899436784763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6137839958835865915713017 4603379969126899436784763)
    ·
      refine ⟨6905069953690349155177145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4603379969126899436784763 6905069953690349155177145)
      ·
        refine ⟨5178802465267761866382859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6905069953690349155177145 5178802465267761866382859)
        ·
          refine ⟨7768203697901642799574289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5178802465267761866382859 7768203697901642799574289)
          ·
            refine ⟨5826152773426232099680717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7768203697901642799574289 5826152773426232099680717)
            ·
              refine ⟨2184807290034837037380269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5826152773426232099680717 2184807290034837037380269)
              ·
                refine ⟨819302733763063889017601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2184807290034837037380269 819302733763063889017601)
                ·
                  refine ⟨614477050322297916763201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 819302733763063889017601 614477050322297916763201)
                  ·
                    refine ⟨460857787741723437572401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 614477050322297916763201 460857787741723437572401)
                    ·
                      refine ⟨345643340806292578179301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 460857787741723437572401 345643340806292578179301)
                      ·
                        rfl

theorem cell23_673138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_673138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673138 prefixEnd_673138 := by exact prefixLift 673138
  have htrace : WordTrace (prefixWord ++ tailWord_673138) baseStart_673138 baseEnd_673138 := by
    simpa [prefixWord, tailWord_673138, baseEnd_673138] using wordTrace_append hprefix tailTrace_673138
  have hstable : (prefixWord ++ tailWord_673138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673138).length < 2 ^ (prefixWord ++ tailWord_673138).sum := by decide
  have hdescent : baseEnd_673138 < baseStart_673138 := by decide
  rcases family_descends (prefixWord ++ tailWord_673138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673157 : List Nat := [1, 3, 1, 1, 3, 1, 2, 3, 1, 7]
def baseStart_673157 : Nat := 118140960795 + 673157 * 2 ^ 59
def prefixEnd_673157 : Nat := 4983230072969 + 3 ^ 40 * 673157 * 2
def baseEnd_673157 : Nat := 115217698979576001280571

theorem tailTrace_673157 : CollatzResearch.WordTrace tailWord_673157 prefixEnd_673157 115217698979576001280571 := by
  unfold tailWord_673157
  simp only [CollatzResearch.WordTrace]
  refine ⟨24552052822274629907793725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16368035214849753271862483 24552052822274629907793725)
  ·
    refine ⟨9207019808352986215422647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24552052822274629907793725 9207019808352986215422647)
    ·
      refine ⟨13810529712529479323133971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9207019808352986215422647 13810529712529479323133971)
      ·
        refine ⟨20715794568794218984700957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13810529712529479323133971 20715794568794218984700957)
        ·
          refine ⟨7768422963297832119262859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20715794568794218984700957 7768422963297832119262859)
          ·
            refine ⟨11652634444946748178894289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7768422963297832119262859 11652634444946748178894289)
            ·
              refine ⟨8739475833710061134170717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11652634444946748178894289 8739475833710061134170717)
              ·
                refine ⟨3277303437641272925314019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8739475833710061134170717 3277303437641272925314019)
                ·
                  refine ⟨4915955156461909387971029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3277303437641272925314019 4915955156461909387971029)
                  ·
                    refine ⟨115217698979576001280571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4915955156461909387971029 115217698979576001280571)
                    ·
                      rfl

theorem cell23_673157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 7].length) (baseStart_673157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673157 prefixEnd_673157 := by exact prefixLift 673157
  have htrace : WordTrace (prefixWord ++ tailWord_673157) baseStart_673157 baseEnd_673157 := by
    simpa [prefixWord, tailWord_673157, baseEnd_673157] using wordTrace_append hprefix tailTrace_673157
  have hstable : (prefixWord ++ tailWord_673157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673157).length < 2 ^ (prefixWord ++ tailWord_673157).sum := by decide
  have hdescent : baseEnd_673157 < baseStart_673157 := by decide
  rcases family_descends (prefixWord ++ tailWord_673157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673181 : List Nat := [1, 4, 2, 1, 3, 1, 1, 1, 2, 5, 2]
def baseStart_673181 : Nat := 118140960795 + 673181 * 2 ^ 59
def prefixEnd_673181 : Nat := 4983230072969 + 3 ^ 40 * 673181 * 2
def baseEnd_673181 : Nat := 345665420474435909941603

theorem tailTrace_673181 : CollatzResearch.WordTrace tailWord_673181 prefixEnd_673181 345665420474435909941603 := by
  unfold tailWord_673181
  simp only [CollatzResearch.WordTrace]
  refine ⟨24552928174187682006667397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16368618782791788004444931 24552928174187682006667397)
  ·
    refine ⟨4603674032660190376250137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24552928174187682006667397 4603674032660190376250137)
    ·
      refine ⟨3452755524495142782187603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4603674032660190376250137 3452755524495142782187603)
      ·
        refine ⟨5179133286742714173281405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3452755524495142782187603 5179133286742714173281405)
        ·
          refine ⟨1942174982528517814980527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5179133286742714173281405 1942174982528517814980527)
          ·
            refine ⟨2913262473792776722470791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1942174982528517814980527 2913262473792776722470791)
            ·
              refine ⟨4369893710689165083706187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2913262473792776722470791 4369893710689165083706187)
              ·
                refine ⟨6554840566033747625559281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4369893710689165083706187 6554840566033747625559281)
                ·
                  refine ⟨4916130424525310719169461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6554840566033747625559281 4916130424525310719169461)
                  ·
                    refine ⟨460887227299247879922137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4916130424525310719169461 460887227299247879922137)
                    ·
                      refine ⟨345665420474435909941603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 460887227299247879922137 345665420474435909941603)
                      ·
                        rfl

theorem cell23_673181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_673181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673181 prefixEnd_673181 := by exact prefixLift 673181
  have htrace : WordTrace (prefixWord ++ tailWord_673181) baseStart_673181 baseEnd_673181 := by
    simpa [prefixWord, tailWord_673181, baseEnd_673181] using wordTrace_append hprefix tailTrace_673181
  have hstable : (prefixWord ++ tailWord_673181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673181).length < 2 ^ (prefixWord ++ tailWord_673181).sum := by decide
  have hdescent : baseEnd_673181 < baseStart_673181 := by decide
  rcases family_descends (prefixWord ++ tailWord_673181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673238 : List Nat := [5, 2, 1, 1, 1, 2, 1, 3, 3, 4]
def baseStart_673238 : Nat := 118140960795 + 673238 * 2 ^ 59
def prefixEnd_673238 : Nat := 4983230072969 + 3 ^ 40 * 673238 * 2
def baseEnd_673238 : Nat := 115231562957247395642947

theorem tailTrace_673238 : CollatzResearch.WordTrace tailWord_673238 prefixEnd_673238 115231562957247395642947 := by
  unfold tailWord_673238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1534687945936323796343273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16370004756654120494328245 1534687945936323796343273)
  ·
    refine ⟨1151015959452242847257455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1534687945936323796343273 1151015959452242847257455)
    ·
      refine ⟨1726523939178364270886183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1151015959452242847257455 1726523939178364270886183)
      ·
        refine ⟨2589785908767546406329275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1726523939178364270886183 2589785908767546406329275)
        ·
          refine ⟨3884678863151319609493913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2589785908767546406329275 3884678863151319609493913)
          ·
            refine ⟨2913509147363489707120435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3884678863151319609493913 2913509147363489707120435)
            ·
              refine ⟨4370263721045234560680653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2913509147363489707120435 4370263721045234560680653)
              ·
                refine ⟨1638848895391962960255245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4370263721045234560680653 1638848895391962960255245)
                ·
                  refine ⟨614568335771986110095717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1638848895391962960255245 614568335771986110095717)
                  ·
                    refine ⟨115231562957247395642947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 614568335771986110095717 115231562957247395642947)
                    ·
                      rfl

theorem cell23_673238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_673238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673238 prefixEnd_673238 := by exact prefixLift 673238
  have htrace : WordTrace (prefixWord ++ tailWord_673238) baseStart_673238 baseEnd_673238 := by
    simpa [prefixWord, tailWord_673238, baseEnd_673238] using wordTrace_append hprefix tailTrace_673238
  have hstable : (prefixWord ++ tailWord_673238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673238).length < 2 ^ (prefixWord ++ tailWord_673238).sum := by decide
  have hdescent : baseEnd_673238 < baseStart_673238 := by decide
  rcases family_descends (prefixWord ++ tailWord_673238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673315 : List Nat := [1, 1, 1, 4, 6, 1, 1, 2, 1, 5]
def baseStart_673315 : Nat := 118140960795 + 673315 * 2 ^ 59
def prefixEnd_673315 : Nat := 4983230072969 + 3 ^ 40 * 673315 * 2
def baseEnd_673315 : Nat := 115244742294046128555329

theorem tailTrace_673315 : CollatzResearch.WordTrace tailWord_673315 prefixEnd_673315 115244742294046128555329 := by
  unfold tailWord_673315
  simp only [CollatzResearch.WordTrace]
  refine ⟨24557815555702222892045399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16371877037134815261363599 24557815555702222892045399)
  ·
    refine ⟨36836723333553334338068099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24557815555702222892045399 36836723333553334338068099)
    ·
      refine ⟨55255085000330001507102149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36836723333553334338068099 55255085000330001507102149)
      ·
        refine ⟨10360328437561875282581653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55255085000330001507102149 10360328437561875282581653)
        ·
          refine ⟨485640395510712903871015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10360328437561875282581653 485640395510712903871015)
          ·
            refine ⟨728460593266069355806523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485640395510712903871015 728460593266069355806523)
            ·
              refine ⟨1092690889899104033709785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 728460593266069355806523 1092690889899104033709785)
              ·
                refine ⟨819518167424328025282339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1092690889899104033709785 819518167424328025282339)
                ·
                  refine ⟨1229277251136492037923509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 819518167424328025282339 1229277251136492037923509)
                  ·
                    refine ⟨115244742294046128555329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1229277251136492037923509 115244742294046128555329)
                    ·
                      rfl

theorem cell23_673315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 1, 5].length) (baseStart_673315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673315 prefixEnd_673315 := by exact prefixLift 673315
  have htrace : WordTrace (prefixWord ++ tailWord_673315) baseStart_673315 baseEnd_673315 := by
    simpa [prefixWord, tailWord_673315, baseEnd_673315] using wordTrace_append hprefix tailTrace_673315
  have hstable : (prefixWord ++ tailWord_673315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673315).length < 2 ^ (prefixWord ++ tailWord_673315).sum := by decide
  have hdescent : baseEnd_673315 < baseStart_673315 := by decide
  rcases family_descends (prefixWord ++ tailWord_673315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673331 : List Nat := [1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 4]
def baseStart_673331 : Nat := 118140960795 + 673331 * 2 ^ 59
def prefixEnd_673331 : Nat := 4983230072969 + 3 ^ 40 * 673331 * 2
def baseEnd_673331 : Nat := 345742442572610323065913

theorem tailTrace_673331 : CollatzResearch.WordTrace tailWord_673331 prefixEnd_673331 345742442572610323065913 := by
  unfold tailWord_673331
  simp only [CollatzResearch.WordTrace]
  refine ⟨24558399123644257624627847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16372266082429505083085231 24558399123644257624627847)
  ·
    refine ⟨36837598685466386436941771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24558399123644257624627847 36837598685466386436941771)
    ·
      refine ⟨55256398028199579655412657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36837598685466386436941771 55256398028199579655412657)
      ·
        refine ⟨41442298521149684741559493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55256398028199579655412657 41442298521149684741559493)
        ·
          refine ⟨7770430972715565889042405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41442298521149684741559493 7770430972715565889042405)
          ·
            refine ⟨1456955807384168604195451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7770430972715565889042405 1456955807384168604195451)
            ·
              refine ⟨2185433711076252906293177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1456955807384168604195451 2185433711076252906293177)
              ·
                refine ⟨1639075283307189679719883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2185433711076252906293177 1639075283307189679719883)
                ·
                  refine ⟨2458612924960784519579825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1639075283307189679719883 2458612924960784519579825)
                  ·
                    refine ⟨1843959693720588389684869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2458612924960784519579825 1843959693720588389684869)
                    ·
                      refine ⟨345742442572610323065913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1843959693720588389684869 345742442572610323065913)
                      ·
                        rfl

theorem cell23_673331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 4].length) (baseStart_673331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673331 prefixEnd_673331 := by exact prefixLift 673331
  have htrace : WordTrace (prefixWord ++ tailWord_673331) baseStart_673331 baseEnd_673331 := by
    simpa [prefixWord, tailWord_673331, baseEnd_673331] using wordTrace_append hprefix tailTrace_673331
  have hstable : (prefixWord ++ tailWord_673331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673331).length < 2 ^ (prefixWord ++ tailWord_673331).sum := by decide
  have hdescent : baseEnd_673331 < baseStart_673331 := by decide
  rcases family_descends (prefixWord ++ tailWord_673331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673341 : List Nat := [1, 4, 1, 3, 4, 10]
def baseStart_673341 : Nat := 118140960795 + 673341 * 2 ^ 59
def prefixEnd_673341 : Nat := 4983230072969 + 3 ^ 40 * 673341 * 2
def baseEnd_673341 : Nat := 1422829536539733678769

theorem tailTrace_673341 : CollatzResearch.WordTrace tailWord_673341 prefixEnd_673341 1422829536539733678769 := by
  unfold tailWord_673341
  simp only [CollatzResearch.WordTrace]
  refine ⟨24558763853608029332491877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16372509235738686221661251 24558763853608029332491877)
  ·
    refine ⟨4604768222551505499842227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24558763853608029332491877 4604768222551505499842227)
    ·
      refine ⟨6907152333827258249763341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4604768222551505499842227 6907152333827258249763341)
      ·
        refine ⟨2590182125185221843661253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6907152333827258249763341 2590182125185221843661253)
        ·
          refine ⟨485659148472229095686485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2590182125185221843661253 485659148472229095686485)
          ·
            refine ⟨1422829536539733678769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 485659148472229095686485 1422829536539733678769)
            ·
              rfl

theorem cell23_673341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 10].length) (baseStart_673341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673341 prefixEnd_673341 := by exact prefixLift 673341
  have htrace : WordTrace (prefixWord ++ tailWord_673341) baseStart_673341 baseEnd_673341 := by
    simpa [prefixWord, tailWord_673341, baseEnd_673341] using wordTrace_append hprefix tailTrace_673341
  have hstable : (prefixWord ++ tailWord_673341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673341).length < 2 ^ (prefixWord ++ tailWord_673341).sum := by decide
  have hdescent : baseEnd_673341 < baseStart_673341 := by decide
  rcases family_descends (prefixWord ++ tailWord_673341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673354 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 1, 9]
def baseStart_673354 : Nat := 118140960795 + 673354 * 2 ^ 59
def prefixEnd_673354 : Nat := 4983230072969 + 3 ^ 40 * 673354 * 2
def baseEnd_673354 : Nat := 115251417542554577692769

theorem tailTrace_673354 : CollatzResearch.WordTrace tailWord_673354 prefixEnd_673354 115251417542554577692769 := by
  unfold tailWord_673354
  simp only [CollatzResearch.WordTrace]
  refine ⟨6139809500640233138178779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16372825335040621701810077 6139809500640233138178779)
  ·
    refine ⟨9209714250960349707268169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6139809500640233138178779 9209714250960349707268169)
    ·
      refine ⟨6907285688220262280451127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9209714250960349707268169 6907285688220262280451127)
      ·
        refine ⟨10360928532330393420676691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6907285688220262280451127 10360928532330393420676691)
        ·
          refine ⟨15541392798495590131015037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10360928532330393420676691 15541392798495590131015037)
          ·
            refine ⟨5828022299435846299130639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15541392798495590131015037 5828022299435846299130639)
            ·
              refine ⟨8742033449153769448695959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5828022299435846299130639 8742033449153769448695959)
              ·
                refine ⟨13113050173730654173043939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8742033449153769448695959 13113050173730654173043939)
                ·
                  refine ⟨19669575260595981259565909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13113050173730654173043939 19669575260595981259565909)
                  ·
                    refine ⟨115251417542554577692769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 19669575260595981259565909 115251417542554577692769)
                    ·
                      rfl

theorem cell23_673354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_673354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673354 prefixEnd_673354 := by exact prefixLift 673354
  have htrace : WordTrace (prefixWord ++ tailWord_673354) baseStart_673354 baseEnd_673354 := by
    simpa [prefixWord, tailWord_673354, baseEnd_673354] using wordTrace_append hprefix tailTrace_673354
  have hstable : (prefixWord ++ tailWord_673354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673354).length < 2 ^ (prefixWord ++ tailWord_673354).sum := by decide
  have hdescent : baseEnd_673354 < baseStart_673354 := by decide
  rcases family_descends (prefixWord ++ tailWord_673354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673389 : List Nat := [1, 5, 1, 1, 5, 1, 2, 1, 1, 2, 3]
def baseStart_673389 : Nat := 118140960795 + 673389 * 2 ^ 59
def prefixEnd_673389 : Nat := 4983230072969 + 3 ^ 40 * 673389 * 2
def baseEnd_673389 : Nat := 345772224450571096140647

theorem tailTrace_673389 : CollatzResearch.WordTrace tailWord_673389 prefixEnd_673389 345772224450571096140647 := by
  unfold tailWord_673389
  simp only [CollatzResearch.WordTrace]
  refine ⟨24560514557434133530239221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16373676371622755686826147 24560514557434133530239221)
  ·
    refine ⟨2302548239759450018459927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24560514557434133530239221 2302548239759450018459927)
    ·
      refine ⟨3453822359639175027689891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2302548239759450018459927 3453822359639175027689891)
      ·
        refine ⟨5180733539458762541534837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3453822359639175027689891 5180733539458762541534837)
        ·
          refine ⟨485693769324258988268891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5180733539458762541534837 485693769324258988268891)
          ·
            refine ⟨728540653986388482403337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485693769324258988268891 728540653986388482403337)
            ·
              refine ⟨546405490489791361802503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 728540653986388482403337 546405490489791361802503)
              ·
                refine ⟨819608235734687042703755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 546405490489791361802503 819608235734687042703755)
                ·
                  refine ⟨1229412353602030564055633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 819608235734687042703755 1229412353602030564055633)
                  ·
                    refine ⟨922059265201522923041725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1229412353602030564055633 922059265201522923041725)
                    ·
                      refine ⟨345772224450571096140647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 922059265201522923041725 345772224450571096140647)
                      ·
                        rfl

theorem cell23_673389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_673389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673389 prefixEnd_673389 := by exact prefixLift 673389
  have htrace : WordTrace (prefixWord ++ tailWord_673389) baseStart_673389 baseEnd_673389 := by
    simpa [prefixWord, tailWord_673389, baseEnd_673389] using wordTrace_append hprefix tailTrace_673389
  have hstable : (prefixWord ++ tailWord_673389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673389).length < 2 ^ (prefixWord ++ tailWord_673389).sum := by decide
  have hdescent : baseEnd_673389 < baseStart_673389 := by decide
  rcases family_descends (prefixWord ++ tailWord_673389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673424 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 9]
def baseStart_673424 : Nat := 118140960795 + 673424 * 2 ^ 59
def prefixEnd_673424 : Nat := 4983230072969 + 3 ^ 40 * 673424 * 2
def baseEnd_673424 : Nat := 345790196273478459202985

theorem tailTrace_673424 : CollatzResearch.WordTrace tailWord_673424 prefixEnd_673424 345790196273478459202985 := by
  unfold tailWord_673424
  simp only [CollatzResearch.WordTrace]
  refine ⟨12280895556153667253881663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16374527408204889671842217 12280895556153667253881663)
  ·
    refine ⟨18421343334230500880822495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12280895556153667253881663 18421343334230500880822495)
    ·
      refine ⟨27632015001345751321233743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18421343334230500880822495 27632015001345751321233743)
      ·
        refine ⟨41448022502018626981850615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27632015001345751321233743 41448022502018626981850615)
        ·
          refine ⟨62172033753027940472775923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41448022502018626981850615 62172033753027940472775923)
          ·
            refine ⟨93258050629541910709163885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62172033753027940472775923 93258050629541910709163885)
            ·
              refine ⟨34971768986078216515936457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93258050629541910709163885 34971768986078216515936457)
              ·
                refine ⟨26228826739558662386952343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34971768986078216515936457 26228826739558662386952343)
                ·
                  refine ⟨39343240109337993580428515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26228826739558662386952343 39343240109337993580428515)
                  ·
                    refine ⟨59014860164006990370642773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39343240109337993580428515 59014860164006990370642773)
                    ·
                      refine ⟨345790196273478459202985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 59014860164006990370642773 345790196273478459202985)
                      ·
                        rfl

theorem cell23_673424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 9].length) (baseStart_673424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673424 prefixEnd_673424 := by exact prefixLift 673424
  have htrace : WordTrace (prefixWord ++ tailWord_673424) baseStart_673424 baseEnd_673424 := by
    simpa [prefixWord, tailWord_673424, baseEnd_673424] using wordTrace_append hprefix tailTrace_673424
  have hstable : (prefixWord ++ tailWord_673424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673424).length < 2 ^ (prefixWord ++ tailWord_673424).sum := by decide
  have hdescent : baseEnd_673424 < baseStart_673424 := by decide
  rcases family_descends (prefixWord ++ tailWord_673424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673431 : List Nat := [1, 1, 3, 3, 2, 2, 2, 2, 7]
def baseStart_673431 : Nat := 118140960795 + 673431 * 2 ^ 59
def prefixEnd_673431 : Nat := 4983230072969 + 3 ^ 40 * 673431 * 2
def baseEnd_673431 : Nat := 38421532293117770201717

theorem tailTrace_673431 : CollatzResearch.WordTrace tailWord_673431 prefixEnd_673431 38421532293117770201717 := by
  unfold tailWord_673431
  simp only [CollatzResearch.WordTrace]
  refine ⟨24562046423281974703268147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16374697615521316468845431 24562046423281974703268147)
  ·
    refine ⟨36843069634922962054902221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24562046423281974703268147 36843069634922962054902221)
    ·
      refine ⟨13816151113096110770588333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36843069634922962054902221 13816151113096110770588333)
      ·
        refine ⟨5181056667411041538970625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13816151113096110770588333 5181056667411041538970625)
        ·
          refine ⟨3885792500558281154227969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5181056667411041538970625 3885792500558281154227969)
          ·
            refine ⟨2914344375418710865670977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3885792500558281154227969 2914344375418710865670977)
            ·
              refine ⟨2185758281564033149253233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2914344375418710865670977 2185758281564033149253233)
              ·
                refine ⟨1639318711173024861939925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2185758281564033149253233 1639318711173024861939925)
                ·
                  refine ⟨38421532293117770201717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1639318711173024861939925 38421532293117770201717)
                  ·
                    rfl

theorem cell23_673431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 7].length) (baseStart_673431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673431 prefixEnd_673431 := by exact prefixLift 673431
  have htrace : WordTrace (prefixWord ++ tailWord_673431) baseStart_673431 baseEnd_673431 := by
    simpa [prefixWord, tailWord_673431, baseEnd_673431] using wordTrace_append hprefix tailTrace_673431
  have hstable : (prefixWord ++ tailWord_673431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673431).length < 2 ^ (prefixWord ++ tailWord_673431).sum := by decide
  have hdescent : baseEnd_673431 < baseStart_673431 := by decide
  rcases family_descends (prefixWord ++ tailWord_673431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673471 : List Nat := [1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 5]
def baseStart_673471 : Nat := 118140960795 + 673471 * 2 ^ 59
def prefixEnd_673471 : Nat := 4983230072969 + 3 ^ 40 * 673471 * 2
def baseEnd_673471 : Nat := 345814329864239775315269

theorem tailTrace_673471 : CollatzResearch.WordTrace tailWord_673471 prefixEnd_673471 345814329864239775315269 := by
  unfold tailWord_673471
  simp only [CollatzResearch.WordTrace]
  refine ⟨24563505343137061534724267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16375670228758041023149511 24563505343137061534724267)
  ·
    refine ⟨36845258014705592302086401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24563505343137061534724267 36845258014705592302086401)
    ·
      refine ⟨27633943511029194226564801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36845258014705592302086401 27633943511029194226564801)
      ·
        refine ⟨20725457633271895669923601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27633943511029194226564801 20725457633271895669923601)
        ·
          refine ⟨15544093224953921752442701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20725457633271895669923601 15544093224953921752442701)
          ·
            refine ⟨5829034959357720657166013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15544093224953921752442701 5829034959357720657166013)
            ·
              refine ⟨2185888109759145246437255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5829034959357720657166013 2185888109759145246437255)
              ·
                refine ⟨3278832164638717869655883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2185888109759145246437255 3278832164638717869655883)
                ·
                  refine ⟨4918248246958076804483825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3278832164638717869655883 4918248246958076804483825)
                  ·
                    refine ⟨3688686185218557603362869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4918248246958076804483825 3688686185218557603362869)
                    ·
                      refine ⟨345814329864239775315269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3688686185218557603362869 345814329864239775315269)
                      ·
                        rfl

theorem cell23_673471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_673471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673471 prefixEnd_673471 := by exact prefixLift 673471
  have htrace : WordTrace (prefixWord ++ tailWord_673471) baseStart_673471 baseEnd_673471 := by
    simpa [prefixWord, tailWord_673471, baseEnd_673471] using wordTrace_append hprefix tailTrace_673471
  have hstable : (prefixWord ++ tailWord_673471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673471).length < 2 ^ (prefixWord ++ tailWord_673471).sum := by decide
  have hdescent : baseEnd_673471 < baseStart_673471 := by decide
  rcases family_descends (prefixWord ++ tailWord_673471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673498 : List Nat := [3, 1, 1, 2, 2, 3, 1, 3, 2, 1, 4]
def baseStart_673498 : Nat := 118140960795 + 673498 * 2 ^ 59
def prefixEnd_673498 : Nat := 4983230072969 + 3 ^ 40 * 673498 * 2
def baseEnd_673498 : Nat := 345828193841911169677645

theorem tailTrace_673498 : CollatzResearch.WordTrace tailWord_673498 prefixEnd_673498 345828193841911169677645 := by
  unfold tailWord_673498
  simp only [CollatzResearch.WordTrace]
  refine ⟨6141122528509811286489287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16376326742692830097304765 6141122528509811286489287)
  ·
    refine ⟨9211683792764716929733931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6141122528509811286489287 9211683792764716929733931)
    ·
      refine ⟨13817525689147075394600897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9211683792764716929733931 13817525689147075394600897)
      ·
        refine ⟨10363144266860306545950673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13817525689147075394600897 10363144266860306545950673)
        ·
          refine ⟨7772358200145229909463005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10363144266860306545950673 7772358200145229909463005)
          ·
            refine ⟨2914634325054461216048627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7772358200145229909463005 2914634325054461216048627)
            ·
              refine ⟨4371951487581691824072941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2914634325054461216048627 4371951487581691824072941)
              ·
                refine ⟨1639481807843134434027353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4371951487581691824072941 1639481807843134434027353)
                ·
                  refine ⟨1229611355882350825520515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1639481807843134434027353 1229611355882350825520515)
                  ·
                    refine ⟨1844417033823526238280773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1229611355882350825520515 1844417033823526238280773)
                    ·
                      refine ⟨345828193841911169677645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1844417033823526238280773 345828193841911169677645)
                      ·
                        rfl

theorem cell23_673498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_673498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673498 prefixEnd_673498 := by exact prefixLift 673498
  have htrace : WordTrace (prefixWord ++ tailWord_673498) baseStart_673498 baseEnd_673498 := by
    simpa [prefixWord, tailWord_673498, baseEnd_673498] using wordTrace_append hprefix tailTrace_673498
  have hstable : (prefixWord ++ tailWord_673498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673498).length < 2 ^ (prefixWord ++ tailWord_673498).sum := by decide
  have hdescent : baseEnd_673498 < baseStart_673498 := by decide
  rcases family_descends (prefixWord ++ tailWord_673498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673605 : List Nat := [1, 3, 1, 1, 1, 2, 6, 2, 1, 1, 4]
def baseStart_673605 : Nat := 118140960795 + 673605 * 2 ^ 59
def prefixEnd_673605 : Nat := 4983230072969 + 3 ^ 40 * 673605 * 2
def baseEnd_673605 : Nat := 345883136271942251039653

theorem tailTrace_673605 : CollatzResearch.WordTrace tailWord_673605 prefixEnd_673605 345883136271942251039653 := by
  unfold tailWord_673605
  simp only [CollatzResearch.WordTrace]
  refine ⟨24568392724651602420102269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16378928483101068280068179 24568392724651602420102269)
  ·
    refine ⟨9213147271744350907538351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24568392724651602420102269 9213147271744350907538351)
    ·
      refine ⟨13819720907616526361307527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9213147271744350907538351 13819720907616526361307527)
      ·
        refine ⟨20729581361424789541961291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13819720907616526361307527 20729581361424789541961291)
        ·
          refine ⟨31094372042137184312941937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20729581361424789541961291 31094372042137184312941937)
          ·
            refine ⟨23320779031602888234706453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31094372042137184312941937 23320779031602888234706453)
            ·
              refine ⟨1093161517106385386001865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23320779031602888234706453 1093161517106385386001865)
              ·
                refine ⟨819871137829789039501399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1093161517106385386001865 819871137829789039501399)
                ·
                  refine ⟨1229806706744683559252099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 819871137829789039501399 1229806706744683559252099)
                  ·
                    refine ⟨1844710060117025338878149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1229806706744683559252099 1844710060117025338878149)
                    ·
                      refine ⟨345883136271942251039653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1844710060117025338878149 345883136271942251039653)
                      ·
                        rfl

theorem cell23_673605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 1, 4].length) (baseStart_673605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673605 prefixEnd_673605 := by exact prefixLift 673605
  have htrace : WordTrace (prefixWord ++ tailWord_673605) baseStart_673605 baseEnd_673605 := by
    simpa [prefixWord, tailWord_673605, baseEnd_673605] using wordTrace_append hprefix tailTrace_673605
  have hstable : (prefixWord ++ tailWord_673605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673605).length < 2 ^ (prefixWord ++ tailWord_673605).sum := by decide
  have hdescent : baseEnd_673605 < baseStart_673605 := by decide
  rcases family_descends (prefixWord ++ tailWord_673605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673625 : List Nat := [1, 2, 1, 2, 2, 3, 1, 5, 1, 2, 3]
def baseStart_673625 : Nat := 118140960795 + 673625 * 2 ^ 59
def prefixEnd_673625 : Nat := 4983230072969 + 3 ^ 40 * 673625 * 2
def baseEnd_673625 : Nat := 345893405885032172789561

theorem tailTrace_673625 : CollatzResearch.WordTrace tailWord_673625 prefixEnd_673625 345893405885032172789561 := by
  unfold tailWord_673625
  simp only [CollatzResearch.WordTrace]
  refine ⟨24569122184579145835830329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16379414789719430557220219 24569122184579145835830329)
  ·
    refine ⟨18426841638434359376872747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24569122184579145835830329 18426841638434359376872747)
    ·
      refine ⟨27640262457651539065309121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18426841638434359376872747 27640262457651539065309121)
      ·
        refine ⟨20730196843238654298981841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27640262457651539065309121 20730196843238654298981841)
        ·
          refine ⟨15547647632428990724236381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20730196843238654298981841 15547647632428990724236381)
          ·
            refine ⟨5830367862160871521588643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15547647632428990724236381 5830367862160871521588643)
            ·
              refine ⟨8745551793241307282382965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5830367862160871521588643 8745551793241307282382965)
              ·
                refine ⟨819895480616372557723403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8745551793241307282382965 819895480616372557723403)
                ·
                  refine ⟨1229843220924558836585105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 819895480616372557723403 1229843220924558836585105)
                  ·
                    refine ⟨922382415693419127438829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1229843220924558836585105 922382415693419127438829)
                    ·
                      refine ⟨345893405885032172789561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 922382415693419127438829 345893405885032172789561)
                      ·
                        rfl

theorem cell23_673625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 2, 3].length) (baseStart_673625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673625 prefixEnd_673625 := by exact prefixLift 673625
  have htrace : WordTrace (prefixWord ++ tailWord_673625) baseStart_673625 baseEnd_673625 := by
    simpa [prefixWord, tailWord_673625, baseEnd_673625] using wordTrace_append hprefix tailTrace_673625
  have hstable : (prefixWord ++ tailWord_673625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673625).length < 2 ^ (prefixWord ++ tailWord_673625).sum := by decide
  have hdescent : baseEnd_673625 < baseStart_673625 := by decide
  rcases family_descends (prefixWord ++ tailWord_673625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673668 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 1, 4, 5]
def baseStart_673668 : Nat := 118140960795 + 673668 * 2 ^ 59
def prefixEnd_673668 : Nat := 4983230072969 + 3 ^ 40 * 673668 * 2
def baseEnd_673668 : Nat := 345915485553175504551863

theorem tailTrace_673668 : CollatzResearch.WordTrace tailWord_673668 prefixEnd_673668 345915485553175504551863 := by
  unfold tailWord_673668
  simp only [CollatzResearch.WordTrace]
  refine ⟨12285345261711682089822829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16380460348948909453097105 12285345261711682089822829)
  ·
    refine ⟨4607004473141880783683561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12285345261711682089822829 4607004473141880783683561)
    ·
      refine ⟨3455253354856410587762671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4607004473141880783683561 3455253354856410587762671)
      ·
        refine ⟨5182880032284615881644007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3455253354856410587762671 5182880032284615881644007)
        ·
          refine ⟨7774320048426923822466011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5182880032284615881644007 7774320048426923822466011)
          ·
            refine ⟨11661480072640385733699017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7774320048426923822466011 11661480072640385733699017)
            ·
              refine ⟨8746110054480289300274263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11661480072640385733699017 8746110054480289300274263)
              ·
                refine ⟨13119165081720433950411395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8746110054480289300274263 13119165081720433950411395)
                ·
                  refine ⟨19678747622580650925617093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13119165081720433950411395 19678747622580650925617093)
                  ·
                    refine ⟨3689765179233872048553205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19678747622580650925617093 3689765179233872048553205)
                    ·
                      refine ⟨345915485553175504551863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3689765179233872048553205 345915485553175504551863)
                      ·
                        rfl

theorem cell23_673668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_673668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673668 prefixEnd_673668 := by exact prefixLift 673668
  have htrace : WordTrace (prefixWord ++ tailWord_673668) baseStart_673668 baseEnd_673668 := by
    simpa [prefixWord, tailWord_673668, baseEnd_673668] using wordTrace_append hprefix tailTrace_673668
  have hstable : (prefixWord ++ tailWord_673668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673668).length < 2 ^ (prefixWord ++ tailWord_673668).sum := by decide
  have hdescent : baseEnd_673668 < baseStart_673668 := by decide
  rcases family_descends (prefixWord ++ tailWord_673668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673672 : List Nat := [2, 1, 3, 3, 3, 1, 1, 2, 1, 3, 3]
def baseStart_673672 : Nat := 118140960795 + 673672 * 2 ^ 59
def prefixEnd_673672 : Nat := 4983230072969 + 3 ^ 40 * 673672 * 2
def baseEnd_673672 : Nat := 345917539475793488901845

theorem tailTrace_673672 : CollatzResearch.WordTrace tailWord_673672 prefixEnd_673672 345917539475793488901845 := by
  unfold tailWord_673672
  simp only [CollatzResearch.WordTrace]
  refine ⟨12285418207704436431395635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16380557610272581908527513 12285418207704436431395635)
  ·
    refine ⟨18428127311556654647093453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12285418207704436431395635 18428127311556654647093453)
    ·
      refine ⟨6910547741833745492660045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18428127311556654647093453 6910547741833745492660045)
      ·
        refine ⟨2591455403187654559747517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6910547741833745492660045 2591455403187654559747517)
        ·
          refine ⟨971795776195370459905319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2591455403187654559747517 971795776195370459905319)
          ·
            refine ⟨1457693664293055689857979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 971795776195370459905319 1457693664293055689857979)
            ·
              refine ⟨2186540496439583534786969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1457693664293055689857979 2186540496439583534786969)
              ·
                refine ⟨1639905372329687651090227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2186540496439583534786969 1639905372329687651090227)
                ·
                  refine ⟨2459858058494531476635341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1639905372329687651090227 2459858058494531476635341)
                  ·
                    refine ⟨922446771935449303738253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2459858058494531476635341 922446771935449303738253)
                    ·
                      refine ⟨345917539475793488901845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 922446771935449303738253 345917539475793488901845)
                      ·
                        rfl

theorem cell23_673672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_673672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673672 prefixEnd_673672 := by exact prefixLift 673672
  have htrace : WordTrace (prefixWord ++ tailWord_673672) baseStart_673672 baseEnd_673672 := by
    simpa [prefixWord, tailWord_673672, baseEnd_673672] using wordTrace_append hprefix tailTrace_673672
  have hstable : (prefixWord ++ tailWord_673672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673672).length < 2 ^ (prefixWord ++ tailWord_673672).sum := by decide
  have hdescent : baseEnd_673672 < baseStart_673672 := by decide
  rcases family_descends (prefixWord ++ tailWord_673672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673746 : List Nat := [3, 2, 2, 3, 2, 1, 1, 1, 4, 2, 2]
def baseStart_673746 : Nat := 118140960795 + 673746 * 2 ^ 59
def prefixEnd_673746 : Nat := 4983230072969 + 3 ^ 40 * 673746 * 2
def baseEnd_673746 : Nat := 345955537044226199376505

theorem tailTrace_673746 : CollatzResearch.WordTrace tailWord_673746 prefixEnd_673746 345955537044226199376505 := by
  unfold tailWord_673746
  simp only [CollatzResearch.WordTrace]
  refine ⟨6143383854285195875246273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16382356944760522333990061 6143383854285195875246273)
  ·
    refine ⟨4607537890713896906434705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6143383854285195875246273 4607537890713896906434705)
    ·
      refine ⟨3455653418035422679826029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4607537890713896906434705 3455653418035422679826029)
      ·
        refine ⟨1295870031763283504934761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3455653418035422679826029 1295870031763283504934761)
        ·
          refine ⟨971902523822462628701071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1295870031763283504934761 971902523822462628701071)
          ·
            refine ⟨1457853785733693943051607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 971902523822462628701071 1457853785733693943051607)
            ·
              refine ⟨2186780678600540914577411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1457853785733693943051607 2186780678600540914577411)
              ·
                refine ⟨3280171017900811371866117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2186780678600540914577411 3280171017900811371866117)
                ·
                  refine ⟨615032065856402132224897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3280171017900811371866117 615032065856402132224897)
                  ·
                    refine ⟨461274049392301599168673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 615032065856402132224897 461274049392301599168673)
                    ·
                      refine ⟨345955537044226199376505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 461274049392301599168673 345955537044226199376505)
                      ·
                        rfl

theorem cell23_673746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_673746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673746 prefixEnd_673746 := by exact prefixLift 673746
  have htrace : WordTrace (prefixWord ++ tailWord_673746) baseStart_673746 baseEnd_673746 := by
    simpa [prefixWord, tailWord_673746, baseEnd_673746] using wordTrace_append hprefix tailTrace_673746
  have hstable : (prefixWord ++ tailWord_673746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673746).length < 2 ^ (prefixWord ++ tailWord_673746).sum := by decide
  have hdescent : baseEnd_673746 < baseStart_673746 := by decide
  rcases family_descends (prefixWord ++ tailWord_673746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673785 : List Nat := [1, 2, 1, 3, 1, 4, 2, 1, 1, 3, 4]
def baseStart_673785 : Nat := 118140960795 + 673785 * 2 ^ 59
def prefixEnd_673785 : Nat := 4983230072969 + 3 ^ 40 * 673785 * 2
def baseEnd_673785 : Nat := 345975562789751546788825

theorem tailTrace_673785 : CollatzResearch.WordTrace tailWord_673785 prefixEnd_673785 345975562789751546788825 := by
  unfold tailWord_673785
  simp only [CollatzResearch.WordTrace]
  refine ⟨24574957863999493161654809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16383305242666328774436539 24574957863999493161654809)
  ·
    refine ⟨18431218397999619871241107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24574957863999493161654809 18431218397999619871241107)
    ·
      refine ⟨27646827596999429806861661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18431218397999619871241107 27646827596999429806861661)
      ·
        refine ⟨10367560348874786177573123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27646827596999429806861661 10367560348874786177573123)
        ·
          refine ⟨15551340523312179266359685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10367560348874786177573123 15551340523312179266359685)
          ·
            refine ⟨2915876348121033612442441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15551340523312179266359685 2915876348121033612442441)
            ·
              refine ⟨2186907261090775209331831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2915876348121033612442441 2186907261090775209331831)
              ·
                refine ⟨3280360891636162813997747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2186907261090775209331831 3280360891636162813997747)
                ·
                  refine ⟨4920541337454244220996621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3280360891636162813997747 4920541337454244220996621)
                  ·
                    refine ⟨1845203001545341582873733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4920541337454244220996621 1845203001545341582873733)
                    ·
                      refine ⟨345975562789751546788825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1845203001545341582873733 345975562789751546788825)
                      ·
                        rfl

theorem cell23_673785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_673785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673785 prefixEnd_673785 := by exact prefixLift 673785
  have htrace : WordTrace (prefixWord ++ tailWord_673785) baseStart_673785 baseEnd_673785 := by
    simpa [prefixWord, tailWord_673785, baseEnd_673785] using wordTrace_append hprefix tailTrace_673785
  have hstable : (prefixWord ++ tailWord_673785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673785).length < 2 ^ (prefixWord ++ tailWord_673785).sum := by decide
  have hdescent : baseEnd_673785 < baseStart_673785 := by decide
  rcases family_descends (prefixWord ++ tailWord_673785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673795 : List Nat := [1, 1, 1, 3, 2, 1, 1, 4, 5, 4]
def baseStart_673795 : Nat := 118140960795 + 673795 * 2 ^ 59
def prefixEnd_673795 : Nat := 4983230072969 + 3 ^ 40 * 673795 * 2
def baseEnd_673795 : Nat := 115326899198765502554593

theorem tailTrace_673795 : CollatzResearch.WordTrace tailWord_673795 prefixEnd_673795 115326899198765502554593 := by
  unfold tailWord_673795
  simp only [CollatzResearch.WordTrace]
  refine ⟨24575322593963264869518839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16383548395975509913012559 24575322593963264869518839)
  ·
    refine ⟨36862983890944897304278259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24575322593963264869518839 36862983890944897304278259)
    ·
      refine ⟨55294475836417345956417389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36862983890944897304278259 55294475836417345956417389)
      ·
        refine ⟨20735428438656504733656521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55294475836417345956417389 20735428438656504733656521)
        ·
          refine ⟨15551571328992378550242391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20735428438656504733656521 15551571328992378550242391)
          ·
            refine ⟨23327356993488567825363587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15551571328992378550242391 23327356993488567825363587)
            ·
              refine ⟨34991035490232851738045381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23327356993488567825363587 34991035490232851738045381)
              ·
                refine ⟨6560819154418659700883509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34991035490232851738045381 6560819154418659700883509)
                ·
                  refine ⟨615076795726749346957829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6560819154418659700883509 615076795726749346957829)
                  ·
                    refine ⟨115326899198765502554593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 615076795726749346957829 115326899198765502554593)
                    ·
                      rfl

theorem cell23_673795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 5, 4].length) (baseStart_673795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673795 prefixEnd_673795 := by exact prefixLift 673795
  have htrace : WordTrace (prefixWord ++ tailWord_673795) baseStart_673795 baseEnd_673795 := by
    simpa [prefixWord, tailWord_673795, baseEnd_673795] using wordTrace_append hprefix tailTrace_673795
  have hstable : (prefixWord ++ tailWord_673795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673795).length < 2 ^ (prefixWord ++ tailWord_673795).sum := by decide
  have hdescent : baseEnd_673795 < baseStart_673795 := by decide
  rcases family_descends (prefixWord ++ tailWord_673795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673846 : List Nat := [5, 1, 2, 1, 1, 1, 2, 5, 1, 4]
def baseStart_673846 : Nat := 118140960795 + 673846 * 2 ^ 59
def prefixEnd_673846 : Nat := 4983230072969 + 3 ^ 40 * 673846 * 2
def baseEnd_673846 : Nat := 115335628369891936042015

theorem tailTrace_673846 : CollatzResearch.WordTrace tailWord_673846 prefixEnd_673846 115335628369891936042015 := by
  unfold tailWord_673846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1536073919798656286226587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16384788477852333719750261 1536073919798656286226587)
  ·
    refine ⟨2304110879697984429339881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1536073919798656286226587 2304110879697984429339881)
    ·
      refine ⟨1728083159773488322004911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2304110879697984429339881 1728083159773488322004911)
      ·
        refine ⟨2592124739660232483007367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1728083159773488322004911 2592124739660232483007367)
        ·
          refine ⟨3888187109490348724511051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2592124739660232483007367 3888187109490348724511051)
          ·
            refine ⟨5832280664235523086766577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3888187109490348724511051 5832280664235523086766577)
            ·
              refine ⟨4374210498176642315074933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5832280664235523086766577 4374210498176642315074933)
              ·
                refine ⟨410082234204060217038275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4374210498176642315074933 410082234204060217038275)
                ·
                  refine ⟨615123351306090325557413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 410082234204060217038275 615123351306090325557413)
                  ·
                    refine ⟨115335628369891936042015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 615123351306090325557413 115335628369891936042015)
                    ·
                      rfl

theorem cell23_673846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_673846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673846 prefixEnd_673846 := by exact prefixLift 673846
  have htrace : WordTrace (prefixWord ++ tailWord_673846) baseStart_673846 baseEnd_673846 := by
    simpa [prefixWord, tailWord_673846, baseEnd_673846] using wordTrace_append hprefix tailTrace_673846
  have hstable : (prefixWord ++ tailWord_673846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673846).length < 2 ^ (prefixWord ++ tailWord_673846).sum := by decide
  have hdescent : baseEnd_673846 < baseStart_673846 := by decide
  rcases family_descends (prefixWord ++ tailWord_673846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673892 : List Nat := [2, 3, 1, 1, 2, 1, 4, 1, 3, 1, 4]
def baseStart_673892 : Nat := 118140960795 + 673892 * 2 ^ 59
def prefixEnd_673892 : Nat := 4983230072969 + 3 ^ 40 * 673892 * 2
def baseEnd_673892 : Nat := 346030505219782628150833

theorem tailTrace_673892 : CollatzResearch.WordTrace tailWord_673892 prefixEnd_673892 346030505219782628150833 := by
  unfold tailWord_673892
  simp only [CollatzResearch.WordTrace]
  refine ⟨12289430237305925217899965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16385906983074566957199953 12289430237305925217899965)
  ·
    refine ⟨4608536338989721956712487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12289430237305925217899965 4608536338989721956712487)
    ·
      refine ⟨6912804508484582935068731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4608536338989721956712487 6912804508484582935068731)
      ·
        refine ⟨10369206762726874402603097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6912804508484582935068731 10369206762726874402603097)
        ·
          refine ⟨7776905072045155801952323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10369206762726874402603097 7776905072045155801952323)
          ·
            refine ⟨11665357608067733702928485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7776905072045155801952323 11665357608067733702928485)
            ·
              refine ⟨2187254551512700069299091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11665357608067733702928485 2187254551512700069299091)
              ·
                refine ⟨3280881827269050103948637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2187254551512700069299091 3280881827269050103948637)
                ·
                  refine ⟨1230330685225893788980739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3280881827269050103948637 1230330685225893788980739)
                  ·
                    refine ⟨1845496027838840683471109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1230330685225893788980739 1845496027838840683471109)
                    ·
                      refine ⟨346030505219782628150833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1845496027838840683471109 346030505219782628150833)
                      ·
                        rfl

theorem cell23_673892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_673892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673892 prefixEnd_673892 := by exact prefixLift 673892
  have htrace : WordTrace (prefixWord ++ tailWord_673892) baseStart_673892 baseEnd_673892 := by
    simpa [prefixWord, tailWord_673892, baseEnd_673892] using wordTrace_append hprefix tailTrace_673892
  have hstable : (prefixWord ++ tailWord_673892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673892).length < 2 ^ (prefixWord ++ tailWord_673892).sum := by decide
  have hdescent : baseEnd_673892 < baseStart_673892 := by decide
  rcases family_descends (prefixWord ++ tailWord_673892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673902 : List Nat := [4, 1, 2, 2, 1, 1, 1, 4, 1, 6]
def baseStart_673902 : Nat := 118140960795 + 673902 * 2 ^ 59
def prefixEnd_673902 : Nat := 4983230072969 + 3 ^ 40 * 673902 * 2
def baseEnd_673902 : Nat := 115345213342109196341929

theorem tailTrace_673902 : CollatzResearch.WordTrace tailWord_673902 prefixEnd_673902 115345213342109196341929 := by
  unfold tailWord_673902
  simp only [CollatzResearch.WordTrace]
  refine ⟨3072403150571952767957995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16386150136383748095775973 3072403150571952767957995)
  ·
    refine ⟨4608604725857929151936993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3072403150571952767957995 4608604725857929151936993)
    ·
      refine ⟨3456453544393446863952745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4608604725857929151936993 3456453544393446863952745)
      ·
        refine ⟨2592340158295085147964559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3456453544393446863952745 2592340158295085147964559)
        ·
          refine ⟨3888510237442627721946839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2592340158295085147964559 3888510237442627721946839)
          ·
            refine ⟨5832765356163941582920259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3888510237442627721946839 5832765356163941582920259)
            ·
              refine ⟨8749148034245912374380389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5832765356163941582920259 8749148034245912374380389)
              ·
                refine ⟨1640465256421108570196323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8749148034245912374380389 1640465256421108570196323)
                ·
                  refine ⟨2460697884631662855294485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1640465256421108570196323 2460697884631662855294485)
                  ·
                    refine ⟨115345213342109196341929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2460697884631662855294485 115345213342109196341929)
                    ·
                      rfl

theorem cell23_673902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_673902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673902 prefixEnd_673902 := by exact prefixLift 673902
  have htrace : WordTrace (prefixWord ++ tailWord_673902) baseStart_673902 baseEnd_673902 := by
    simpa [prefixWord, tailWord_673902, baseEnd_673902] using wordTrace_append hprefix tailTrace_673902
  have hstable : (prefixWord ++ tailWord_673902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673902).length < 2 ^ (prefixWord ++ tailWord_673902).sum := by decide
  have hdescent : baseEnd_673902 < baseStart_673902 := by decide
  rcases family_descends (prefixWord ++ tailWord_673902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673906 : List Nat := [3, 2, 1, 2, 2, 4, 2, 1, 1, 5]
def baseStart_673906 : Nat := 118140960795 + 673906 * 2 ^ 59
def prefixEnd_673906 : Nat := 4983230072969 + 3 ^ 40 * 673906 * 2
def baseEnd_673906 : Nat := 115345897982981857791923

theorem tailTrace_673906 : CollatzResearch.WordTrace tailWord_673906 prefixEnd_673906 115345897982981857791923 := by
  unfold tailWord_673906
  simp only [CollatzResearch.WordTrace]
  refine ⟨6144842774140282706702393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16386247397707420551206381 6144842774140282706702393)
  ·
    refine ⟨4608632080605212030026795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6144842774140282706702393 4608632080605212030026795)
    ·
      refine ⟨6912948120907818045040193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4608632080605212030026795 6912948120907818045040193)
      ·
        refine ⟨5184711090680863533780145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6912948120907818045040193 5184711090680863533780145)
        ·
          refine ⟨3888533318010647650335109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5184711090680863533780145 3888533318010647650335109)
          ·
            refine ⟨729099997126996434437833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3888533318010647650335109 729099997126996434437833)
            ·
              refine ⟨546824997845247325828375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 729099997126996434437833 546824997845247325828375)
              ·
                refine ⟨820237496767870988742563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 546824997845247325828375 820237496767870988742563)
                ·
                  refine ⟨1230356245151806483113845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 820237496767870988742563 1230356245151806483113845)
                  ·
                    refine ⟨115345897982981857791923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1230356245151806483113845 115345897982981857791923)
                    ·
                      rfl

theorem cell23_673906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 1, 5].length) (baseStart_673906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673906 prefixEnd_673906 := by exact prefixLift 673906
  have htrace : WordTrace (prefixWord ++ tailWord_673906) baseStart_673906 baseEnd_673906 := by
    simpa [prefixWord, tailWord_673906, baseEnd_673906] using wordTrace_append hprefix tailTrace_673906
  have hstable : (prefixWord ++ tailWord_673906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673906).length < 2 ^ (prefixWord ++ tailWord_673906).sum := by decide
  have hdescent : baseEnd_673906 < baseStart_673906 := by decide
  rcases family_descends (prefixWord ++ tailWord_673906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673945 : List Nat := [1, 2, 1, 2, 1, 2, 1, 4, 2, 7]
def baseStart_673945 : Nat := 118140960795 + 673945 * 2 ^ 59
def prefixEnd_673945 : Nat := 4983230072969 + 3 ^ 40 * 673945 * 2
def baseEnd_673945 : Nat := 115352573231490306929363

theorem tailTrace_673945 : CollatzResearch.WordTrace tailWord_673945 prefixEnd_673945 115352573231490306929363 := by
  unfold tailWord_673945
  simp only [CollatzResearch.WordTrace]
  refine ⟨24580793543419840487479289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16387195695613226991652859 24580793543419840487479289)
  ·
    refine ⟨18435595157564880365609467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24580793543419840487479289 18435595157564880365609467)
    ·
      refine ⟨27653392736347320548414201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18435595157564880365609467 27653392736347320548414201)
      ·
        refine ⟨20740044552260490411310651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27653392736347320548414201 20740044552260490411310651)
        ·
          refine ⟨31110066828390735616965977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20740044552260490411310651 31110066828390735616965977)
          ·
            refine ⟨23332550121293051712724483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31110066828390735616965977 23332550121293051712724483)
            ·
              refine ⟨34998825181939577569086725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23332550121293051712724483 34998825181939577569086725)
              ·
                refine ⟨6562279721613670794203761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34998825181939577569086725 6562279721613670794203761)
                ·
                  refine ⟨4921709791210253095652821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6562279721613670794203761 4921709791210253095652821)
                  ·
                    refine ⟨115352573231490306929363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4921709791210253095652821 115352573231490306929363)
                    ·
                      rfl

theorem cell23_673945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 7].length) (baseStart_673945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673945 prefixEnd_673945 := by exact prefixLift 673945
  have htrace : WordTrace (prefixWord ++ tailWord_673945) baseStart_673945 baseEnd_673945 := by
    simpa [prefixWord, tailWord_673945, baseEnd_673945] using wordTrace_append hprefix tailTrace_673945
  have hstable : (prefixWord ++ tailWord_673945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673945).length < 2 ^ (prefixWord ++ tailWord_673945).sum := by decide
  have hdescent : baseEnd_673945 < baseStart_673945 := by decide
  rcases family_descends (prefixWord ++ tailWord_673945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
